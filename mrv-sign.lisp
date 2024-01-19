(in-package :maxima)

;; Given a Maxima expression e and a variable x, return the sign of e in
;; a neighborhood of infinity. The sign is encoded as -1 for negative, 0
;; for zero, and 1 for positive. We'll say this encoding is the "mrv sign" 
;; of an expression.

;; The gruntz code makes an assumption that x > *large-positive-number* before
;; this code is called. This assumption is made in a new super context, so 
;; it's OK for this code to make new assumptions, as the gruntz code eventually 
;; kills the super context, deleting the new assumptions.

;; The function mrv-sign-helper extends the mrv sign of an expression to 
;; include the values of 2 for an expression that is not bounded above in a 
;; neighborhood of infinity and -2 for one that is  not bounded below. For 
;; example, the extended mrv sign of x --> log(x) is 2 and the extended
;;; mrv sign of x --> -x is -2. 

;; For debugging, the global *mrv-sign-failures* is a list of expressions that 
;; mrv-sign was not able to do. 

;; rtest_gruntz failures:
;(7 8 16 17 20 21 24 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 81 82 83 84 85 86 87 89 90 91 95 101 102)
(defvar *mrv-sign-failures* nil)

;; Do {neg, zero, pos} --> {-1,0,1}. For all other inputs, throw an error
;; to taylor-catch. Running the testsuite, neg is the most poplular input
;; to this function.
(defun mrv-sign-to-number (sgn)
	(cond ((eq sgn '$neg) -1)
		  ((eq sgn '$pos) 1)
		  ((eq sgn '$zero) 0)
		  (t (throw 'taylor-catch nil)))) ; pn, pz, nz, pnz, complex, or imaginary.

;; Return the mrv-sign of an expression that is free of the variable x.
;; Unfortunately, the limit problem limit(ind*inf) makes its way to the gruntz 
;; code as gruntz(ind*x,x,inf). And that calls mrv-sign-constant on ind. So
;; we trap for this case (and other extended reals) and throw an error to 
;; taylor-catch.

(defvar *jj* nil)
(defun mrv-sign-constant (e)
	(let ((sgn))
	  (cond 
	    ((member e extended-reals) (throw 'taylor-catch nil)) 
	    (t 		
		  ;; The orginial mrv-sign code called radcan on e before calling 
		  ;; sign, but I'm not sure the radcan is needed. Let's just call 
		  ;; csign on e and skip the radcan.
		  (setq sgn ($csign e))
		  ;; When sgn is pnz and *getsignl-asksign-ok* is true, do an asksign. 
		  (when (and *getsignl-asksign-ok* (eq sgn '$pnz))
			 (setq sgn ($asksign e))
			  ;; The gruntz code uses a super context, so we can make assumptions
			  ;; that will be removed when the super context is killed. Possibly
			  ;; these assumptions keep Maxima from asking redundant questions, but
			  ;; I don't have an example that shows doing these assumptions makes
			  ;; a difference.
			  (cond ((eq sgn '$neg) (assume (ftake 'mlessp e 0)))
			        ((eq sgn '$zero) (assume (ftake '$equal e 0)))
			        ((eq sgn '$pos) (assume (ftake 'mlessp 0 e))))) 
		  ;; Map {neg, zero, pos} --> {-1,0,1}. For all other values,
		  ;; throw an error to taylor-catch.
		  (mrv-sign-to-number sgn)))))
			

;; The notorious Bug #3054 
;;
;; limit(exp(exp(2*log(x**5 + x)*log(log(x)))) / exp(exp(10*log(x)*log(log(x)))), x, inf)
;;
;; sends some expressions to mrv-sign-sum that this code does not handle.

(defun mrv-sign-sum (e x)
	(let ((ee (mapcar #'(lambda (q) (mrv-sign-helper q x)) (cdr e))))
	(cond 
	    ;; unable to find the sign of one term, dispatch csign on e.
		((some #'null ee)
		  (mrv-sign-to-number ($csign e)))
        ;; at least one term is -2 and all other terms are finite; return -2
		((and (every #'(lambda (q) (<= q 1)) ee) (member -2 ee :test #'eql))
		 -2)
         ;; at least one term is 2 and all other terms are finite; return 2
		((and (every #'(lambda (q) (<= -1 q)) ee) (member 2 ee :test #'eql))
		 2) 
	    ;; every term of e is nonnegative, return 1 for postive & 2 for inf
	    ((every #'(lambda (q) (>= q 0)) ee) (apply #'max ee))
		;; every term is nonpositive, return -1 for negative & -2 for minf
		((every #'(lambda (q) (>= 0 q)) ee) (apply #'min ee))
		(t (mrv-indeterminate-sum e x)))))

;; OK, once this function is polished, I should blend it with mrv-sign-sum. 
;; Calling both mrv-sign-sum and mrv-indeterminate-sum is inefficient.
(defun mrv-indeterminate-sum (e x)	
    (let ((minf-term 0) (inf-term 0) (finite-term 0) (failed-term 0) (q) (qq) (ans))
	(setq e (cdr e))
	(dolist (q e)
		(setq ans (mrv-sign-helper q x))
		(cond ((eql -2 ans) (setq minf-term (add minf-term q)))
		      ((eql 2 ans) (setq inf-term (add inf-term q)))
			  ((eq nil ans) (setq failed-term (add failed-term q)))
			  (t (setq finite-term (add finite-term q)))))

	(cond ((and (eql 0 failed-term) (not (eql 0 minf-term)) (not (eql inf-term 0)))
	       (setq q ($gruntz (div inf-term (mul -1 minf-term)) x '$inf))
		   (cond ((eq t (mgrp q 1)) 2)
		         ((eq t (mgrp 1 q)) -2)
				 ((eql q 1)
				      ;; The call to sratsimp is needed for one rtest_gruntz test.
					  (setq qq (sratsimp (sub (div inf-term (mul -1 minf-term)) 1)))
					  ;; The function tlimit-taylor iterates on the taylor order
					  ;; until the result is nonzero. The last argument (here 3) 
					  ;; stops the after quadrupling the order three times. When
					  ;; tlimit-taylor fails to find the leading term, throw an 
					  ;; error to taylor-catch
					  (setq qq (tlimit-taylor qq x '$inf 1 3)) ;16 1
					  (when (null qq)
					    (throw 'taylor-catch nil))
					  ;; I'm not sure this always returns the leading order?
					  (setq qq (sratsimp ($first ($expand qq))))
		              (setq qq (mrv-sign qq x))
					  qq)
				 (t (throw 'taylor-catch nil)))) ;shouldn't happen?
		  
		  (t 
		   	;; Hope that csign can do it!
	        (mrv-sign-to-number ($csign e))))))

(defun mrv-sign-product (e x)
  (let ((ee (mapcar #'(lambda (q) (mrv-sign-helper q x)) (cdr e))))
  (cond
     ;; unable to find the sign of one term, dispatch csign on e.
	 ((some #'null ee) (mrv-sign-to-number ($csign e)))
     (t (max -2 (min 2 (reduce '* ee)))))))

;; To allow the (slow) test
;;   gruntz(%e^(8*%e^((54*x^(49/45))/17+(21*x^(6/11))/8+5/(2*x^(5/7))+2/x^8))/log(log(-log(4/(3*x^(5/14)))))^(7/6),x,inf);
;; to complete, we need to examine the mrv sign of both X and 1/X, where 
;; the input to mrv-sign-log is log(X).
(defun mrv-sign-log (e x) ; e = log(X)
	(let ((sgn (mrv-sign-helper (cadr e) x)))
      (cond 
	    ((eql sgn 2) 2) ; log(inf) = inf	 
		((null sgn) (throw 'taylor-catch nil))
		(t 
		  ;; When the extended mrv sign of 1/X is 2, that means X = zeroa.
		  ;; so mrvsign(log(X))= mrvsign(minf) = -2
		  (setq sgn (mrv-sign-helper (div 1 (cadr e)) x))
		  (if (eql sgn 2) -2) (mrv-sign-to-number ($csign e))))))
		

(defun mvr-sign-mexpt (e x) ; e = X^Y
  (let ((a (mrv-sign-helper (cadr e) x))
        (b (mrv-sign-helper (caddr e) x)))
	(cond 
	  ;; pos^minf = pos
	  ((and (eql a 1) (eql b -2)) 1)
	  ;; pos^inf = inf
	  ((and (eql a 1) (eql b 2)) 2)
	  ;; inf^pos = inf & inf^inf = inf
	  ((and (eql a 2) (or (eql b 1) (eql b 2))) 2)
      ;; inf^{neg, zero} = pos
	  ((and (eql a 2) (or (eql b -1) (eql b 0))) 1)
	  ;; pos^{neg, zero, pos} = pos
	  ((and (eql a 1) (or (eql b -1) (eql b 0) (eql b 1))) 1)
	  ;; for all other cases, dispatch csign
	  (t (mrv-sign-to-number ($csign e))))))

(defun atanp (e)
	(and (consp e) (eq '%atan (caar e))))

(defun mvr-sign-atan (e x)
  (mrv-sign-helper (cadr e) x))

(defun sinhp (e)
  (and (consp e) (or (eq '%sinh (caar e))  (eq '$sinh (caar e)))))

(defun mvr-sign-sinh (e x)
  (mrv-sign-helper (cadr e) x))

(defun sinp (e)
	(and (consp e) (eq '%sin (caar e))))

(defun mrv-sign-sin (e x)
	(let ((sgn (mrv-sign-helper (div 1 (cadr e)) x)))
		(cond ((eql sgn 2) 1)
		      ((eql sgn -2) -1)
			  (t nil))))

(defun coshp (e)
	(and (consp e) (eq '%cosh (caar e))))

;; Wrong when e = cosh(X) and X isn't real?
(defun mrv-sign-cosh (e x)
  (let ((sgn (mrv-sign-helper (cadr e) x))) ;e = cosh(X)
  (cond ((eql sgn -2) 2) ;cosh(-minf) = inf
        ((eql sgn 2) 2) ;cosh(inf) = inf
		(t 1)))) ; range(cosh) = [1,inf]


;; Return the extended mrv sign of an expression. To do this, the code
;; examines the operator of the expression and dispatches the appropriate function.

;; For debugging, build a list *missing-mrv-operator* of all operators that 
;; mrv-sign-helper encounters but doesn't know how to handle. Currently 
;; running the testsuite + the share testsuite does not reveal any missing 
;; operators. If the list of operators grows, maybe I should put the 
;; various sign functions in a hashtable and dispatch by lookup. It seems
;; that mrv-sign-helper encounters a nounform sinh expression?
(defvar *missing-mrv-operator* nil)

(defun mrv-sign-helper (e x)
	(cond ((freeof x e) (mrv-sign-constant e))
	      ((eq e x) 2)
	      ((mtimesp e) (mrv-sign-product e x))
		  ((mplusp e) (mrv-sign-sum e x))
		  ((mexptp e) (mvr-sign-mexpt e x))
		  ((mlogp e) (mrv-sign-log e x))
		  ((atanp e) (mvr-sign-atan e x))
		  ((coshp e) (mrv-sign-cosh e x))
		  ((sinhp e) (mvr-sign-sinh e x))
		  ((sinp e) (mrv-sign-sin e x))
		  (t 
		    (when (consp e)
				(push (caar e) *missing-mrv-operator*))
		    (mrv-sign-to-number ($csign e)))))

(defun mrv-sign (e x)
	(let ((sgn (mrv-sign-helper e x)))
	  ;; For now, do a fake asksign on expressions the code cannot handle.
	  (when (and (null sgn) (eq '$pnz ($csign e)))
	    (push (ftake 'mlist e x sgn ($csign e)) *mrv-sign-failures*)
	    (mtell "Enter sign (either -1,0,or 1) of ~M ~%" e)
	    (setq sgn ($read )))
     ;; When sgn is null, throw to taylor-catch; otherwise	 
	 ;; map {-2,-1,0,1,2} --> {-1,-1,0,1,1}.
	 (if (null sgn) (throw 'taylor-catch nil) (max -1 (min 1 sgn)))))

;; The function gruntz1 standardizes the limit point to inf and the limit variable
;; to a gensym. Since the limit point is possibly altered by this function, we
;; need to make the appropriate assumptions on the limit variable. This is done
;; in a supcontext.
(defun gruntz1 (exp var val &rest rest)
  (cond ((> (length rest) 1)
	 (merror (intl:gettext "gruntz: too many arguments; expected just 3 or 4"))))
  (let (($logexpand t) ; gruntz needs $logexpand T
        (newvar (gensym "w"))
	(dir (car rest)))
	(putprop newvar t 'internal); keep var from appearing in questions to user	
    (cond ((eq val '$inf)
	   (setq exp (maxima-substitute newvar var exp)))
	  ((eq val '$minf)
	   (setq exp (maxima-substitute (m* -1 newvar) var exp)))
	  ((eq val '$zeroa)
	   (setq exp (maxima-substitute (m// 1 newvar) var exp)))
	  ((eq val '$zerob)
	   (setq exp (maxima-substitute (m// -1 newvar) var exp)))
	  ((eq dir '$plus)
	   (setq exp (maxima-substitute (m+ val (m// 1 newvar)) var exp)))
	  ((eq dir '$minus)
	   (setq exp (maxima-substitute (m+ val (m// -1 newvar)) var exp)))
	  (t (merror (intl:gettext "gruntz: direction must be 'plus' or 'minus'; found: ~M") dir)))
	  (let ((cx ($supcontext)))
	   	    (unwind-protect
 	         (progn
				  (mfuncall '$assume (ftake 'mlessp *large-positive-number* newvar)) ; *large-positive-number* < newvar
                  (mfuncall '$assume (ftake 'mlessp 0 'lim-epsilon)) ; 0 < lim-epsilon
				  (mfuncall '$assume (ftake 'mlessp *large-positive-number* 'prin-inf)) ; *large-positive-number* < prin-inf
				  (mfuncall '$activate cx) ;not sure this is needed, but OK	
				  (setq exp (resimplify exp)) ;simplify in new context
                  (setq exp (let ((var newvar)) 
				    (declare (special var)) 
				    (resimp-extra-simp (sratsimp exp)))) ;additional simplifications
				  (limitinf exp newvar)) ;compute & return limit
			($killcontext cx))))) ;kill context & forget all new facts.	 