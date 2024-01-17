(in-package :maxima)

;; Given a Maxima expression e and a variable x, return the sign of e in
;; a neighborhood of infinity. The sign is encoded as -1 for negative, 0
;; for zero, and 1 for positive. We'll say this encoding is the mrv-sign 
;; of an expression.

;; The limit code makes an assumption that x > *large-positive-number* before
;; this code is called. This assumption is made in a new super context, so 
;; it's OK for this code to make new assumptions, as the limit code eventually 
;; kills the super context, deleting the new assumptions.

;; The function mrv-sign-helper extends the mrv-sign of an expression. It returns 
;; 2 for an expression that is not bounded above in a neighborhood of infinity 
;; and -2 for one that is  not bounded below. For bounded expressions, it returns 
;; the sign encoded as -1 for negative, 0 for zero, and 1 for positive. This is 
;; the extended mrv-sign.

;; For debugging, the global *mrv-sign* is a list of expressions that this code
;; was not able to do. After running the testsuite, it's informatitive to examine
;; the list *mrv-sign*

(defvar *mrv-sign* nil)

;; Do {neg, zero, pos} --> {-1,0,1}. For all other inputs, return nil
(defun mrv-sign-to-number (sgn)
	(cond ((eq sgn '$neg) -1)
		  ((eq sgn '$zero) 0)
		  ((eq sgn '$pos) 1)
		  (t nil))) ; pn, pz, nz, pnz, complex, or imaginary.

;; Return the mrv-sign of an expression that is free of the variable x.
;; Unfortunately, the limit problem limit(ind*inf) makes its way to the gruntz 
;; code as gruntz(ind*x,x,inf). And that calls mrv-sign-constant on ind. So
;; we trap for this case (and other extended reals) and return nil for its
;; mrv sign.
(defun mrv-sign-constant (e)
	(let ((sgn))
	  (cond 
	    ((member e extended-reals) (throw 'taylor-catch nil)) ;should not happen
	    (t 		
		  ;; The orginial mrv-sign code called radcan on e before calling 
		  ;; sign, but I'm not sure the radcan is needed. Let's just call 
		  ;; csign on e and skip the radcan.
		  (setq sgn ($csign e))
		  ;; When sgn is pnz and *getsignl-asksign-ok* is true, do an asksign. 
		  (when (and *getsignl-asksign-ok* (eq sgn '$pnz))
			 (setq sgn ($asksign e))
			  ;; The gruntz code uses a super context, so we can make assumptions
			  ;; that will be removed when the super context is killed.
			  (cond ((eq sgn '$neg) (assume (ftake 'mlessp e 0)))
			        ((eq sgn '$zero) (assume (ftake '$equal e 0)))
			        ((eq sgn '$pos) (assume (ftake 'mlessp 0 e))))) 
		  ;; When sgn is still pnz, throw an error--the grunt code cannot proceed
		  ;; without knowing the sign.
		  (when (eq sgn '$pnz)
	        (throw 'taylor-catch nil))
          ;; convert sgn to a numerical code.
		  (mrv-sign-to-number sgn)))))

;; This code runs the testsuite OK, but it fails to find the mrv sign of 
;; sums whose terms involve both minus infinity and infinite terms, for example
;; log(x+1) - log(x). The original mrv-sign code dispatched limitinf on a 
;; sum and then returned the mrv sign of that result. Maybe that's OK, but
;; I worry about an infinite loop?

;; The notorious Bug #3054 
;;
;; limit(exp(exp(2*log(x**5 + x)*log(log(x)))) / exp(exp(10*log(x)*log(log(x)))), x, inf)
;;
;; sends some expressions to mrv-sign-sum that this code does not handle.

(defun mrv-sign-sum (e x)
	(let ((ee (mapcar #'(lambda (q) (mrv-sign-helper q x)) (cdr e))))
	(mtell "ee = ~M ~%" (cons '(mlist) ee))
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
		((and (every #'(lambda (q) (>= q -1)) ee) (member 2 ee :test #'eql))
		 2)
	    (t (mrv-indeterminate-sum e x)))))

;; OK, once this function is polished, I should blend it with mrv-sign-sum. Currently,
;; calling both is inefficient.
(defun mrv-indeterminate-sum (e x)	
    (let ((minf-term 0) (inf-term 0) (finite-term 0) (failed-term 0) (q) (qq) (ans))
	(setq e (cdr e))
	(dolist (q e)
		(setq ans (mrv-sign-helper q x))
		(cond ((eql -2 ans) (setq minf-term (add minf-term q)))
		      ((eql 2 ans) (setq inf-term (add inf-term q)))
			  ((eq nil ans) (setq failed-term (add failed-term q)))
			  (t (setq finite-term (add finite-term q)))))

	(mtell "a = ~M ; b = ~M ; c = ~M ~%" minf-term inf-term failed-term)

	(cond ((and (eql 0 failed-term) (not (eql 0 minf-term)) (not (eql inf-term 0)))
	       (setq q ($limit (div inf-term (mul -1 minf-term)) x '$inf))
		   (mtell "q = ~M ~%" q)
		   (cond ((eq t (mgrp q 1)) 2)
		         ((eq t (mgrp 1 q)) -2)
				 ((eql q 1)
				      ;; OK this needs some attention!
                      (setq qq ($radcan (sub (div inf-term (mul -1 minf-term)) 1)))
		              (setq qq (let (($taylordepth 16)) ($taylor qq x '$inf 16)))
					  (setq qq (sratsimp ($first ($expand qq))))
					  (mtell "qq = ~M ~%" qq)
		              (setq qq (mrv-sign qq x))
					  (mtell "qq = ~M ~%" qq)
					  qq)
				 (t nil)))
		  
		  (t 
		   	;; Hope that csign can do it!
	        (mrv-sign-to-number ($csign e))))))

(defun mrv-sign-product (e x)
  (let ((ee (mapcar #'(lambda (q) (mrv-sign-helper q x)) (cdr e))))
  (cond
     ;; unable to find the sign of one term, dispatch csign on e.
	 ((some #'null ee) (mrv-sign-to-number ($csign e)))
     (t (max -2 (min 2 (reduce '* ee)))))))

(defun mrv-sign-log (e x) ; e = log(X)
	(let ((sgn (mrv-sign-helper (cadr e) x)))
      (cond 
	    ((eql sgn 2) 2) ; log(inf) = inf	 
		;; for all other cases, dispatch csign
		(t (mrv-sign-to-number ($csign e))))))

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

;; For debugging, build a list *missing-mrv* of all operator that mrv-sign-helper
;; encounters but doesn't know how to handle.
(defvar *missing-mrv* nil)
;; Let ans = limit(e,x,inf). Then do 
;;      {minf, negative, zero, pos,  inf} --> {-2, -1, 0, 1, 2}.
(defun mrv-sign-helper (e x)
	(cond ((freeof x e) (mrv-sign-constant e))
	      ((eq e x) 2)
		  ;((alike e (mul -1 x)) -2)
	      ((mtimesp e) (mrv-sign-product e x))
		  ((mplusp e) (mrv-sign-sum e x))
		  ((mexptp e) (mvr-sign-mexpt e x))
		  ((mlogp e) (mrv-sign-log e x))
		  (t 
		    (when (consp e)
				(push (caar e) *missing-mrv*))
		    (mrv-sign-to-number ($csign e)))))

;; Only for testing!
(defun $larry (e x)
	(mrv-sign e x))

(defun mrv-sign (e x)
	(let ((sgn (mrv-sign-helper e x)))
      ;; These special cases shouldn't be needed!
	 ; (when (alike1 e (mul -1 (ftake '%log x)))
	  ;	(setq sgn -2))
	  ;(when (alike1 e (sub 1 (ftake '%log x)))
	 ; 	(setq sgn -2))
    ; (when (alike1 e (mul (sub 1 (ftake '%log x)) (ftake '%log x)))
	 ; 	(setq sgn -2))
	  ;; For now, do an fake asksign on expressions the code cannot handle.
	  (when (and (null sgn) (eq '$pnz ($csign e)))
	    (push (ftake 'mlist e x sgn ($csign e)) *mrv-sign*)
	    (mtell "Enter sign (either -1,0,or 1) of ~M ~%" e)
	    (setq sgn ($read )))
     ;; Convert {nil, -2,-1,0,1,2} --> {nil,-1,-1,0,1,1}.
	 (if (null sgn) (throw 'taylor-catch nil) (max -1 (min 1 sgn)))))