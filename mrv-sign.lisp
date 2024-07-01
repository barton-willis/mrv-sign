(in-package :maxima)
;; Given a Maxima expression e and a variable x, mrv-sign(e,x) returns the sign 
;; of e in a neighborhood of inf (real infinity). The sign is encoded as -1 for 
;; negative, 0 for zero, and 1 for positive. 

;; Notice that for a sufficiently large number of compositions, log(log(...(log(x)))) 
;; is positive in a neighborhood of infinity, but no matter how large we assume x 
;; to be, sign(log(log(... (log(x))))) = pnz. So no, the function mrv-sign cannot 
;; simply call sign.

;; The Gruntz code makes an assumption that x > *large-positive-number* before
;; this code is called. This assumption is made in a new super context, so 
;; it's OK for this code to make new assumptions, as the Gruntz code eventually 
;; kills the super context, deleting the new assumptions.

;; The function mrv-sign-helper extends the mrv sign of an expression to 
;; include the values of 2 for an expression that is not bounded above in a 
;; neighborhood of infinity and -2 for one that is not bounded below. For 
;; example, the extended mrv sign of x --> log(x) is 2, and the extended
;;; mrv sign of x --> -x is -2. 

;; Map {$neg, $zero, $pos} --> {-1, 0, 1}. For all other inputs, throw an error
;; to taylor-catch. 
(defun mrv-sign-to-number (sgn)
  (cond ((eq sgn '$neg) -1)
        ((eq sgn '$zero) 0)
        ((eq sgn '$pos) 1)
        (t (throw 'taylor-catch nil)))) ; nil for pn, pz, nz, pnz, complex, or imaginary.

;; The function mrv-sign-constant returns the mrv-sign of an expression that is 
;; free of the variable x. Unfortunately, the limit problem limit(ind*inf) makes 
;; its way to the Gruntz code as gruntz(ind*x, x, inf). And utlimately that calls 
;; mrv-sign-constant on ind. So, we trap for this case (and other extended reals) 
;; and throw an error to taylor-catch for an input that is an extended real 
;; (minf, zerob, zeroa, ind, und, inf, or infinity). Possibly, for the inputs
;; minf, zerob, zeroa, and inf, mrv-sign-constant shouldn't throw to taylor-catch.

;; When this code does an asksign, it would be OK to append this fact to the 
;; fact database (the Gruntz code works in a new super context). Better, I think, 
;; would be an option on asksign to append the fact.

(defun mrv-sign (e x)
	(let ((sgn (mrv-sign-helper e x)))
	 (if (null sgn) (throw 'taylor-catch nil) (max -1 (min 1 sgn)))))

(defun mrv-sign-constant (e)
   (if (member e extended-reals)
      (throw 'taylor-catch nil)
      (mrv-sign-to-number (if *getsignl-asksign-ok*
                              ($asksign e)
                              ($sign e)))))

;; Return the mrv-sign of e, where e is a sum.
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
		(t (mrv-sign-indeterminate-sum e x)))))

(defun mrv-sign-indeterminate-sum (e x)	
     (let ((minf-term nil) (other-term nil) (q) (qq) (ans))
  	   (setq e (cdr e)) 
	   (dolist (q e)
	      (setq ans (mrv-sign-helper q x))
		    (if (eql -2 ans) 
		        (push q minf-term) 
			    (push q other-term)))

	   (setq minf-term (fapply 'mplus minf-term))
	   (setq other-term (fapply 'mplus other-term))

 	   (cond ((not (eql 0 minf-term))
	       (setq q ($limit (sratsimp (div other-term (mul -1 minf-term))) x '$inf))
		   (cond ((eq t (mgrp q 1)) 2)
		         ((eql 0 q) -2)
		         ((eq t (mgrp 1 q)) -2)
				 ((eql q 1)
				      ;; The call to sratsimp is needed for one rtest_gruntz test.
					  (setq qq (sratsimp (sub (div other-term (mul -1 minf-term)) 1)))
					  (setq qq (tlimit-taylor qq x '$inf 0 3))
					  (if (null qq)
					        (throw 'taylor-catch nil))
		                    (mrv-sign ($ratdisrep qq) x))
				 (t (throw 'taylor-catch nil))))
		  (t 
		    ;; Hope that csign can do it!
	        (mrv-sign-to-number ($csign (fapply 'mplus e)))))))

;; Return the mrv-sign of the expression e, where e is a product.
(defun mrv-sign-product (e x)
  (let ((ee (mapcar #'(lambda (q) (mrv-sign-helper q x)) (cdr e))))
  (cond
     ;; unable to find the sign of one term, dispatch csign on e.
	 ((some #'null ee) (mrv-sign-to-number ($csign e)))
     (t (max -2 (min 2 (reduce '* ee)))))))

;; Return the mrv-sign of the expression e, where the operator of e is log. To 
;; allow the (slow to finish) test
;;   gruntz(%e^(8*%e^((54*x^(49/45))/17+(21*x^(6/11))/8+5/(2*x^(5/7))+2/x^8))/log(log(-log(4/(3*x^(5/14)))))^(7/6),x,inf);
;; to complete, we need to examine the mrv sign of both X and 1/X, where 
;; the input to mrv-sign-log is log(X).
(defun mrv-sign-log (e x)
	(cond ((eql 2 (mrv-sign-helper (cadr e) x)) 2) ;log(inf) = inf
	      ((eql 2 (mrv-sign-helper (div 1 (cadr e)) x)) -2); log(zeroa) = minf
		  (t (throw 'taylor-catch nil))))

;; Return the mrv sign of the expression e, where e = X^Y. For the mrv sign
;; of an expression to be zero, it needs to be zero in a neighborhood of zero.
;; so if limit(X,x,inf) = 1/2 & limit(Y,x,inf) = inf, although limit(X^Y,x,inf)=0,
;; the mrv sign of X^Y is not zero.
(defun mrv-sign-mexpt (e x) ; e = X^Y
  (let ((a (mrv-sign-helper (cadr e) x))
        (b (mrv-sign-helper (caddr e) x)))
	(cond 
	  ;; pos^minf = pos
	  ((and (eql a 1) (eql b -2)) 1)
	  ;; pos^inf = inf
	  ((and (eql a 1) (eql b 2)) 2)
	  ;; pos^{neg, pos} = pos
	  ((and (eql a 1) (or (eql b -1) (eql b 1))) 1)
	  ;; inf^pos = inf & inf^inf = inf
	  ((and (eql a 2) (or (eql b 1) (eql b 2))) 2)
      ;; inf^{neg, zero} = pos
	  ((and (eql a 2) (or (eql b -1) (eql b 0))) 1)
	  ;; inf^minf = 1
	  ((and (eql a 2) (eql b -2)) 1)
      ;; zero^{pos,inf} = 0. But this case isn't tested by the testsuite!
	  ((and (eql a 0) (or (eql b 1) (eql b 2))) 0)
	  ;; For all other cases, let's dispatch csign or asksign
	  (t 
	    (mrv-sign-to-number 
	      (if *getsignl-asksign-ok* ($asksign e) ($csign e)))))))

(defun atanp (e)
	(and (consp e) (eq '%atan (caar e))))

;; Return the mrv-sign of the expression e, where e = atan(X).
(defun mrv-sign-atan (e x)
  (mrv-sign-helper (cadr e) x))

(defun sinp (e)
	(and (consp e) (eq '%sin (caar e))))

(defun mrv-sign-sin (e x)
	(let ((sgn (mrv-sign-helper (div 1 (cadr e)) x)))
		(cond ((eql sgn 2) 1) ;sin(zeroa) = 1
		      ((eql sgn -2) -1) ;sin(zerob) = -1
			  (t (throw 'taylor-catch nil)))))

;; Return the extended mrv sign of an expression. To do this, the code
;; examines the operator of the expression and dispatches the appropriate function.
(defun mrv-sign-helper (e x)
	(cond ((freeof x e) (mrv-sign-constant e))
	      ((eq e x) 2)
	      ((mtimesp e) (mrv-sign-product e x))
		  ((mplusp e) (mrv-sign-sum e x))
		  ((mexptp e) (mrv-sign-mexpt e x))
		  ((mlogp e) (mrv-sign-log e x))
		  ((atanp e) (mrv-sign-atan e x))
		  ((sinp e) (mrv-sign-sin e x))
		  ;; As needed, uncomment and define the following functions:
          ;; ((coshp e) (mrv-sign-cosh e x))
          ;; ((sinhp e) (mrv-sign-sinh e x))
		  (t 
		    (throw 'taylor-catch nil))))

