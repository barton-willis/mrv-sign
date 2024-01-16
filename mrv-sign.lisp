(in-package :maxima)

;;; Given a Maxima expression e and a variable x, return the sign of e in
;;; a neighborhood of infinity. The sign is encoded as -1 for negative, 0
;;; for zero, and 1 for positive. 

;;; The function mrv-sign-helper returns 2 for an expression that is not bounded
;;; above in a neighborhood of infinity and -2 for one that is not bounded below.
;;; For bounded expressions it returns the sign encoded as -1 for negative, 0
;;; for zero, and 1 for positive. 
(defvar *mrv-sign* nil)

;; Do {neg, zero, pos} --> {-1,0,1}. For all other inputs, return nil
(defun mrv-sign-to-number (sgn)
	(cond ((eq sgn '$neg) -1)
		  ((eq sgn '$zero) 0)
		  ((eq sgn '$pos) 1)
		  (t nil))) ; pn, pz, nz, pnz, complex, imaginary.

;; I think this isn't neeed. 
(defun mrv-sign-mabs (e x)
	(let ((sgn (mrv-sign-helper (cadr e) x)))
		(cond ((eql sgn -2) 2) ;abs(minf) = inf
		      ((eql sgn 2) 2) ;abs(inf) = inf
			  ((eql sgn 1) 1) ;abs(pos) = pos
			  ((eql sgn -1) 1) ;abs(neg) = inf
			  ((eq t (mnqp 0 (cadr e))) 1) ; abs(nonzero) = pos
			  (t (mrv-sign-to-number ($csign e))))))

(defun mrv-sign-constant (e x)
	(let ((sgn))
	  (cond ((eq e '$minf) -2)
	        ((eq e '$zerob) -1) ;not sure needed--likely OK
	  	    ((eq e '$zeroa) 1)  ;not sure needed--likely OK
		    ((eq e '$inf) 2)
		    ((or (eq e '$infinity) (eq e '$ind)  (eq e '$und)) nil)
		    (t 
		      (setq sgn ($csign ($radcan e))) ;not sure about the radcan
			  ;; Do an asksign when sgn = pnz. Not sure about the 
              ;; *getsignl-asksign-ok* flag.
		  	  (when (and *getsignl-asksign-ok* (eq sgn '$pnz))
				(setq sgn ($asksign e)))
              ;; return -1, 0, or 1.
			  (mrv-sign-to-number sgn)))))

(defun mrv-sign-sum (e x)
	(let ((ee (mapcar #'(lambda (q) (mrv-sign-helper q x)) (cdr e))))
	(cond 
	    ;; unable to find the sign of one term, dispatch csign on e.
		((some #'null ee)
		  (mrv-sign-to-number ($csign e)))
	    ;; every term of e is nonnegative, return 1 for postive & 2 for inf
	    ((every #'(lambda (q) (>= q 0)) ee) (apply #'max ee))
		;; every term is nonpositive, return -1 for negative & -2 for minf
		((every #'(lambda (q) (>= 0 q)) ee) (apply #'min ee))
		((and (every #'(lambda (q) (>= q -1)) ee) (member 2 ee :test #'eql))
		 2)
		;; Hope that csign can do it
	    (t (mrv-sign-to-number ($csign e))))))
 
(defun mrv-sign-product (e x)
  (let ((ee (mapcar #'(lambda (q) (mrv-sign-helper q x)) (cdr e))))
  (cond
     ;; unable to find the sign of one term, dispatch csign on e.
	 ((some #'null ee)
		  (mrv-sign-to-number ($csign e)))
     ;; one or more zero terms and one or more infinite terms, dispatch csign on e 
     ((and (member 0 ee) (or (member -2 ee) (member 2 ee))) ;indeterminate
	      (mrv-sign-to-number ($csign e)))
     (t  (max -2 (min 2 (reduce '* ee)))))))

(defun mrv-sign-log (e x) ; e = log(X)
	(let ((sgn (mrv-sign-helper (cadr e) x)))
      (cond 
		;; log(inf) = inf	 
	    ((eql sgn 2) 2)
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

;; True iff e = abs(X)
(defun mabsp (e)
	(and (consp e) (eq (caar e) 'mabs)))

(defvar *missing-mrv* nil)

;; Let ans = limit(e,x,inf). Then do 
;;      {minf, negative, zero, pos,  inf} --> {-2, -1, 0, 1, 2}.
(defun mrv-sign-helper (e x)
	(cond ((freeof x e) (mrv-sign-constant e x))
	      ((eq e x) 2)
		  ((alike e (mul -1 x)) -2)
	      ((mtimesp e) (mrv-sign-product e x))
		  ((mplusp e) (mrv-sign-sum e x))
		  ((mexptp e) (mvr-sign-mexpt e x))
		  ((mlogp e) (mrv-sign-log e x))
		  ((mabsp e) (mrv-sign-mabs e x))
		  (t 
		    (when (consp e)
				(push (caar e) *missing-mrv*))
		    (mrv-sign-to-number ($csign e)))))

(defun $larry (e x)
	(mrv-sign e x))

;; bugs 
;; larry(-log(x),x) = -1 (should be -2)
;; larry(1-log(x),x) = false (should be -2)
;; larry((1-log(x))*log(x),x) = false (should be -2)
(defun mrv-sign (e x)
	(let ((sgn (mrv-sign-helper e x)))
	  (when (alike1 e (mul -1 (ftake '%log x)))
	  	(setq sgn -2))
	  (when (alike1 e (sub 1 (ftake '%log x)))
	  	(setq sgn -2))
     (when (alike1 e (mul (sub 1 (ftake '%log x)) (ftake '%log x)))
	  	(setq sgn -2))
	  (when (and (null sgn) (eq '$pnz ($csign e)))
	    (push (ftake 'mlist e x sgn ($csign e)) *mrv-sign*)
	    (mtell "Enter sign (either -1,0,or 1) of ~M ~%" e)
	    (setq sgn ($read )))
	 (if (null sgn) sgn (max -1 (min 1 sgn)))))