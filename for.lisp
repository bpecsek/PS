;;;                     *The FOR macro*
;;;
;;;This macro serves as simplification macro for some of the complicated
;;;LISP mapping function for iterative processing.
;;;
;;;Eq. (for (x :in l) :do (foo x))
;;; -> (mapc #'foo l)
;;;
;;;    (for (x :in l) :filter (foo x))
;;; -> (mapcan #'(lambda (x)
;;;		      (let ((x (foo x)))
;;;			   (if x (list x) nil))) l)
;;;
;;;General syntax:
;;;
;;;  (FOR { (variable :IN list) }*
;;;       :WHEN test
;;;       { :DO | :SAVE | :FILTER | :SPLICE } expression)
;;;
(declaim (optimize speed (safety 0)))
(in-package "PS")

;; (export '(For-Vars For-Args For Var-Form-P Var-Form-Var Var-Form-Arg For-Test
;; 	  For-Type For-Body For-Item Make-Mapfn Use-Remove-If-Not-P
;; 	  Make-Body Add-Test Make-Lambda))

(defun For-Vars (l)
        (mapcan #'(lambda (x)
                        (if (var-form-p x)
                            (list (var-form-var x)) nil)) l))


(defmacro For (&rest l)
	(let ((vars (for-vars l))
	      (args (for-args l))
	      (test (for-test l))
	      (type (for-type l))
	      (body (for-body l)))
	  `(,(make-mapfn vars test type body)
	    #',(make-lambda vars
			                (add-test test
				                        (make-body vars test type body))) ,@args)))

(defun For-Args (l)
	(mapcan #'(lambda (x)
		          (if (var-form-p x)
		              (list (var-form-arg x)) nil)) l))

(defun Var-Form-P (x)
	(and (consp x) (= (length x) 3) (eq (cadr x) :in)))

(defun Var-Form-Var (x) (car x))

(defun Var-Form-Arg (x) (caddr x))

(defun For-Test (l)
	(cadr (for-item '(:when) l)))

(defun For-Type (l)
	(let ((item (for-item '(:do :save :splice :filter) l)))
	  (cond (item (car item))
		      (t (error t "No body in FOR-loop!")))))

(defun For-Body (l)
	(let ((item (for-item '(:do :save :splice :filter) l)))
	     (cond (item (cadr item))
		   (t (error t "No body in FOR-loop!")))))

(defun For-Item (keywords l)
	(some #'(lambda (key) (member key l)) keywords))

(defun Make-Mapfn (vars test type body)
	(cond ((eq type :do) 'mapc)
	      ((not (eq type :save)) 'mapcan)
	      ((null test) 'mapcar)
	      ((use-remove-if-not-p vars body) 'remove-if-not)
	      (t 'mapcan)))

(defun Use-Remove-If-Not-P (vars body)
	(and (= (length vars) 1) (equal (car vars) body)))

(defun Make-Body (vars test type body)
	(cond ((eq type :filter)
	       `(let ((x ,body)) (if x (list x) nil)))
	      ((or (not (eq type :save)) (null test)) body)
	      ((use-remove-if-not-p vars body) nil)
	      (t `(list ,body))))

(defun Add-Test (test body)
	(cond ((null test) body)
	      ((null body) test)
	      (t `(if ,test ,body nil))))

(defun Make-Lambda (vars body)
	`(lambda ,vars ,body))
