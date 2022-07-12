;;;                        UNIFIER
;;;
;;;   *The unification algorithm for the PS rule-based system*
;;;
;;;This algorithm is responsible for the unification process required
;;;for the PS production system. This algorithm for unification is activated
;;;by calling the Unify command with two patterns. Both patterns can have
;;;arbitrary structure with or without variables. Variables are represented
;;;by predicate-calculus variables. The system recognizes and creates the
;;;variable automaticaly when a word preceading by a question mark is read.
;;;
;;;The unification algorithm returns the substitutions that unifies the
;;;patterns or nil when the two patterns cannot be unified.
;;;
;;;Eg. (Unify '(p ?x ?x) '(p (f ?y) (f a))) -> ((?y a))
;;;
;;;Functions are intered into the knowledge-base (kb) package and exported for
;;;external use if required.
;;;
(declaim (optimize speed (safety 0)))
(in-package "PS")

;;;                       *Data structures*
;;;
;;;A PCVAR is a predicate-calculus variable, and is represented as a
;;;structure.
;;;
;;;(Pcvar-p x) returns true if x is a pcvar othervise it returns nil.
;;;
;;;(Pcvar-id x) returns the atom associated with the pcvar.
;;;
;;;                       *Reader syntax*
;;;
;;;?expression is read by the LISP reader as (make-pcvar :id expression)
;;;and prints as ?expression. That is when the LISP reader reads an atom
;;;starting with a question mark it automaticaly creates a variable and
;;;stores it in a structure represented by its :id.
;;;
;; (eval-when (:compile-toplevel :load-toplevel :execute)
;;   (defun Print-Pcvar (var stream depth)
;; 	  (declare (ignore depth))
;; 	  (format stream "?~s" (pcvar-id var)))

;;   (defstruct (pcvar (:print-function print-pcvar)) id)

;;   (set-macro-character #\?
;; 	                     #'(lambda (stream char)
;; 		                       (make-pcvar :id (read stream char))) t))

;;;
;;;(Unify-1 pattern1 pattern2 substitution) returns a list of zero or one
;;;extensions to the sabstitutions that unifies the two patterns.
;;;

(defun Unify-1 (pat1 pat2 sub)
	(cond ((pcvar-p pat1)
	       (var-unify pat1 pat2 sub))
	      ((pcvar-p pat2)
	       (var-unify pat2 pat1 sub))
	      ((atom pat1)
	       (cond ((eql pat1 pat2) (list sub))
		           (t nil)))
	      ((atom pat2) nil)
	      (t (for (sub :in
			               (unify-1 (car pat1) (car pat2) sub))
		            :splice
		            (unify-1 (cdr pat1) (cdr pat2) sub)))))

;;;                          *Main procedure*
;;;
;;;(UNIFY pattern1 pattern2) returns a list of zero or one substitutions
;;;that unifies the two patterns. If the two patterns are unified the function
;;;returns the substitution list, othervise it returns nill.
;;;
;;;Unify calls the function Unify-1 with the two patterns to be unified
;;;and an empty substitution list that is to store the substitution if the
;;;two patterns are unified or nill when the two pattern cannot be unified.
;;;

(defun Unify (pat1 pat2)
	(unify-1 pat1 pat2 nil))


;;;
;;;(Var-Unify variable pattern substitution) returns a list of zero or one
;;;extension to the substitution that unifies the variable with the pattern.
;;;

(defun Var-Unify (pcvar pat sub)
	(cond ((or (eql pcvar pat)
		         (and (pcvar-p pat)
			            (eql (pcvar-id pcvar)
			                 (pcvar-id pat))))
	       (list sub))
	      (t (let ((binding (pcvar-binding pcvar sub)))
		         (cond (binding
			              (unify-1 (binding-value binding) pat sub))
			             ((and *occurs-check-p*
				                 (occurs-in-p pcvar pat sub))
			              nil)
			             (t (list
				               (extend-binding pcvar pat sub))))))))

(defvar *Occurs-Check-P* t)


;;;
;;;(Occurs-In-P variable pattern substitution) returns true if the variable
;;;occurs in the pattern otherwise it returns nill.
;;;

(defun Occurs-In-P (pcvar pat sub)
	(cond ((pcvar-p pat)
	       (or (eq (pcvar-id pcvar) (pcvar-id pat))
		         (let ((binding (pcvar-binding pat sub)))
			         (and binding
			              (occurs-in-p pcvar
				                         (binding-value binding) sub)))))
	      ((atom pat) nil)
	      (t (or (occurs-in-p pcvar (car pat) sub)
		           (occurs-in-p pcvar (cdr pat) sub)))))


;;;
;;;(Pcvar-Binding variable substitution) returns the current binding of the
;;;variable, in the form (variable value), or else it returns nill.
;;;

(defun Pcvar-Binding (pcvar alist)
	(assoc (pcvar-id pcvar) alist))


;;;
;;;(Extend-Binding variable pattern substitution) adds the form (variable
;;;value) to the substitution and returns the new list.
;;;

(defun Extend-Binding (pcvar pat alist)
	(cons (list (pcvar-id pcvar) pat) alist))


;;;
;;;(Binding-Value binding) returns the actual binding of the variable
;;;

(defun Binding-Value (binding) (cadr binding))

;;;*END-OF-FILE*;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
