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
(in-package "PS")

(defun Print-Pcvar (var stream depth)
	(declare (ignore depth))
	(format stream "?~s" (pcvar-id var)))

(defstruct (pcvar (:print-function print-pcvar)) id)

(defun |?-reader| (stream char)
  (declare (ignore char))
  (make-pcvar :id (read stream t nil t)))

;;;
;;;Macro character definition for !.
;;;When the LISP reader reads the character ! it forces the next expression
;;;to be evaluated.
;;;Eg. !test --> (eval test)

(defun |!-reader| (stream char)
  (declare (ignore char))
  (list 'eval (read stream t nil t)))

(defvar *previous-readtables* nil)

(defmacro enable-reader-macros ()
  '(eval-when (:compile-toplevel :load-toplevel :execute)
    (push *readtable* *previous-readtables*)
    (setq *readtable* (copy-readtable))
    (set-macro-character #\? '|?-reader|)
    (set-macro-character #\! '|!-reader|)))

(defmacro disable-reader-macros ()
  '(eval-when (:compile-toplevel :load-toplevel :execute)
    (setq *readtable* (pop *previous-readtables*))))
  
