;;; File: utils.lisp
;;; Description: Miscellaneous utility functions.

;;; $Id: utils.lisp,v 1.23 2004/09/15 17:57:15 youngde Exp $
(declaim (optimize speed (safety 0)))
(in-package "PS")

;;; All code below courtesy of the PORT module, CLOCC project.

;;;
;;; Conditions
;;;

(define-condition code (error)
  ((proc :reader code-proc :initarg :proc)
   (mesg :type simple-string :reader code-mesg :initarg :mesg)
   (args :type list :reader code-args :initarg :args))
  (:documentation "An error in the user code.")
  (:report (lambda (cc out)
             (declare (stream out))
             (format out "[~s]~@[ ~?~]" (code-proc cc)
                     (and (slot-boundp cc 'mesg) (code-mesg cc))
                     (and (slot-boundp cc 'args) (code-args cc))))))

(define-condition case-error (code)
  ((mesg :type simple-string :reader code-mesg :initform
         "`~s' evaluated to `~s', not one of [~@{`~s'~^ ~}]"))
  (:documentation "An error in a case statement.
This carries the function name which makes the error message more useful."))

(define-condition not-implemented (code)
  ((mesg :type simple-string :reader code-mesg :initform
         "not implemented for ~a [~a]")
   (args :type list :reader code-args :initform
         (list (lisp-implementation-type) (lisp-implementation-version))))
  (:documentation "Your implementation does not support this functionality."))

;;;
;;; Extensions
;;;
(defmacro definline (name arglist &body body)
  "Declare an inline defun."
  `(progn (declaim (inline ,name)) (defun ,name ,arglist ,@body)))

(defmacro defcustom (name type init &optional doc)
  "Define a typed global variable."
  `(progn (declaim (type ,type ,name))
    (defvar ,name (the ,type ,init) ,doc)))

(defmacro defconst (name type init &optional doc)
  "Define a typed constant."
  `(progn (declaim (type ,type ,name))
    ;; since constant redefinition must be the same under EQL, there
    ;; can be no constants other than symbols, numbers and characters
    ;; see ANSI CL spec 3.1.2.1.1.3 "Constant Variables"
    (,(if (subtypep type '(or symbol number character)) 'defconstant 'defvar)
     ,name (the ,type ,init) ,doc)))

(defmacro mk-array (type init &optional len)
  "Make array with elements of TYPE, initializing."
  (if len `(make-array ,len :element-type ,type :initial-element ,init)
      `(make-array (length ,init) :element-type ,type
        :initial-contents ,init)))

(defmacro with-gensyms (syms &body body)
  "Bind symbols to gensyms.  First sym is a string - `gensym' prefix.
Inspired by Paul Graham, <On Lisp>, p. 145."
  `(let (,@(mapcar (lambda (sy) `(,sy (gensym ,(car syms)))) (cdr syms)))
    ,@body))

(defmacro map-in (fn seq &rest seqs)
  "`map-into' the first sequence, evaluating it once.
  (map-in F S) == (map-into S F S)"
  (with-gensyms ("MI-" mi)
    `(let ((,mi ,seq)) (map-into ,mi ,fn ,mi ,@seqs))))

(defun gc ()
  "Invoke the garbage collector."
  #+allegro (excl:gc)
  #+clisp (#+lisp=cl ext:gc #-lisp=cl lisp:gc)
  #+cmu (ext:gc)
  #+cormanlisp (cl::gc)
  #+gcl (si::gbc)
  #+lispworks (hcl:normal-gc)
  #+lucid (lcl:gc)
  #+sbcl (sb-ext:gc)
  #-(or allegro clisp cmu cormanlisp gcl lispworks lucid sbcl)
  (error 'not-implemented :proc (list 'gc)))

(defun quit (&optional code)
  #+allegro (excl:exit code)
  #+clisp (#+lisp=cl ext:quit #-lisp=cl lisp:quit code)
  #+cmu (ext:quit code)
  #+cormanlisp (win32:exitprocess code)
  #+gcl (lisp:bye code)
  #+lispworks (lw:quit :status code)
  #+lucid (lcl:quit code)
  #+sbcl (sb-ext:quit :unix-status (typecase code (number code) (null 0) (t 1)))
  #-(or allegro clisp cmu cormanlisp gcl lispworks lucid sbcl)
  (error 'not-implemented :proc (list 'quit code)))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (progn
    (proclaim '(ftype (function () nil) required-argument))
    (defun required-argument ()
      "A useful default for required arguments and DEFSTRUCT slots."
      (error "A required argument was not supplied."))))
