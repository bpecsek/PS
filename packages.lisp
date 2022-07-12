(eval-when (:compile-toplevel :load-toplevel :execute)
  ;; (defpackage "UNIFIER"
  ;;   (:use "COMMON-LISP")
  ;;   (:export
  ;;    #:pcvar
  ;;    #:print-pcvar
  ;;    #:unify
  ;;    #:unify-1
  ;;    #:var-unify
  ;;    #:*occurs-check-p*
	;;    #:occurs-in-p
  ;;    #:pcvar-binding
  ;;    #:extend-binding
  ;;    #:binding-value))

	(defpackage "PS"
    (:use "COMMON-LISP" "KR")
    (:export
     #:for
     #:defrule
     #:store
     #:retract
     #:reset
     #:init-pm
     #:clear
     #:rules
     #:define-rule-sets
	   #:pprules
     #:pprule
     #:excise
     #:run
     #:halt
     #:watch
     #:unwatch
     #:watch-rule-firing
	   #:set-concurrent-firing-mode
     #:facts
     ;#:show-wme
     #:deffacts
     #:list-deffacts
	   #:reset
     #:init-wm
     #:clear
     #:init-pm
	   #:reset-concurrent-firing-mode
     #:create-rule-sets
     #:quit
     #:gc)))
