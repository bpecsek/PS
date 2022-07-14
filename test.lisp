(in-package :ps)
(enable-reader-macros)

(define-rule-sets process-selection)
(init-pm process-selection)

(defun select-process-for (feature)
	(init-wm)
	(store `(exist ,feature))
	(store '(goal init))
	(run process-selection))

(defun get-best-process-for (feature)
  (format t "~:(~a~)ing" feature))

(defrule process-selection.init-rule "Initialization rule" nil
	       (assign ?a (goal init))
	       ->
	       (retract a)
	       (store '(goal select-process)))

(defrule process-selection.rule-1 "Select recommended process for features" nil
	       (assign ?a (goal select-process))
	       (exist ?feature)
	       ->
	       (retract a)
	       (store `(recommended-process-for feature
			                                    ,(get-best-process-for !feature))))

(defrule process-selection.rule-2 "Print recommended process for features" nil
	       (not (goal select-process))
	       (recommended-process-for ?feature ?process)
	       ->
	       (format t "~%Recomended process for ~s is ~s.~%" feature process)
	       (halt nil))

;(select-process-for 'drill)
