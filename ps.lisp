;;;			*The PS production system*
;;;
;;;Implementation of a small Production System based on XPS developed by
;;;Eugene Charniak at al, and presented in the authors' book "Artificial
;;;Intelligence Programming, Second Edition"
;;;
;;;Although the base framework of the original program is retained, substantial
;;;modifications have been introduced to the system to make it more efficient.
;;;
;;;Modifications made:
;;;	1, Rules are represented by KR objects.
;;;	   The behavior of the individual rules are inherited from the 
;;;	   prototype object Ps-Rule and accessed by sending messages
;;;	   to the rule-objects.
;;;	   Main advantage:
;;;		- Dynamic Rule modification can be achieved.
;;;		  That is the rules can be modified at run time for machine
;;;		  learning purposes.
;;;
;;;	2, Rule structure is modified.
;;;		a, Explicit control by salience values is introduced.
;;;		b, Rule documentation added.
;;;		c, Several modification in naming convention is made to make the
;;;		   system more CLIPS-like. (CLIPS is a Production System
;;;		   developed by NASA at the Artificial Intelligence Section of
;;;		   the Johnson Space Centre.)
;;;
;;;	3, Conflict resolution is modified to use the new salience control.
;;;
;;;	4, Rule Sets (Rule buckets) are introduced to be able to separate
;;;	   independent knowledge sets. This modification makes the overall speed
;;;	   of execution considerable faster.
;;;
;;;	5, Concurrent Rule Firing is introduced.
;;;	   This method can be used when the order in which satisfied rules are 
;;;	   fired is not important.  That is when the firing of rules
;;;	   does not modify the agenda by changing the state of the working
;;;	   memory such a way that the previously satisfied rules are not
;;;	   satisfied any more.
;;;	   (By using this method a speed up of 250-300% has been achieved 
;;;	   with the feature recognition knowledge base.)
;;;
;;;	5, Rules are linked to the blackboard on both sides of the rule.
;;;	   That is the rules can access the declarative knowledge represented by
;;;	   objects, consequently the system speed is increased substantially
;;;	   by eliminating unnecessary pattern matching.
;;;
;;;	6, Watch command is introduced to get appropriate debugging information.
;;;	   The state of execution can be watched to debug the knowledge base.
;;;
;;;	7, Unnecessary rules can be retracted by the Excise-Rule command.
;;;
;;;The syntax of defining rules in PS:
;;;
;;;	(DEFRULE <rule-set.rule-name> "documentation string"
;;;		  { (:DECLARE-SALIENCE salience-value) | nil }
;;;		  <<patterns>>	;Left-Hand Side (LHS) or prerequisite of the rule.
;;;		  ->
;;;		  <<Actions>>)	;Right-Hand Side (RHS) of the rule.
;;;				;The hole LISP environment can be used on this
;;;				;side of the rule. That feature makes PS a very
;;;				;effective rule based system. LHS of the rules
;;;				;can be compiled which makes execution faster.
;;;
;;;Eg:(Defrule Raw-Chucking.Barstock-Chucking-Rule-2
;;;		"Rule to establish chucking position for the raw material"
;;;		(:Declare-Salience 100)		;Rule priority is high.
;;;		(assign ?a (exist ?part))	;If part exists assign it to ?a
;;;		(exist ?raw-material)		  ;Raw material is known
;;;		(is-a-p ?raw-material barstock)	;Raw material is a BARSTOCK
;;;		(assign ?b (position ?pos)) ;Bar stock position is known
;;;		(assign ?c (chuck ?chuck))	;Chuck is known assign it to ?c
;;;		(between (get-diameter ?raw-material)
;;;		 	       (get-min-chucking-diameter ?chuck) 30)
;;;				     ;Raw material diameter is between the minimum
;;;				     ;chucking diameter of the chuck used and 30
;;;		->			 ;then
;;;		(retract a b c)			;Retract a, b and c from working
;;;						;memory
;;;		(set-base-position !raw-material ;Leave 0.5 mm for facing
;;;	   	(+ (get-part-length !part) !pos 1))
;;;		(store '(goal centering-method)));Store that centreing method
;;;						;is to be established next
(declaim (optimize speed (safety 0)))

(in-package "PS")

(enable-reader-macros)

;;;			*Working Memory*
;;;
;;;Working memory is organised into a discrimination net represented
;;;by a key and list of sublinks to the next nodes.
;;;
(defstruct Link (key nil) (link-list nil))

;;;
;;;(Link-Contents link) returns the contents of the node to which the link
;;;points.
;;;
(defun Link-Contents (link) (link-link-list link))

(defsetf Link-Contents (link) (value)
	`(setf (link-link-list ,link) ,value))

;;;
;;;*Working-Memory* is initialised by creating the empty discrimination net.
;;;
(defvar *working-memory* (make-link))

;;;
;;;Working memory elements are represented by a structure consisting of a
;;;time-tag and the pattern.
;;;
(defstruct Wme time-tag pattern)

;;;
;;;The empty working memory element is established by creating a wme with
;;;zero time-tag and empty pattern.
;;;
(defvar *empty-wme* (make-wme :time-tag 0 :pattern nil))

;;;
;;;(New-Time-Tag) returns a new time tag by incrementing the previous one
;;;by 1.
;;;
(let ((time 0))
	(defun New-Time-Tag () (setq time (1+ time))))

;;;
;;;(Index-1 item key link) stores item in a discrimination net starting at
;;;link, indexed by pattern.
;;;
(defun Index-1 (item key link)
	(establish-links-1 key link
		                 #'(lambda (link)
			                   (pushnew item (link-contents link)))
		                 #'(lambda (key link succeed)
			                   (let ((l (make-link :key key)))
	 		                     (push l (link-link-list link))
                                        ;add link on failure
			                     (funcall succeed l)))))

;;;
;;;
(defun Establish-Links-1 (item link succeed fail)
  (cond ((pcvar-p item) (traverse-link '*var* link succeed fail))
	      ((atom item) (traverse-link item link succeed fail))
	      (t (labels ((establish-cons (link)
		                  (traverse-link '*cons* link #'establish-car fail))
		                (establish-car (link)
		                  (establish-links-1 (car item) link #'establish-cdr fail))
		                (establish-cdr (link)
		                  (establish-links-1 (cdr item) link succeed fail)))
		         (establish-cons link)))))

;;;
;;;(Store <<pattens>>) stores facts into the working memory.
;;;One or more facts can be given as parameters to store.
;;;
(defun Store (&rest patterns)
  (dolist (pattern patterns)
	  (index-1 (make-wme :time-tag (new-time-tag) :pattern pattern)
		         pattern
		         *working-memory*)))

;;;
;;;Definition of Deffects prototype object.
;;;
(create-instance '*deffacts* nil
	(:name)
	(:comment)
	(:ruleset)
	(:facts))

;;;
;;;(List-Deffects) lists the names of deffects that are currently loaded
;;;in PS.
;;;
(defun List-Deffacts ()
	(let ((deffacts (gv *deffacts* :is-a-inv)))
	  (dolist (factset deffacts)
		  (format t "~%~s" (gv factset :name))))
	(values))

;;;
;;;(Deffacts deffacts-name "comment"" <<facts>>) grups facts wich represent
;;;initial knowledge.
;;;
;;;Eg. (Deffacts machine "Facts about machines"
;;;        (machine cns-machine-1)
;;;        (status cnc-machine-1 idle))
;;;
(defmacro Deffacts (deffacts-name comment &rest facts)
  (let ((rule-set (get-bucket-for deffacts-name))
	      (name     (get-name-for deffacts-name)))
    `(let ((factset (kr::schema-name
		                 (create-instance ',name *deffacts*
			                 (:name ',deffacts-name)
			                 (:comment ',comment)
			                 (:ruleset ',rule-set)
			                 (:facts ',facts)))))
	     factset)))

;;;
;;;(Get-All-Deffacts-Facts) returns all the initial facts defined by deffacts.
;;;
(defun Get-All-Deffacts-Facts ()
	(let ((factsets (gv *deffacts* :is-a-inv))
	      (facts nil))
	  (dolist (factset factsets)
		  (dolist (fact (gv factset :facts))
			  (push fact facts)))
	  facts))

;;;
;;;(Reset) asserts all the initial facts defined by Deffects into working
;;;memory.
;;;
(defun Reset ()
  (let ((facts (get-all-deffacts-facts)))
	  (init-wm)
	  (when facts
	    (dolist (fact facts)
		    (store fact)))))

;;;
;;;(Retract <<facts>>) ratracts facts from working memory.
;;;
(defun Retract (&rest wme)
	(if (listp wme)
	    (dolist (wm wme)
		    (unindex-1 wm (wme-pattern wm) *working-memory*))
	    (unindex-1 wme (wme-pattern wme) *working-memory*)))

;;;
;;;(Unindex-1 item pattern link) deletes item, indexed by pattern, from the
;;;discrimination tree starting at link.
;;;It returns true if item, indexed by pattern, removed from tree.
;;;
(defun Unindex-1 (item pattern link)
  (let ((sublinks (link-link-list link)))
    (if (null sublinks) nil
	      (delete-links pattern link (car sublinks) link
		                  #'(lambda (last-link pcl pcp)
			                    (let ((items (link-contents last-link)))
			                      (prog1 (member item items)
				                      (if (null
					                         (setf (link-contents last-link)
					                               (delete item items
						                                     :test #'variants-p)))
				                          (detach-link pcl pcp)))))
		                  #'(lambda (item link succeed)
     			                (declare (ignore item link succeed))
			                    nil)))))

;;;
;;;(Variant-P pat1 pat2) returns true if pattern2 is the same as pattern1,
;;;except for variable names.
;;;
(defun Variants-P (pat1 pat2)
  (let ((alist '()))
    (labels ((variant-ids-p (id1 id2)
			         (let ((entry1 (assoc id1 alist))
				             (entry2 (rassoc id2 alist)))
				         (if (and (null entry1)
					                (null entry2))
					           (push (cons id1 id2) alist))
				         (eq entry1 entry2)))
		         (test (pat1 pat2)
		           (or (and (pcvar-p pat1)
			                  (pcvar-p pat2)
			                  (variant-ids-p (pcvar-id pat1) (pcvar-id pat2)))
			             (eql pat1 pat2)
			             (and (consp pat1)
			                  (consp pat2)
			                  (test (car pat1) (car pat2))
			                  (test (cdr pat1) (cdr pat2))))))
	    (test pat1 pat2))))

;;;
;;;(Delete-Links pattern tree potential-cut-link potential-cut-pattern
;;;              success-continuation failure-continuation)
;;;Delete-links deletes the links from the discrimination tree when the
;;;patterns are to be deleted. The actual deletion of the individual links are
;;;performed by the Delete-link function.
;;;It is called by Unindex-1
;;;
(defun Delete-Links (pattern link pcl pcp succeed fail)
  (cond ((pcvar-p pattern)
	       (delete-link '*var* link pcl pcp succeed fail))
	      ((atom pattern)
	       (delete-link pattern link pcl pcp succeed fail))
	      (t (labels ((delete-cons (link pcl pcp)
		                  (delete-link '*cons* link pcl pcp #'delete-car fail))
		                (delete-car (link pcl pcp)
		                  (delete-links (car pattern) link pcl pcp
				                            #'delete-cdr fail))
		                (delete-cdr (link pcl pcp)
		                  (delete-links (cdr pattern) link pcl pcp
			                              succeed fail)))
	           (delete-cons link pcl pcp)))))

;;;
;;;(Next-Link key link) returns the next link pointing to key.
;;;
(defun Next-Link (key link)
  (find key (link-link-list link) :key #'link-key))

;;;
;;;(Traverse-Link item link succeed fail) traverses the discrimination net
;;;for links. If a link is found it returns the succeed continuation if not
;;;it returns the fail continuation which is nil.
;;;
(defun Traverse-Link (item link succeed fail)
  (let ((l (next-link item link)))
    (if (link-p l) (funcall succeed l)
		    (funcall fail item link succeed))))

;;;
;;;(Delete-Link atom link pcl pcp success-continuation failure-continuation)
;;;Traverses the sublink for atom, if possible, and updates the potential
;;;cut point if more than one sublink exists.
;;;
(defun Delete-Link (item link pcl pcp succeed fail)
  (traverse-link item link
	               #'(lambda (sublink)
			               (if (null (cdr (link-link-list link)))
			                   (funcall succeed sublink pcl pcp)
			                   (funcall succeed sublink sublink link))) fail))

;;;
;;;(Detach-Link link parent) removes link from the link-list of parent.
;;;
(defun Detach-Link (link parent)
  (if parent (setf (link-link-list parent)
		               (delete link (link-link-list parent) :test #'variants-p))))

;;;
;;;(Init-Wm) initializes *working-memory* by resetting it.
;;;
(defun Init-Wm ()
  (setq *working-memory* (make-link)))

;;;
;;;(Init-Pm rule-buckets) initializes the knowledge-base set stored in
;;;rule-bucket by destroying the rule objects, thus removing them from
;;;the rule set.
;;;Individual rule-bucket or a list of rule-bucket can be given as parameter(s)
;;;to the Init-Pm function.
;;;
(defun Init-Pm (&rest rule-buckets)
	(dolist (rule-bucket rule-buckets)
		(dolist (rule (get-ps-rules rule-bucket))
			(kr:destroy-schema rule))
		(s-value rule-bucket :is-a-inv nil)))

;;;
;;;(Clear) initializes the entire knowledge base by first initializing
;;;*working-memory* the calling Init-Pm for the existing rule-buckets.
;;;
(defun Clear ()
	(init-wm)
	(dolist (rule-bucket (get-ps-rule-buckets))
		(init-pm rule-bucket)))

;;;
;;;Type declaration for the Left-Hend Side slot of the rule.
;;;
(def-kr-type lhs-type () '(or list null) "Either list or NIL")

;;;
;;;Type declaration for the symbols.
;;;
(def-kr-type symbol-type () '(satisfies symbolp) "Must be a symbol")

;;;
;;;Type declaration for the action functions.
;;;

(def-kr-type function-type () '(or (satisfies functionp) null)
  "Either a function or NIL")

;;;
;;;Type declaration for integer between -10000 and 10000
;;;

(def-kr-type salience-type () '(or (integer -10000 10000) null)
  "An Integer type between -10000 and 10000")
;;;
;;;Definition of the Ps-Rule prototype object from which the individual rules
;;;are instantiated and their behavior is inherited.
;;;
(setq kr::*Print-As-Structure* nil
      kr::*Print-New-Structure* nil
      kr::*Warning-On-Create-Schema nil)

(create-instance 'Ps-Rule nil
  :declare ((:parameters :name :bucket :documentation :salience :patterns
		         :psvars :action :time-tags)
		        (:type (salience-type :salience)
			             (string :documentation)
			             (lhs-type :patterns)
			             (list :pcvars :time-tags)
			             (symbol-type :name :bucket)
			             (function-type :action))
		        (:sorted-slots :is-a :name :bucket :documentation :salience
				     :pcvars :action :time-tags))
	(:name)
	(:bucket)
	(:documentation "")
	(:salience 0)
	(:patterns)
	(:pcvars)
	(:action)
	(:time-tags))

;;;
;;;Interface methods and functions to access the slots of rules.
;;;
;;;The methods are defined for the prototype object Ps-Rule and
;;;inherited by the actual rules thet are instances of the prototype
;;;object.
;;;
(define-method :get-ps-rule-name ps-rule (rule)
	(gv rule :name))

(defun Ps-Rule-Name (rule)
	(kr-send ps-rule :get-ps-rule-name rule))

(define-method :get-ps-rule-bucket ps-rule (rule)
  (gv rule :bucket))

(defun Ps-Rule-Bucket (rule)
  (kr-send ps-rule :get-ps-rule-bucket rule))

(define-method :get-ps-rule-buckets ps-rule ()
	(gv ps-rule :is-a-inv))

(defun Get-Ps-Rule-Buckets ()
	(kr-send ps-rule :get-ps-rule-buckets))

(define-method :get-ps-rule-documentation ps-rule (rule)
  (gv rule :documentation))

(defun Ps-Rule-Documentation (rule)
  (kr-send ps-rule :get-ps-rule-documentation rule))

(define-method :get-ps-rule-salience ps-rule (rule)
  (gv rule :salience))

(defun Ps-Rule-Salience (rule)
  (kr-send ps-rule :get-ps-rule-salience rule))

(define-method :get-ps-rule-patterns ps-rule (rule)
  (gv rule :patterns))

(defun Ps-Rule-Patterns (rule)
  (kr-send ps-rule :get-ps-rule-patterns rule))

(define-method :get-ps-rule-pcvars ps-rule (rule)
  (gv rule :pcvars))

(defun Ps-Rule-Pcvars (rule)
  (kr-send ps-rule :get-ps-rule-pcvars rule))

(define-method :get-ps-rule-action ps-rule (rule)
  (gv rule :action))

(defun Ps-Rule-Action (rule)
  (kr-send ps-rule :get-ps-rule-action rule))

(define-method :get-ps-rule-time-tags ps-rule (rule)
  (gv rule :time-tags))

(defun Ps-Rule-Time-Tags (rule)
  (kr-send ps-rule :get-ps-rule-time-tags rule))

(define-method :get-ps-rules ps-rule (rule)
  (gv rule :is-a-inv))


;;;
;;;(Get-Ps-Rule ruleset) returns the rules of the given ruleset.
;;;
(defun Get-Ps-Rules (rule-bucket)
  (kr-send ps-rule :get-ps-rules rule-bucket))

;;;
;;;(Define-Rule-Sets <<rulesets>>) creates one or more rule-sets.
;;;
;;;To create one ruleset only a single ruleset must be given as parameter.
;;;Eg. 1, (Define-Rule-Sets Recognizer) creates ruleset Recognizer.
;;;
;;;To create more then one rulesets a list of the rulesets must be given as
;;;parameter.
;;;    2, (Define-Rule-Sets Recognizer Machinesel Rawmatsel)
;;;          Creates rulesets Recognizer, Machinesel and Rawmatsel.
;;;
;;;Alternatively new ruleset can be defined by creating the ruleset directly
;;;by instantiating it from Ps-Rule.
;;;
;;;Eq. (create-instance 'new-ruleset Ps-Rule)
;;;
(defmacro Define-Rule-Sets (&rest rulesets)
	`(dolist (set ',rulesets)
		 (create-instance set ps-rule)))

;;;
;;;Creation of four rulesets.
;;;   - Recognizer for feature recognition.
;;;   - Machinesel for machine selection.
;;;   - Raw-Chucking for raw material chucking determination.
;;;   - Rawmatsel for raw material selection.
;;;
                                        ; (Define-Rule-Sets Recognizer Machinesel Raw-Chucking Rawmatsel)

;;;
;;;(Ps-Rule-P rule) is a predicate function and returns true if rule is a
;;;valid rule, otherwise it returns false.
;;;
(defun Ps-Rule-P (rule)
	(is-a-p rule ps-rule))

;;;
;;;(Get-Bucket-For rule) Returns the rule bucket of the rule.
;;;
;;;Eg. (Get-Bucket-For 'Recognizer.Rule-1) returns Recognizer.
;;;
(defun Get-Bucket-For (rule)
	(let* ((name-string (string rule))
	       (bucket (read-from-string (subseq name-string 0
					                                 (position #\. name-string )))))
	  bucket))

;;;
;;;(Get-Name-For rule) returns the name of the rule.
;;;
;;;Eg. (Get-Name-For 'Recognizer.Rule-1) returns Rule-1.
;;;
(defun Get-Name-For (rule)
  (let* ((name-string (string rule))
         (rule-name (read-from-string (subseq name-string
				                                      (1+ (position #\. name-string ))))))
	  rule-name))

;;;
;;;Macro for defining Rules.
;;;
;;;The rule definition syntax is given in the header section of this file.
;;;
(defmacro Defrule (rule doc-string (&key (declare-salience  0)) . rest)
  (let ((bucket    (get-bucket-for rule))
	      (rule-name (get-name-for rule)))
    (parse-ps-rule rest
                   #'(lambda (lhs rhs)
	                     (let* ((pcvars (pcvars-in lhs '()))
		                          (lambda-vars (mapcar #'pcvar-id pcvars)))
		                     `(let ((ps-rule (kr::schema-name
			                                    (create-instance ',rule ,bucket
				                                    (:name ',rule-name)
				                                    (:bucket ',bucket)
				                                    (:documentation ',doc-string)
				                                    (:salience ',declare-salience)
				                                    (:patterns ',lhs)
				                                    (:pcvars ',pcvars)
				                                    (:action #'(lambda ,lambda-vars ,@rhs))
				                                    (:time-tags '())))))
	                          ps-rule))))))

;;;
;;;(Parse-Ps-Rule rule-form continuation) cuts the rule into LHS and
;;;RHS and calls the continuation function with the left and right hand
;;;side of the rule.
;;;
;;;It gives an error message "Missing -> in <rule-name>" if the then
;;;sine -> is missing from the rule definition.
;;;
(defun Parse-Ps-Rule (rule-form -c-)
  (let ((l (member '-> rule-form)))
    (if (null l)
	      (error  "Missing -> in ~s~%." rule-form)
	      (funcall -c- (ldiff rule-form l) (cdr l)))))

;;;
;;;(Pcvars-In pattern vars) returns the list of pattern variables.
;;;
(defun Pcvars-In (pattern vars)
  (cond ((pcvar-p pattern)
	       (if (member (pcvar-id pattern) vars :key #'pcvar-id)
	           vars
	           (cons pattern vars)))
	      ((atom pattern) vars)
	      (t (pcvars-in (cdr pattern)
	                    (pcvars-in (car pattern) vars)))))

;;;
;;;(Rules rule-bucket) returns the names and the total number of rules
;;;in rule-backet
;;;
(defun Rules (rule-bucket)
  (format t "~%Rule-bucket: ~s~%" rule-bucket)
  (let ((rules (get-ps-rules rule-bucket)))
    (dolist (rule rules)
	    (format t "~s~%" rule))
    (format t "~%Number of rules in rule-bucket ~s is : ~s" rule-bucket
		        (length rules)))
	(values))

;;;
;;;(Pprules rule-bucket) returns the rules of the ruleset by listing
;;;the structure of the rules, as well as the total number of rules in the
;;;ruleset.
;;;
(defun Pprules (rule-bucket)
  (format t "~%Rule-bucket: ~s" rule-bucket)
  (let ((rules (get-ps-rules rule-bucket)))
    (dolist (rule rules)
      (format t "Name : ~s~%Rule-bucket : ~s~%Documentation : ~s
Salience : ~s~%Patterns :~%~{~s~%~}   ->~%Action : ~%~s~2%"
              (ps-rule-name rule)
              (ps-rule-bucket rule)
              (ps-rule-documentation rule)
              (ps-rule-salience rule)
              (ps-rule-patterns rule)
              (ps-rule-action rule)))
    (format t "~2%Number of rules in rule-bucket ~s is : ~s" rule-bucket
		        (length rules)))
  (values))

;;;
;;;(Pprule rule) returns the structure of the rule.
;;;If the rule is not in the ruleset message is given and some hints
;;;how to figure out the existance of the rule.
;;;
(defun Pprule (rule)
  (let* ((rule-bucket (get-bucket-for (kr::schema-name rule)))
	       (rules-in-bucket (get-ps-rules (eval rule-bucket))))
	  (if (not (member rule rules-in-bucket))
        (progn
          (format t "~%~s is not a member of Ps-Rules." (kr::schema-name rule))
          (format t "~%Check if ~s is a legal Rule Bucket!" rule-bucket)
          (format t "~%~s is a legal Rule Bucket if it's a sub-class of Ps-Rules."
	                rule-bucket)
          (format t "~%Hint : Please evaluate (is-a-p ~s ps-rule) and check if it's T."
	                rule-bucket))
        (format t "Name : ~s~%Rule-Bucket : ~s~%Documentation : ~s~%Salience : ~s
~%Patterns :~%~{~s~%~} ->~%Action :~%~s~%"
                (ps-rule-name rule)
                (ps-rule-bucket rule)
                (ps-rule-documentation rule)
                (ps-rule-salience rule)
                (ps-rule-patterns rule)
                (ps-rule-action rule)))))

;;;
;;;(Excise rules) removes the rules from the ruleset by destroying
;;;the object of the rule.
;;;
;;;Eg. 1, (Excise Recognizer.Rule-1) removes Rule-1 from Recognizer ruleset.
;;;
;;;    2, (Excise Recognizer.Rule-1 Recognizer.Rule-2) removes Rule-1 and
;;;          Rule-2 from ruleset Recognizer.
;;;
(defun Excise (&rest rules)
	(dolist (rule rules)
		(if (ps-rule-p rule)
		    (kr::destroy-schema rule)
		    (format t "~s is not a valid rule.~%" rule)))
	(values))

;;;
;;;Global variable definition for *concurrent-fire-p*.
;;;
(defvar *concurrent-fire-p* nil)

;;;
;;;(Set-Concurrent-Firing-Mode) sets concurrent firing mode of the
;;;inference engine.
;;;
(defun Set-Concurrent-Firing-Mode ()
	(setq *concurrent-fire-p* t))

;;;
;;;(Reset-Concurrent-Firing-Mode) resets concurrent firing mode.
;;;
(defun Reset-Concurrent-Firing-Mode ()
  (setq *concurrent-fire-p* nil))

;;;
;;;Global variable for *rule-firing*.
;;;
(defvar *rule-firing* t)

;;;
;;;Helpping functions for the Watch command.
;;;(Watch-Rule-Firing) sets rule firing mode of the inference engine.
;;;
(defun Watch-Rule-Firing ()
	(setq *rule-firing* t))

;;;
;;;(Unwatch-Rule-Firing) resets rule fireing mode of the inference engine.
;;;
(defun Unwatch-Rule-Firing ()
  (setq *rule-firing* nil))

(defvar *consider-print* nil)

;;;
;;;(Watch-Rule-Consideration) sets rule consideration execution mode of the
;;;inference engine.
;;;
(defun Watch-Rule-Consideration ()
	(setq *consider-print* t))

;;;
;;;(Unwatch-Rule-Consideratio) resets rule consideration execution mode of the
;;;inference engine.
;;;
(defun Unwatch-Rule-Consideration ()
  (setq *consider-print* nil))

;;;
;;;(Watch conditions) sets conditions for debuging.
;;;Different conditions can be given to be watched during exicution.
;;;
;;;Eq. 1, (Watch rule-fireing) sets rule-fireing to be watched.
;;;		If this command, is given the inferrence engine prints the
;;;		message "Firing rule <rule-name>.")
;;;
;;;	 2, (Watch rule-fireing rule-consideration) sets rule-fireing
;;;		and rule-considerations to be watched.
;;;		If this commands is given the inferrence engine is
;;;		instructed to print the rule-firing message as well as the
;;;		rule-consideration message.
;;;			"I am comsidering rule <rule-name> for firing..."
;;;
(defmacro Watch (&rest conditions)
	`(dolist (condition ',conditions)
		 (case condition
		   (rule-firing (watch-rule-firing))
		   (rule-consideration (watch-rule-consideration))
		   (all (watch-rule-firing)
			  (watch-rule-consideration)))))

;;;
;;;(Unwatch conditions) resets the watching conditions.
;;;The syntax of Unwatch is the same as the syntax of Watch.
;;;
(defmacro Unwatch (&rest conditions)
	`(dolist (condition ',conditions)
		 (case condition
		   (rule-firing (unwatch-rule-firing))
		   (rule-consideration (unwatch-rule-consideration))
		   (all (unwatch-rule-fireing)
			  (unwatch-rule-consideration)))))

;;;
;;;(Run rule-bucket) runs the production system with rule-bucket.
;;;
;;;Run is the top level command of the PS production system. The cycle is to
;;;compute the conflict set, that is to find the rules in rule-bucket that are
;;;sattisfied by fects, choose one rule from the conflict set, fire it and
;;;start over.
;;;
;;;If the conflict set is empty, which means there is no rule which is
;;;sattisfied by fects thus no rules can fire, terminate the loop with the
;;;message "Empty conflict set." and halt the system.
;;;
;;;The other way to halt the system is to have a rule action call the
;;;function HALT.
;;;
(defun Run (rule-bucket)
  (declare (optimize speed (safety 0)))
	(catch 'ps-run
	  (loop
		  (let ((conflict-set (compute-agenda rule-bucket)))
		    (cond ((null conflict-set)
			         (format t "~%Empty conflict set~%")
			         (return))
			        (t (fire (resolve-conflicts conflict-set))))))))

;;;
;;;(Halt return-value) halts the system and returns the returm-value by
;;;calling the throw command that throws the catched symbol 'xps-run.
;;;
(defun Halt (return-value) (throw 'ps-run return-value))

;;;
;;;(Facts [<start> [<end> [<maximum>]]]) returns the list of the facts in 
;;;working memory by listing their time-tags and patterns.
;;;
;;;When no argument is given the entire working memory is listed.
;;;
;;;If the <start> argument is specified but not end and maximum, all facts with
;;;time-tags greater then or equal to <start> are displayed.
;;;
;;;If <start> and <end> are specified, all facts with time-tags greater then or
;;;equal to <start> and less then or equal to <end> are displayed.
;;;
;;;If the <maximum> argument is also specified along with <start> and <end>,
;;;no more than <maximum> facts will be displayed.
;;;
(defun Facts (&optional start end maximum)
  (let ((sorted-facts (sort (ps-fetch '?x) #'< :key #'wme-time-tag)))
    (cond ((not start)
	         (dolist (wme sorted-facts)
		         (format t "F-~s : ~s~%"(wme-time-tag wme)(wme-pattern wme))))
	        ((and start (not end))
	         (loop for wme in sorted-facts
		             when (>= (wme-time-tag wme) start)
 		               do (format t "F-~s : ~s~%"(wme-time-tag wme)(wme-pattern wme))))
	        ((and start end)
	         (loop for wme in sorted-facts
		             when (and (>= (wme-time-tag wme) start)
			                     (<= (wme-time-tag wme) end))
		               do (format t "F-~s : ~s~%"(wme-time-tag wme)(wme-pattern wme))))
	        ((and start end maximum)
	         (loop for wme in sorted-facts
		             when (and (>= (wme-time-tag wme) start)
			                     (<= (wme-time-tag wme) end)
			                     (< (wme-time-tag wme)  (+ start maximum)))
		               do (format t "F-~s : ~s~%"(wme-time-tag wme)(wme-pattern wme)))
	         )))
  (values))

;;;
;;;(Fact time-tag) returns the fact with wme-time-tag equal to time-tag.
;;;
(defun Show-Fact (time-tag)
  (let* ((wme (find time-tag (ps-fetch '?x) :key #'wme-time-tag)))
	  (format t "F-~s : ~s~%" (wme-time-tag wme) (wme-pattern wme)))
	(values))

(Def-Kr-Type Rule-Type () '(or null (satisfies ps-rule-p)))

(create-instance 'Instances nil
  :declare ((:parameters :rule :sub :time-tags)
	          (:type (rule-type :rule)
		               (list :sub :time-tags))
	          (:sorted-slots :rule :sub :time-tags))
	(:rule)
	(:sub)
	(:time-tags))

;;;
;;;Interface methods and functions to access slots of agenda rules.
;;;
(define-method :get-instances-rule instances (instance)
	(gv instance :rule))

(defun Instances-Rule (instance)
	(kr-send instances :get-instances-rule instance))

(define-method :get-instances-sub instances (instance)
  (gv instance :sub))

(defun Instances-Sub (instance)
  (kr-send instances :get-instances-sub instance))

(define-method :get-instances-time-tags instances (instance)
  (gv instance :time-tags))

(defun Instances-Time-Tags (instance)
  (kr-send instances :get-instances-time-tags instance))

;;;
;;;(Compute-Agenda rule-bucket) goes through all the production rules
;;;of the given ruleset and tests each rule with Test-Pattern to check if
;;;the rule is satisfied by facts. If the rule is satisfied it creates
;;;an instance of the satisfied rule with the substitution list and time-tags
;;;and puts it into the agenda. (Agenda is the set of the satisfied rules in
;;;a given cycle ofo execution.)
;;;When there is no more rule found the agenda is return for conflict
;;;resolution.
;;;
;;;Refraction is taken care of here by checking if the rule has already been
;;;fired or not. If the rule has already been fired on the same fact
;;;refraction blocks the rule to fire again.
;;;
(defun Compute-Agenda (rule-bucket)
  (declare (optimize speed (safety 0)))
  (let ((agenda '()))
    (dolist (rule (get-ps-rules rule-bucket))
	    (if *consider-print*
		      (format t "I am considering ~S for firing...~%"
			            (ps-rule-name rule)))
	    (test-patterns (ps-rule-patterns rule) '() '()
		                 #'(lambda (sub time-tags)
			                   (unless (already-fired-p rule time-tags)
		                       (push (create-instance nil instances ;It is fuster with
				                           (:rule rule)               ;structure!!!!
				                           (:sub sub)
				                           (:time-tags time-tags))
			                           agenda)))))
    agenda))

;;;
;;;(Test-Patterns pattern substitution time-tags continuation) returns both
;;;the variable bindings and the time tags of the satisfied facts retrieved
;;;from working memory by doing conjunct retrieval on the pattern.
;;;If all the patterns in the rule, that is the entire LHS is satisfied, than
;;;the continuation passed to Test-Pattern is called.
;;;
(defun Test-Patterns (patterns sub time-tags -c-)
  (declare (optimize speed (safety 0)))
  (if (null patterns)
      (funcall -c- sub time-tags)
      (ps-retrieve (replace-variables (car patterns) sub)
		               #'(lambda (sub2 wme)
			                 (test-patterns (cdr patterns) (append sub2 sub)
					                            (cons (wme-time-tag wme) time-tags)
	                                    -c-)))))

;;;
;;;(Replace-Variable pattern substitution) replaces all the variables with
;;;their values, if any, as determined by using Pcvar-Value and substitution.
;;;The value of a variable with no binding in substitution is itself.
;;;
(defun Replace-Variables (pat sub)
	(cond ((pcvar-p pat) (pcvar-value pat sub))
	      ((atom pat) pat)
	      (t (cons (replace-variables (car pat) sub)
		             (replace-variables (cdr pat) sub)))))

;;;
;;;(Pcvar-Value pattern substitution) If variable is bound to another variable,
;;;or to a functional term containing variables, it replaces those variables
;;;with their bindings, if any, as determined by substitution.
;;;
(defun Pcvar-Value (pat sub)
	(let ((binding (pcvar-binding pat sub)))
	  (cond ((null binding) pat)
		      (t (let ((value (binding-value binding)))
			         (cond ((eql value pat) pat)
				             (t (replace-variables value sub))))))))

;;;
;;;(Already-Fired-P ps-rule time-tags) returns not nil if the rule has been
;;;fired already on the fact.
;;;This function carries out the refraction of the rule.
;;;
(defun Already-Fired-P (ps-rule time-tags)
  (member time-tags (ps-rule-time-tags ps-rule) :test #'equal))

;;;
;;;(Ps-Retrieve pattern continuation) uses fetcher to get working memory
;;;elements, and the unifier to match patterns against working memory elements.
;;;
;;;For every match, the retriever returns both the substitution list and the
;;;working memory elements.
;;;
(defun Ps-Retrieve (pat -c-)
  (let ((method (and (consp pat)
		                 (ps-retrieval-method (pattern-head pat)))))
    (if method
	      (funcall method pat -c-)
	      (dolist (wme (ps-fetch pat))
		      (dolist (sub (unify pat (wme-pattern wme)))
			      (funcall -c- sub wme))))))

;;;
;;;(Patter-Head pattern ) returns the first element (head) of the pattern.
;;;
(defun Pattern-Head (pat) (car pat))

;;;
;;;(Pattern-Args pattern) returns the elements of the pattern but the first
;;;one.
;;;
(defun Pattern-Args (pat) (cdr pat))

;;;
;;;                        *The pattern fetcher for PS*
;;;
;;;(Ps-Fetch pattern) gets working memory elements.
;;;
(defun Ps-Fetch (pat)
  (declare (optimize speed (safety 0)))
  (fetch-2 pat *working-memory*))

;;;
;;;(Fetch-2 item link) fetchs item or items from working memory and returns
;;;the ones that match the pattern of item as a list or nil if there is no
;;;metching pattern in the working memory.
;;;
;;;Eg. *working-memory* = ((insert roughing i-1)    ;In reality, facts are
;;;                        (insert roughing i-13)   ;stored as discrimination
;;;                        (insert finishing i-25)) ;net.
;;; Then
;;;(Fatch-2 '(insert roughing ?x) *working-memory*) returns
;;;
;;;> ((insert roughing i-1) (insert roughing i-13))
;;;
(defun Fetch-2 (item link)
  (declare (optimize speed (safety 0)))
  (let ((results '()))
    (traverse-links-2 item link
		                  #'(lambda (link)
				                  (setq results
				                        (append (link-contents link) results)))
		                  #'(lambda (item link succeed)
				                  (declare (ignore item link succeed))
				                  nil))
    results))

;;;
;;;(Traverse-Links-2 item link succeed fail) traverses the discrimination net.
;;;If there is a variable in the item it skips the variable and continues
;;;traversing the net.
;;;If the item is found, the succeed continuation is called otherwise
;;;it calls the fail continuation which is effectively nil.
;;;
(defun Traverse-Links-2 (item link succeed fail)
  (declare (optimize speed (safety 0)))
  (cond ((pcvar-p item) (skip-exp link succeed))
	      (t (if (atom item)
	             (traverse-link item link succeed fail)
	             (labels ((traverse-cons (link)
				                  (traverse-link '*cons*
						                             link #'traverse-car fail))
			                  (traverse-car (link)
				                  (traverse-links-2 (car item)
						                                link #'traverse-cdr fail))
			                  (traverse-cdr (link)
				                  (traverse-links-2 (cdr item)
						                                link succeed fail)))
		             (traverse-cons link)))
	         (traverse-link '*var* link succeed fail))))

;;;
;;;(Skip-Exp link succeed) skips over variables in the discrimination net.
;;;
(defun Skip-Exp (link succeed)
	(dolist (sublink (link-link-list link))
		(cond ((not (eq (link-key sublink) '*cons*))
		       (funcall succeed sublink))
		      (t (skip-exp sublink
				               #'(lambda (link)
					                 (skip-exp link succeed)))))))

;;;
;;;                   *Conflict Resolution*
;;;
;;;If only one rule is found to fire during the recognize-act cycle, then that
;;;rule fires, and the cycle starts over. However in real situation usually
;;;more than one rules are satisfied. In this situation a so called conflict
;;;resolution is required.
;;;
;;;In PS a five level conflict resolution strategy is applied. During this
;;;conflict resolution the agenda or conflict set is filtered using five
;;;filters. If every rule except one is eliminated by the filteres on any
;;;level of the conflict resolution, it is returned to be fired.
;;;
;;;1. Refraction filter:
;;;   The first level is the refraction that is taken care of in the Compute-
;;;   Conflict-Set function. Refraction means that if the rule has already
;;;   fired on the same fect it won't fire again doing so endless loops are
;;;   effectively eliminated.
;;;
;;;2. Salience filter:
;;;   At the second level the rules with the highest salience value are only
;;;   kept. The rest is filtered out. If only one remained it is returned and
;;;   fired.
;;;
;;;3. Recency filter:
;;;   At the third level the rules that matched the facts with the highest
;;;   time-tags, that means the ones that has been more recently stored in
;;;   working memory are collected. When only one rule survived the previous
;;;   filter it is immediately returned.
;;;
;;;4. Specificity filter:
;;;   At the fourth level the rules with the highes number of conditions on
;;;   the LHS are given preference. The rest is filtered out.
;;;
;;;5. Pick randomly:
;;;   If even after the four previous filter more than one rule remained than
;;;   one is picked randomly.
;;;
;;;Although this five-level conflict resolution gives an effective strategy to
;;;resolve conflict among rules, in some cases when the state of the problem
;;;domain is not changed by the rule fireing every filter except the first
;;;can by eliminated. This strategy has been incorporated into the conflict
;;;resolution and called here "Concurrent Rule Firing Mode". CRFM can be set
;;;whith the (Set-Concurrent-Firing-Mode).
;;;By the introduction of this strategy a 250-300% increase in speed has been
;;;gained with the feature recognition knowledge base.
;;;
(defun Resolve-Conflicts (instances)
  (if *concurrent-fire-p*
      (try-high-salience instances)
      (pick-random (try-specificity (try-recency (try-high-salience instances))))))

;;;
;;;(Try-High-Salience instances) returns the rules with the highest salience.
;;;
(defun Try-High-Salience (instances)
  (if (null (cdr instances))
      instances
      (flet ((rules-salience (instance)
			         (ps-rule-salience (instances-rule instance))))
	      (first-equiv-class instances #'> :key #'rules-salience))))

;;;
;;;(Try-Recency instances) returns the rules that matched the facts that are
;;;most recent.
;;;
(defun Try-Recency (instances)
  (if (null (cdr instances)) instances
      (flet ((sorted-time-tags (instance)
	             (sort (remove-duplicates (instances-time-tags instance)) #'>)))
	      (first-equiv-class instances #'lex> :key #'sorted-time-tags))))

;;;
;;;(Try-Specificity instances) returns the rules with the highest number of
;;;conditions on the LHS of the rules.
;;;
(defun Try-Specificity (instances)
  (if (null (cdr instances))
      instances
      (flet ((specificity (instance)
			         (length (instances-time-tags instance))))
	      (first-equiv-class instances #'> :key #'specificity))))

;;;
;;;(Get-Rule-Name instance) returns the name of the rule of the instance.
;;;
(defun Get-Rule-Name (instance)
	(ps-rule-name (instances-rule instance)))

;;;
;;;(Pick-Random instances) picks one instance out of the instances that
;;;survived the previous filters.
;;;
(defun Pick-Random (instances)
  (cond ((null (cdr instances)) (car instances))
        (t (dolist (instance instances)
		         (format t "Resolving tie at random : ~s~%"
			               (get-rule-name instance)))
	         (nth (random (length instances)) instances))))

;;;
;;;(Lex> l1 l2) returns true or false depending on the lexicographical
;;;relation of the two lists.
;;;
(defun Lex> (l1 l2)
	(cond ((null l1) nil)
	      ((null l2) t)
	      ((> (car l1) (car l2)) t)
	      ((< (car l1) (car l2)) nil)
	      (t (lex> (cdr l1) (cdr l2)))))

;;;
;;;(First-Equiv-Class list predicate key-function) returns a subset C of L
;;;with the following properties:
;;;
;;;If x is in C and Y is in L but not in C, then pred(key(x),key(y)) is true.
;;;
;;;If x and y are both in C, then pred(key(x),key(y)) is false.
;;;
(defun First-Equiv-Class (list pred &key (key #'identity))
  (if (null (cdr list))
      list
      (let ((class nil)
	          (val nil))
	      (mapc #'(lambda (x)
			            (let ((new-val (funcall key x)))
				            (cond ((or (null class)
					                     (funcall pred new-val val))
					                 (setq val new-val)
					                 (setq class (list x)))
				                  ((not (funcall pred val new-val))
					                 (push x class))))) list)
	      (nreverse class))))

;;;
;;;(Fire instances) fires, that is executes the RHS of the rule or rules
;;;given as parameter(s) to Fire.
;;;A local function fire-rule is defined and called depending on the the
;;;number of rules passed to Fire.
;;;
;;;If only one rule is passed, that is concurrent fireing mode is set to nil,
;;;then fire-rule is called with that rule.
;;;
;;;If a list of rules are given then fire-rule is called with the individual
;;;rule in a loop.
;;;
(defun Fire (instances)
  (flet ((fire-rule (instance)
		       (let ((ps-rule (instances-rule instance))
			           (sub (instances-sub instance))
			           (tags (instances-time-tags instance)))
			       (when *rule-firing*
			         (format t "~%Firing rule ~s~%"
					             (ps-rule-name ps-rule)))
			       (push tags (gv ps-rule :time-tags))
			       (apply (ps-rule-action ps-rule)
				            (for (pcvar :in (ps-rule-pcvars ps-rule))
				                 :save (binding-value
					                      (pcvar-binding pcvar sub)))))))
	  (if (listp instances)
	      (dolist (inst instances)
		      (fire-rule inst))
	      (fire-rule instances))))

;;;
;;;                *Retrieval-Methods*
;;;
;;;Definition of data-driven retrieval methods for retrieving working memory
;;;elements for patterns.
;;;
;;;Data-driven retrieval methods are stored in a hash-table and indexed
;;;by the name of the retrieval method.
;;;

;;;
;;;Definition of hash-table for storing the retrieval methods.
;;;
(defvar *ps-retrieval-methods* (make-hash-table))

;;;
;;;(Ps-Retrieval-Method name) returns the function stored in the hash-table
;;;*ps-retrieval-method* with Define-Retrieval-Method.
;;;
(defun Ps-Retrieval-Method (name)
  (gethash name *ps-retrieval-methods*))

;;;
;;;(Set-Ps-Retrieval-Methos name proc) srores the retrieval method into the
;;;hash-table indexed by its name.
;;;
(defun Set-Ps-Retrieval-Method (name proc)
	(setf (gethash name *ps-retrieval-methods*) proc))

(defsetf Ps-Retrieval-Method Set-Ps-Retrieval-Method)

;;;
;;;(Define-Ps-Retrieval-Method symbol (variables) code) associates symbol
;;;with a function that knows how to retrieve patterns of the form variable.
;;;
(defmacro Define-Ps-Retrieval-Method (head args &body body)
  `(progn (setf (ps-retrieval-method ',head)
		            #'(lambda ,args ,@body))
	        ',head))

;;;
;;;                         *Definition of Retrieval Methods*
;;;
;;;Retrieval method for Assign.
;;;
;;;(Assign element-var subpattern) calls Ps-Retrieve with subpattern and a
;;;continuation that extends the substitution list to bind element-variable
;;;to whatever working memory element is retrieved.
;;;
(define-ps-retrieval-method Assign (pat -c-)
  (let ((var (car (pattern-args pat)))
	      (subpat (cadr (pattern-args pat))))
    (ps-retrieve subpat
		             #'(lambda (sub wme)
			               (funcall -c- (extend-binding var wme sub) wme)))))

;;;
;;;Retrieval method for And:
;;;
;;;(And <<paterns>>) calls Ps-Conjucts-Retrieve on every pattern and returns
;;;the one with the highest time-tag.
;;;
(defun Ps-Conjuncts-Retrieve (conjuncts sub wme -c-)
  (if (null conjuncts)
      (funcall -c- sub wme)
      (ps-retrieve
       (replace-variables (car conjuncts) sub)
       #'(lambda (sub-2 wme-2)
		       (ps-conjuncts-retrieve
		        (cdr conjuncts)
		        (append sub-2 sub)
		        (if (> (wme-time-tag wme-2)
			             (wme-time-tag wme))
		            wme-2
		            wme)
		        -c-)))))

(define-ps-retrieval-method And (pat -c-)
	(ps-conjuncts-retrieve (pattern-args pat) '() *empty-wme* -c-))

(define-ps-retrieval-method Exist (pat -c-)
  (let* ((a (pattern-args pat)))
    (if (ps-retrieve (replace-variables a '()) -c-)
        (funcall -c- nil *empty-wme*))))

#|
(define-ps-retrieval-method Or (pat -c-)
(ps-or-retrieve
(pattern-args pat)
'()
*empty-wme*
-c-))

(defun Ps-Or-Retrieve (conjuncts sub wme -c-)
(if (null conjuncts)
(funcall -c- sub wme)
(ps-retrieve (replace-variables (car conjuncts) sub)
#'(lambda (sub-2 wme-2)
(return-from out nil) 
(ps-or-retrieve
(cdr conjuncts)
(append sub-2 sub)
(if (> (wme-time-tag wme-2)
(wme-time-tag wme))
wme-2
wme)
-c-)))))

(define-ps-retrieval-method Is-A-P (pat -c-)
(let* ((a (car (pattern-args pat)))
(b (cadr (pattern-args pat)))
(c (eval (ps-retrieve (replace-variables a '())))))
(if (is-a-p c b)
(funcall -c- nil *empty-wme*))))

;(define-ps-retrieval-method Exist (pat -c-) ; ;
 ; (let* ((a (pattern-args pat)))       ; ;
	;(if (ps-retrieve (replace-variables a '()) -c-) ; ;
	;(funcall -c- nil *empty-wme*))))     ; ;
|#

;;;
;;;Retrieval method for Not.
;;;
;;;(Not pattern) calls its continuation with a special element *empty-wme*
;;;when there is no working memory element that match pattern. If the pattern
;;;ever matchs it immediately returns without calling the continuation passed
;;;to Not's retrieval method.
;;;
(define-ps-retrieval-method Not (pat -c-)
  (block not-body
	  (ps-retrieve (car (pattern-args pat))
		             #'(lambda (sub wme)
				             (declare (ignore sub wme))
				             (return-from not-body nil)))
	  (funcall -c- nil *empty-wme*)))

;;;
;;;Retrieval method for Equal.
;;;
;;;(Equal pattern1 pattern2) calls its continuation with *empty-wme* if
;;;pattern1 and pattern2 matches.
;;;
(define-ps-retrieval-method Equal (pat -c-)
  (let ((a (car (pattern-args pat)))
	      (b (cadr (pattern-args pat))))
    (dolist (sub (unify a b))
	    (funcall -c- sub *empty-wme*))))

;;;
;;;Retrieval method for Eql.
;;;
;;;(Eql symbol1 symbol2) calls its continuation with *empty-wme* if symbol1
;;;is eql to symbol2.
;;;
(define-ps-retrieval-method Eql (pat -c-)
  (let ((a (eval (car (pattern-args pat))))
	      (b (cadr (pattern-args pat))))
    (if (and (symbolp a) (symbolp b) (eql a b))
	      (funcall -c- nil *empty-wme*))))

;;;
;;;Retrieval method for Is-A-P.
;;;
;;;(Is-a-p pattern1 pattern2) calls its continuation with *empty-wme* when
;;;pattern1 is a pattern2.
;;;
(define-ps-retrieval-method Is-A-P (pat -c-)
  (let ((a (if  (not (listp (car (pattern-args pat))))
		            (eval (car (pattern-args pat)))
		            (car (pattern-args pat))))
	      (b	(eval (cadr (pattern-args pat)))))
    (if (is-a-p a b)
	      (funcall -c- nil *empty-wme*))))

#|
(define-ps-retrieval-method Line-Mode (pat -c-)
(let ((a (car (pattern-args pat)))
(b (cadr (pattern-args pat))))
(c (unify a b)))
(if (eql ((caaar c) (second (caar '(((A A))))))
(funcall -c- nil *empty-wme*)))

(define-ps-retrieval-method Next-Line (pat -c-)
(let ((a (if  (not (listp (car (pattern-args pat))))
(eval (car (pattern-args pat)))
(car (pattern-args pat))))
(b      (eval (cadr (pattern-args pat)))))
(if (is-next-line? a b)
(funcall -c- nil *empty-wme*))))

(define-ps-retrieval-method Recognized (pat -c-)
(let ((a (if  (not (listp (car (pattern-args pat))))
(eval (car (pattern-args pat)))
(car (pattern-args pat)))))
(if (is-recognised? a) 
(funcall -c- nil *empty-wme*))))

(define-ps-retrieval-method Not-Recognized (pat -c-)
(let ((a (if  (not (listp (car (pattern-args pat))))
(eval (car (pattern-args pat)))
(car (pattern-args pat)))))
(if (is-recognised? a)
nil
(funcall -c- nil *empty-wme*))))


(define-ps-retrieval-method Is-A-P (pat -c-)
(let ((a (eval (car (pattern-args pat))))
(b (eval (cadr (pattern-args pat)))))
(if (is-a-p a b)
(funcall -c- nil *empty-wme*)
(format t "~S ~S~%" a b))))
|#

;;;
;;;Retrieval method for >.
;;;
;;;(> pattern1 pattern2) calls its continuation with *empty-wme* if both
;;;pattern1 and pattern2 are numbers and pattern1 is greater the pattern2.
;;;
(define-ps-retrieval-method > (pat -c-)
  (let* ((1st (first (pattern-args pat)))
	       (2nd (second (pattern-args pat)))
	       (a (if (listp 1st) (eval 1st) 1st))
	       (b (if (listp 2nd) (eval 2nd) 2nd)))
	  (if (and (numberp a) (numberp b) (> a b))
	      (funcall -c- nil *empty-wme*))))

;;;
;;;Retrieval method for <.
;;;
;;;(< pattern1 pattern2) calls its continuation with *empty-wme* if both
;;;pattern1 and pattern2 are numbers and pattern1 is less the pattern2.
;;;
(define-ps-retrieval-method < (pat -c-)
  (let* ((1st (first (pattern-args pat)))
	       (2nd (second (pattern-args pat)))
	       (a (if (listp 1st) (eval 1st) 1st))
	       (b (if (listp 2nd) (eval 2nd) 2nd)))
	  (if (and (numberp a) (numberp b) (< a b))
	      (funcall -c- nil *empty-wme*))))

;;;
;;;Retrieval method for >=.
;;;
;;;(>= pattern1 pattern2) calls its continuation with *empty-wme* if both
;;;pattern1 and pattern2 are numbers and pattern1 is greater or equal to
;;;pattern2.
;;;
(define-ps-retrieval-method >= (pat -c-)
  (let* ((1st (first (pattern-args pat)))
	       (2nd (second (pattern-args pat)))
	       (a (if (listp 1st) (eval 1st) 1st))
	       (b (if (listp 2nd) (eval 2nd) 2nd)))
	  (if (and (numberp a) (numberp b) (>= a b))
	      (funcall -c- nil *empty-wme*))))

;;;
;;;Retrieval method for <=.
;;;
;;;(<= pattern1 pattern2) calls its continuation with *empty-wme* if both
;;;pattern1 and pattern2 are numbers and pattern1 is less then or equal to
;;;pattern2.
;;;
(define-ps-retrieval-method <= (pat -c-)
  (let* ((1st (first (pattern-args pat)))
	       (2nd (second (pattern-args pat)))
	       (a (if (listp 1st) (eval 1st) 1st))
	       (b (if (listp 2nd) (eval 2nd) 2nd)))
	  (if (and (numberp a) (numberp b) (<= a b))
	      (funcall -c- nil *empty-wme*))))

;;;
;;;Retrieval method for =.
;;;
;;;(= pattern1 pattern2) calls its continuation with *empty-wme* if both
;;;pattern1 and pattern2 are numbers and pattern1 is equal to pattern2.
;;;
(define-ps-retrieval-method = (pat -c-)
  (let* ((1st (first (pattern-args pat)))
	       (2nd (second (pattern-args pat)))
	       (a (if (listp 1st) (eval 1st) 1st))
	       (b (if (listp 2nd) (eval 2nd) 2nd)))
	  (if (and (numberp a) (numberp b) (= a b))
	      (funcall -c- nil *empty-wme*))))

;;;
;;;Retrieval method for /=.
;;;
;;;(/= pattern1 pattern2) calls its continuation with *empty-wme* if both
;;;pattern1 and pattern2 are numbers and pattern1 is not equal to pattern2.
;;;
(define-ps-retrieval-method /= (pat -c-)
  (let* ((1st (first (pattern-args pat)))
	       (2nd (second (pattern-args pat)))
	       (a (if (listp 1st) (eval 1st) 1st))
	       (b (if (listp 2nd) (eval 2nd) 2nd)))
	  (if (and (numberp a) (numberp b) (/= a b))
	      (funcall -c- nil *empty-wme*))))

;;;
;;;Retrieval method for Between.
;;;
;;;(Between pattern1 pattern2 pattern3) calls its continuation with *empty-wme*
;;;if every patterns are numbers and pattern3 is greater or equal to pattern1
;;;and less or equal to pattern2.
;;;
(define-ps-retrieval-method Between (pat -c-)
  (let* ((1st (first (pattern-args pat)))
	       (2nd (second (pattern-args pat)))
	       (3rd (third (pattern-args pat)))
	       (a (if (listp 1st) (eval 1st) 1st))
	       (b (if (listp 2nd) (eval 2nd) 2nd))
	       (c (if (listp 3rd) (eval 3rd) 3rd)))
	  (if (and (numberp a) (numberp b) (numberp c) (and (>= a b) (<= a c)))
	      (funcall -c- nil *empty-wme*))))

;(disable-reader-macros)
