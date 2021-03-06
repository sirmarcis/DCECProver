;;; Written by: Anders Maraviglia
;;; MAIN FUNCTION: prove-dcec
;;; NOTE: Function main was meant to be used as the entry point for a build image,
;;; and uses command line arguments intrinsically, do not use if working in a lisp
;;; enviormnent.

(in-package :shadowprover)

(defparameter *test-input-1* "Prototypes:
typedef Function Object
typedef Set Object
Boolean w Object
Boolean BigV Set Function
Boolean isMember Object Set

Axioms:
exists([Object x] implies(BigV(s,w_obj),and(isMember(x,s),w(x))))
BigV(s w_obj)

Conclusion:
exists([Object x] w(x))")

(defparameter *test-input-2* "Prototypes:
typedef Function Object
typedef Set Object
Boolean w Object
Boolean not_w Object
Boolean Most Set Function
Boolean BigA Set Function
Boolean isMember Object Set

Axioms:
forAll([Object x],isMember(x,s))
Most(s,not_w_obj)
forAll([Object x],implies(Most(s,not_w_obj),BigA(s,not_w_obj)))
forAll([Object x],implies(BigA(s,not_w_obj),implies(isMember(x,s),not_w(x))))


Conclusion:
forAll([Object x],implies(isMember(x,s),not_w(x)))")

(defparameter *opts* '(("o" :required)
                       ("h" :none)))

(defvar *dy-sig* NIL)

(defvar *f-to-s-hash* NIL)
(setf *f-to-s-hash* (make-hash-table :size 10 :test #'equal :rehash-size 2))
(setf (gethash "Object" *f-to-s-hash*) "obj")
(setf (gethash "Agent" *f-to-s-hash*) "agent")
(setf (gethash "Action" *f-to-s-hash*) "action")
(setf (gethash "Common" *f-to-s-hash*) "C")
(setf (gethash "Fluent" *f-to-s-hash*) "fluent")
(setf (gethash "Moment" *f-to-s-hash*) "moment")
(setf (gethash "Boolean" *f-to-s-hash*) "boolean")
(setf (gethash "C" *f-to-s-hash*) "common")
(setf (gethash "K" *f-to-s-hash*) "Knows")


(defvar *axiom-delimiter-hash* NIL)
(setf *axiom-delimiter-hash* (make-hash-table :size 10 :test #'equal :rehash-size 2))
(setf (gethash #\( *axiom-delimiter-hash*) T)
(setf (gethash #\) *axiom-delimiter-hash*) T)
(setf (gethash #\, *axiom-delimiter-hash*) T)
(setf (gethash #\Space *axiom-delimiter-hash*) T)
(setf (gethash #\[ *axiom-delimiter-hash*) T)
(setf (gethash #\] *axiom-delimiter-hash*) T)

(defun space-tokenize (input-str)
  "called by parse-prototype-line, very simple word space tokenizer"
  (let*((output-list NIL)
	(output-arr NIL)
	(curr-word "")
	(word-start-pos 0))
    (dotimes (char-elt (length input-str))
      (when (equalp (aref input-str char-elt) #\Space);; loop over string, stopping on spaces
	(setf curr-word (subseq input-str word-start-pos char-elt))
	(setf output-list (append (list curr-word) output-list))
	(setf word-start-pos (+ char-elt 1))))
    (setf curr-word (subseq input-str word-start-pos))
    (setf output-list (append (list curr-word) output-list))
    (setf output-arr (make-array (length output-list) :initial-contents (reverse output-list)))
    output-arr))

(defun parse-prototype-line (curr-line special-fun-names-hash all-fun-hash)
  "called by parse-input-str to parse a single line that contains prototype data, returning a list"
  (let*((input-prototype-arr (space-tokenize curr-line))
	(output-prototype-arr NIL))
    (if (equalp (aref input-prototype-arr 0) "typedef") ;; typedef case
	(progn
	  (setf (gethash (aref input-prototype-arr 1) *f-to-s-hash*)
		(gethash (aref input-prototype-arr 2) *f-to-s-hash*)) ;; map an object subtype to its s recognisable supertype
	  (return-from parse-prototype-line))
	(progn ;; must define either a variable or a function (mostly the latter here)
	  (if (find-symbol (string-upcase (aref input-prototype-arr 1)) 'snark-lisp)
	      (progn
		(setf (gethash (string-upcase (aref input-prototype-arr 1)) special-fun-names-hash)
		      (intern (format NIL "~a!" (string-upcase (aref input-prototype-arr 1)))))
		(setf output-prototype-arr (append output-prototype-arr
						   (list (intern (format NIL "~a!" (string-upcase (aref input-prototype-arr 1))))))))
	      (progn
		(setf (gethash (string-upcase (aref input-prototype-arr 1)) special-fun-names-hash)
		      (intern (string-upcase (aref input-prototype-arr 1))))
		(setf output-prototype-arr (append output-prototype-arr
						 (list (intern (string-upcase (aref input-prototype-arr 1)))))))) ;; map name
	  (setf output-prototype-arr (append output-prototype-arr
		(list (intern (string-upcase (gethash (aref input-prototype-arr 0) *f-to-s-hash*)))))) ;; map output
	  (let*((inputs-list NIL)) ;; map one or more inputs to a single list
	    (dotimes (char-elt (- (length input-prototype-arr) 2))
	      (setf inputs-list
		    (append
		     (list
		      (intern (string-upcase (gethash (aref input-prototype-arr (+ char-elt 2)) *f-to-s-hash*))))
		     inputs-list))) ;; map f inputs to s recognisable names
	    (setf (gethash (intern (string-upcase (first output-prototype-arr))) all-fun-hash) (reverse inputs-list))
	    (if (> (length inputs-list) 1)
		(setf output-prototype-arr (append output-prototype-arr (list (reverse inputs-list))))
		(setf output-prototype-arr (append output-prototype-arr (reverse inputs-list)))))))
    output-prototype-arr))

(defun get-var-type (curr-var all-fun-hash curr-depth list-depth-hash proto-var-hash local-var-p)
  (let*((curr-s-exp (gethash curr-depth list-depth-hash))
	(var-index (- (length curr-s-exp) 1))
	(new-proto-entry NIL)
	(curr-var-symbol (intern (string-upcase curr-var)))
	)
    (if local-var-p
	(let*((depth-reverse (- curr-depth 1)))
	  (dotimes (depth-elt curr-depth)
	    (setf depth-reverse (- depth-reverse 1))
	    (when (or (equalp (first (gethash depth-reverse list-depth-hash)) 'FORALL) (equalp (first (gethash depth-reverse list-depth-hash)) 'EXISTS))
	      (dolist (var-dec-list (second (gethash depth-reverse list-depth-hash)))
		(when (and (equalp (first var-dec-list) curr-var-symbol) (nth var-index (gethash (first curr-s-exp) all-fun-hash)))
		  (setf (second var-dec-list) (nth var-index (gethash (first curr-s-exp) all-fun-hash)))
		  ))
	      (return-from get-var-type))))
	(unless (gethash curr-var-symbol proto-var-hash) ;;only add for unique variables
	  (if (nth var-index (gethash (first curr-s-exp) all-fun-hash))
	      (setf new-proto-entry (list curr-var-symbol (nth var-index (gethash (first curr-s-exp) all-fun-hash)) NIL))
	      (setf new-proto-entry (list curr-var-symbol 'OBJ NIL)))
	  (setf (gethash curr-var-symbol proto-var-hash) new-proto-entry)
	  ))
    ))

(defun forall-case (line-str forall-var-hash)
  (let*((curr-var-str "")
	(curr-obj-str "Object")
	(var-start-pos 0)
	(var-list NIL))
    (dotimes (char-elt (length line-str))
      (when (gethash (aref line-str char-elt) *axiom-delimiter-hash*)
	(setf curr-var-str (subseq line-str  var-start-pos char-elt))
	(setf var-start-pos (+ char-elt 1))
	(if (or (equalp (aref line-str char-elt) #\,) (equalp (aref line-str char-elt) #\]))
	    (unless (equalp curr-var-str "")
	      (setf (gethash curr-var-str forall-var-hash) T)
	      (if (equalp curr-obj-str "")
		  (setf var-list (append var-list (list (intern (string-upcase (format NIL "?~A" curr-var-str)))
							 )))
		  (setf var-list (append var-list (list (list
							 (intern (string-upcase (format NIL "?~A" curr-var-str)))
							 (intern (string-upcase (gethash curr-obj-str *f-to-s-hash*))))))))
	      (setf curr-obj-str "Object"))
	    (unless (equalp curr-var-str "")
	      (setf curr-obj-str curr-var-str)))))
    var-list))

(defun add-statement-to-s-exp (curr-statement curr-depth list-depth-hash)
  (setf (gethash curr-depth list-depth-hash)
	(append (gethash curr-depth list-depth-hash)
		(list curr-statement))))

(defun new-s-exp-case (curr-statement special-fun-names-hash curr-depth list-depth-hash forall-p char-elt)
  "called by parse-axioms-line"
  (if (gethash (string-upcase curr-statement) special-fun-names-hash)
      (add-statement-to-s-exp (list (gethash (string-upcase curr-statement) special-fun-names-hash)) curr-depth list-depth-hash)
      (if (gethash curr-statement *f-to-s-hash*)
	  (add-statement-to-s-exp (list (intern (string-upcase (gethash curr-statement *f-to-s-hash*)))) curr-depth list-depth-hash)
	  (add-statement-to-s-exp (list (intern (string-upcase curr-statement))) curr-depth list-depth-hash)))
  (setf (gethash (+ curr-depth 1) list-depth-hash)
	(first (last (gethash curr-depth list-depth-hash))))
  (when (equalp (string-upcase curr-statement) "FORALL")
    (setf forall-p char-elt))
  (incf curr-depth)
  (list curr-depth forall-p))

(defun end-s-exp-case (curr-statement curr-depth list-depth-hash forall-var-hash all-fun-hash proto-var-hash)
  "called by parse-axioms-line"
  (unless (equalp curr-statement "")
    (if (gethash curr-statement forall-var-hash)
	(if (find-symbol (string-upcase (first (gethash curr-depth list-depth-hash))) 'snark-lisp)
	    (progn
	      (add-statement-to-s-exp (list (intern "HOLDS!") (intern (string-upcase (format NIL "?~a" curr-statement)))) curr-depth list-depth-hash)
	      )
	    (progn
	      (get-var-type (format NIL "?~a" curr-statement) all-fun-hash curr-depth list-depth-hash proto-var-hash T)
	      (add-statement-to-s-exp (intern (string-upcase (format NIL "?~a" curr-statement))) curr-depth list-depth-hash)
	      ))
	(progn
	  (get-var-type curr-statement all-fun-hash curr-depth list-depth-hash proto-var-hash NIL)
	  (add-statement-to-s-exp (intern (string-upcase curr-statement)) curr-depth list-depth-hash)
	  )))
  (setf (first (last (gethash (- curr-depth 1) list-depth-hash)))
	(gethash curr-depth list-depth-hash)) ;; tie back tree to level above
  (setf curr-depth (- curr-depth 1))
  curr-depth)

(defun end-var-dec-case (curr-statement curr-depth list-depth-hash forall-var-hash var-dec-str char-elt curr-line forall-p)
  "called by parse-axioms-line"
  (if forall-p
      (add-statement-to-s-exp (forall-case (subseq curr-line forall-p (+ char-elt 1)) forall-var-hash ) curr-depth list-depth-hash)
      (add-statement-to-s-exp (list (intern (string-upcase (format NIL "?~a" curr-statement))) (intern (string-upcase var-dec-str))) curr-depth list-depth-hash)
      ))

(defun simple-var-case (curr-statement forall-var-hash curr-depth list-depth-hash all-fun-hash proto-var-hash)
  (if (gethash curr-statement forall-var-hash)
      (progn
	(get-var-type (format NIL "?~a" curr-statement) all-fun-hash curr-depth list-depth-hash proto-var-hash T)
	(if (find-symbol (string-upcase (first (gethash curr-depth list-depth-hash))) 'snark-lisp)
	    (add-statement-to-s-exp (list (intern "HOLDS!") (intern (string-upcase (format NIL "?~a" curr-statement)))) curr-depth list-depth-hash)
	    (add-statement-to-s-exp (intern (string-upcase (format NIL "?~a" curr-statement))) curr-depth list-depth-hash)
	    ))
      (progn
	(get-var-type curr-statement all-fun-hash curr-depth list-depth-hash proto-var-hash NIL)
	(add-statement-to-s-exp (intern (string-upcase curr-statement)) curr-depth list-depth-hash)
	)))

(defun parse-axioms-line (curr-line special-fun-names-hash all-fun-hash proto-var-hash)
  "called by parse-input-str to read and translate a line of axioms by building a list tree, where the depth lists are kept track of in a hash table whose keys are list depth"
  (let*((curr-statement "")
	(stat-pos 0)
	(var-dec-str "")
	(forall-p NIL)
	(forall-var-hash (make-hash-table :size 5 :test #'equalp :rehash-size 2))
	(get-s-exp-str NIL)
	(list-depth-hash (make-hash-table :size 20 :test #'equal :rehash-size 2))
	(curr-depth 0))
    (dotimes (char-elt (length curr-line)) ;; loop over every char in line
      (when (gethash (aref curr-line char-elt) *axiom-delimiter-hash*)
	(setf curr-statement (subseq curr-line stat-pos char-elt))
	(when (and get-s-exp-str (equalp var-dec-str ""))
	  (setf var-dec-str (gethash curr-statement *f-to-s-hash*)))
	(if (equalp (aref curr-line char-elt) #\() ;; branch tree when open paren
	    (let*((new-s-list (new-s-exp-case curr-statement special-fun-names-hash curr-depth list-depth-hash forall-p char-elt)))
	      (setf curr-depth (first new-s-list))
	      (setf forall-p (second new-s-list)))
	    (if (equalp (aref curr-line char-elt) #\[)
		(progn
		  (setf forall-p char-elt)
		  (setf get-s-exp-str T))
		(if (equalp (aref curr-line char-elt) #\));; go back when close paren
		    (setf curr-depth (end-s-exp-case curr-statement curr-depth list-depth-hash forall-var-hash all-fun-hash proto-var-hash))
		    (if (equalp (aref curr-line char-elt) #\])
			(progn
			  (end-var-dec-case curr-statement curr-depth list-depth-hash forall-var-hash var-dec-str char-elt curr-line forall-p)
			  (setf var-dec-str "")
			  (setf get-s-exp-str NIL) )
			(unless (or (equalp curr-statement  "") get-s-exp-str)
			  (simple-var-case curr-statement forall-var-hash curr-depth list-depth-hash all-fun-hash proto-var-hash))))))
	(setf stat-pos (+ char-elt 1))))
    (first (gethash 0 list-depth-hash))))

(defun add-new-prototypes (proto-var-hash prototype-arr-list)
  (loop for value being the hash-values of proto-var-hash
       do (setf prototype-arr-list (append prototype-arr-list (list value))))
  prototype-arr-list)

(defun parse-input-str (input-str)
  "called by prove-dcec, does all the translation from f to s expressions from input-str and finds prototypes, axioms, and conclusions and puts it in shadowprover readable data structures"
  (let*((curr-line "")
	(line-pos 0)
	(prototypes-p NIL)
	(axioms-p NIL)
	(conclusions-p NIL)
	(curr-prototype NIL)
	(prototype-arr-list NIL)
	(break-char-list '(#\Space #\linefeed))
	(special-fun-names-hash (make-hash-table :size 5 :test #'equalp :rehash-size 2))
	(all-fun-hash (make-hash-table :size 5 :test #'equalp :rehash-size 2))
	(proto-var-hash (make-hash-table :size 5 :test #'equalp :rehash-size 2))
	(axiom-list NIL)
	(conclusion-list NIL))
    (dotimes (char-elt (length input-str))
      (when (or (equalp (aref input-str char-elt) #\linefeed) (equalp (aref input-str char-elt) #\#)) ;; for every line
	(when (< line-pos char-elt)
	  (setf curr-line (string-trim break-char-list (subseq input-str line-pos char-elt)))
	 
	  (if (string=  curr-line "Prototypes:") ;; begin looking for prototypes
	      (setf prototypes-p T)
	      (if (string= curr-line "Axioms:") ;; begin looking for axioms
		  (progn
		    (setf prototypes-p NIL)
		    (setf axioms-p T))
		  (if (string= curr-line "Conclusion:") ;; begin looking for conclusion
		      (progn
			(setf axioms-p NIL)
			(setf conclusions-p T))
		      (progn ;; found one of the three types
			(when (and prototypes-p (> (length curr-line) 0))
			  (setf curr-prototype (parse-prototype-line curr-line special-fun-names-hash all-fun-hash))
			  (when curr-prototype
			    (setf prototype-arr-list (append prototype-arr-list (list curr-prototype)))))
			(when (and axioms-p (> (length curr-line) 0))
			  (setf axiom-list (append axiom-list (list (parse-axioms-line curr-line special-fun-names-hash all-fun-hash proto-var-hash)))))
			(when (and conclusions-p (> (length curr-line) 0))
			  (setf conclusion-list (append (list (parse-axioms-line curr-line special-fun-names-hash all-fun-hash proto-var-hash)) conclusion-list)))))))
	  (setf line-pos (+ char-elt 1)))))
    (setf curr-line (subseq input-str line-pos))  ;; last line edge case
    (when (and conclusions-p (> (length (string-trim break-char-list curr-line)) 0)) ;; to find conclusion
      (setf conclusion-list (append (list (parse-axioms-line curr-line special-fun-names-hash all-fun-hash proto-var-hash)) conclusion-list)))
    (setf prototype-arr-list (add-new-prototypes proto-var-hash prototype-arr-list))
    (list prototype-arr-list axiom-list conclusion-list)))
;;(parse-input-str *test-input-1*)

(defun prove-dcec (input-str &key debug)
  "called by main, calls parse-input-str to format data to run through shadowprover"
  (let*((snark-response NIL))
    (destructuring-bind (prototype-arr-list axiom-list conclusion-list) (parse-input-str input-str)
      (setf prototype-arr-list (append (list '(holds! boolean obj)) prototype-arr-list))
      (when debug ;; debugging messages
	(format t "prototype-arr-list[~w]~%" prototype-arr-list)
	(format t "axiom-list:~%" )
	(pprint axiom-list)
	(format t "~%conclusion-list[~w]~%" conclusion-list))
      (setf snark-response (prove axiom-list (first conclusion-list) :signature prototype-arr-list))
      (pprint snark-response)
      (format t "~%"))))
;;(prove-dcec *test-input-2*)

(defun get-file-contents-str (file-name)
  "simple function to get the contents of a text file"
  (let*((output-str "")
	(in (open file-name :if-does-not-exist nil)))
    (when in
      (loop for line = (read-line in nil)
         while line do (setf output-str (format NIL "~a~a~%" output-str line)))
      (close in))
    output-str)) ;; returns an empty string of file does not exist

(defun main ()
  "built to be run as the main function for an image, relies on command line arguments"
  (let*((argv (subseq sb-ext:*posix-argv* 1))
	(input-str ""))
    (multiple-value-bind (args opts)
        (getopt:getopt argv *opts*)
      (unless (car argv)
        (format t "bad args[~w]~%" opts))
      (when (> (length argv) 2)
	  (when (equalp (third argv) "--file")
	    (setf input-str (get-file-contents-str (first argv)))
	    (when (equalp input-str "")
	      (format t "Error: file[~a] does not exist!~%" (first argv))
	      (return-from main))))
      (if (> (length argv) 1)
	  (if (equalp (second argv) "-f")
	      (if (equalp input-str "")
		  (prove-dcec (first args)) ;; truth case
		  (prove-dcec input-str)) ;; false case
	      (if (equalp (second argv) "-s")
		  (progn ;; use read-from-string
		    (format t "not currently implimented~%")
		    )
		  (format t "usage: ./shadowprover-<OSType> <input> [-f or -s] [--file]~%")))))))
