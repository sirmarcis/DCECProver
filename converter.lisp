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
(setf (gethash "Object" *f-to-s-hash*) "object")
(setf (gethash "Agent" *f-to-s-hash*) "agent")
(setf (gethash "Common" *f-to-s-hash*) "C")
(setf (gethash "Fluent" *f-to-s-hash*) "fluent")
(setf (gethash "Moment" *f-to-s-hash*) "moment")


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

(defun parse-prototype-line (curr-line)
  "called by parse-input-str to parse a single line that contains prototype data, returning a list"
  (let*((input-prototype-arr (space-tokenize curr-line))
	(output-prototype-arr NIL))
    (if (equalp (aref input-prototype-arr 0) "typedef") ;; typedef case
	(progn
	  (setf (gethash (aref input-prototype-arr 1) *f-to-s-hash*)
		(gethash (aref input-prototype-arr 2) *f-to-s-hash*)) ;; map an object subtype to its s recognisable supertype
	  (return-from parse-prototype-line))
	(progn ;; return type case
	  (setf output-prototype-arr (append output-prototype-arr
		(list (intern (string-upcase (aref input-prototype-arr 1)))))) ;; map name
	  (setf output-prototype-arr (append output-prototype-arr
		(list (intern (string-upcase (aref input-prototype-arr 0)))))) ;; map output
	  (let*((inputs-list NIL)) ;; map one or more inputs to a single list
	    (dotimes (char-elt (- (length input-prototype-arr) 2))
	      (setf inputs-list
		    (append
		     (list
		      (intern (string-upcase (gethash (aref input-prototype-arr (+ char-elt 2)) *f-to-s-hash*))))
		     inputs-list))) ;; map f inputs to s recognisable names
	    (if (> (length inputs-list) 1)
		(setf output-prototype-arr (append output-prototype-arr (list (reverse inputs-list))))
		(setf output-prototype-arr (append output-prototype-arr (reverse inputs-list)))))))
    output-prototype-arr))

(defun parse-axioms-line (curr-line)
  "called by parse-input-str to read and translate a line of axioms by building a list tree, where the depth lists are kept track of in a hash table whose keys are list depth"
  (let*((curr-statement "")
	(stat-pos 0)
	(var-dec-str "")
	(get-s-exp-str NIL)
	(list-depth-hash (make-hash-table :size 20 :test #'equal :rehash-size 2))
	(curr-depth 0))
    (dotimes (char-elt (length curr-line)) ;; loop over every char in line
      (when (gethash (aref curr-line char-elt) *axiom-delimiter-hash*)
	(setf curr-statement (subseq curr-line stat-pos char-elt))
	(when (and get-s-exp-str (equalp var-dec-str ""))
	  (setf var-dec-str (gethash curr-statement *f-to-s-hash*)))
	(if (equalp (aref curr-line char-elt) #\() ;; branch tree when open paren
	    (progn
	      (setf (gethash curr-depth list-depth-hash)
		    (append (gethash curr-depth list-depth-hash)
			    (list (list (intern (string-upcase curr-statement))))))
	      (setf (gethash (+ curr-depth 1) list-depth-hash)
		    (first (last (gethash curr-depth list-depth-hash))))
	      (incf curr-depth))
	    (if (equalp (aref curr-line char-elt) #\[)
		(progn
		  (setf get-s-exp-str T))
		(if (equalp (aref curr-line char-elt) #\));; go back when close paren
		    (progn
		      (unless (equalp curr-statement "")
			(setf (gethash curr-depth list-depth-hash)
			      (append (gethash curr-depth list-depth-hash)
				      (list (intern (string-upcase curr-statement))))))
		      (setf (first (last (gethash (- curr-depth 1) list-depth-hash)))
			    (gethash curr-depth list-depth-hash)) ;; tie back tree to level above
		      (setf curr-depth (- curr-depth 1)))
		    (if (equalp (aref curr-line char-elt) #\])
			(progn
			  (setf (gethash curr-depth list-depth-hash)
				(append
				 (gethash curr-depth list-depth-hash)
				 (list (list (intern (string-upcase (format NIL "?~a" curr-statement))) (intern (string-upcase var-dec-str))))))
			  (setf var-dec-str "")
			  (setf get-s-exp-str NIL))
			(unless (or (equalp curr-statement  "") get-s-exp-str)
			  (setf (gethash curr-depth list-depth-hash)
				(append (gethash curr-depth list-depth-hash)
					(list (intern (string-upcase curr-statement))))))))))
	(setf stat-pos (+ char-elt 1))))
    (first (gethash 0 list-depth-hash))))

(defun parse-input-str (input-str)
  "called by prove-dcec, does all the translation from f to s expressions from input-str and finds prototypes, axioms, and conclusions and puts it in shadowprover readable data structures"
  (let*((curr-line "")
	(line-pos 0)
	(prototypes-p NIL)
	(axioms-p NIL)
	(conclusions-p NIL)
	(curr-prototype NIL)
	(prototype-arr-list NIL)
	(axiom-list NIL)
	(conclusion-list NIL))
    (dotimes (char-elt (length input-str))
      (when (equalp (aref input-str char-elt) #\linefeed) ;; for every line 
	(setf curr-line (subseq input-str line-pos char-elt))
	(if (string= curr-line "Prototypes:") ;; begin looking for prototypes
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
			(setf curr-prototype (parse-prototype-line curr-line))
			(when curr-prototype
			  (setf prototype-arr-list (append prototype-arr-list (list curr-prototype)))))
		      (when (and axioms-p (> (length curr-line) 0))
			(setf axiom-list (append axiom-list (list (parse-axioms-line curr-line)))))
		      (when (and conclusions-p (> (length curr-line) 0))
			(setf conclusion-list (append (list (parse-axioms-line curr-line)) conclusion-list))
			)))))
	(setf line-pos (+ char-elt 1))))
    (setf curr-line (subseq input-str line-pos))  ;; last line edge case
    (when (and conclusions-p (> (length curr-line) 0)) ;; to find conclusion
      (setf conclusion-list (append (list (parse-axioms-line curr-line)) conclusion-list)))
    (list prototype-arr-list axiom-list conclusion-list)))
;;(parse-input-str *test-input-1*)

(defun prove-dcec (input-str &key debug)
  "called by main, calls parse-input-str to format data to run through shadowprover"
  (destructuring-bind (prototype-arr-list axiom-list conclusion-list) (parse-input-str input-str)
    (setf *dy-sig* prototype-arr-list)
    (when debug ;; debugging messages
      (format t "prototype-arr-list[~w]~%" :prototype-arr-list)
      (format t "axiom-list[~w]~%" axiom-list)
      (format t "conclusion-list[~w]~%" conclusion-list))
    (pprint (prove axiom-list (first conclusion-list) :signature *dy-sig*))))
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
  "built to be run as the main function from an image, relies on command line arguments"
  (let*((argv (subseq sb-ext:*posix-argv* 1))
	(input-str ""))
    (multiple-value-bind (args opts)
        (getopt:getopt argv *opts*)
      (unless (car argv)
        (format t "bad args[~w]~%" opts))
      (if (> (length argv) 1)
	  (when (or (equalp (second argv) "-f") (equalp (second argv) "--file"))
	    (setf input-str (get-file-contents-str (first argv)))
	    (if (equalp input-str "")
		(format t "Error: file[~a] does not exist!~%" (first argv))
		(progn
		  (format t "file-contents[~a]~%" input-str)
		  (prove-dcec input-str))))
	  (progn
	    (prove-dcec (first args)))))))
