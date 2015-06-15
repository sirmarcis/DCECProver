(in-package :shadowprover)

(declare-signature
 *lottery-paradox-1*
 (:name w :output boolean :inputs object)
 (:name BigV :output boolean :inputs (object object))
 (:name isMember :output boolean :inputs (object object)))

(defparameter *A1*
  '(exists (?x object)
    (implies (BigV s w_obj)
     (and (isMember x s) (w x)))))

(defparameter *A2*
  '(BigV s w_obj))

(defun prove-lottery-paradox ()
  (prove (list *A1* *A2*)
	 '(exists (?x object) (w x))))
