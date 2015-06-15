(defparameter *ql-modules*
  (list "fiveam" "optima" "gtfl"))

(mapcar #'quicklisp:quickload *ql-modules*)

(load (format NIL "~asnark-20120808r022/snark-system.lisp" *default-pathname-defaults*))
(make-snark-system)
(let*((reg-pathname (make-pathname :directory (pathname-directory *load-truename*)))
      (path-present NIL))
  (dolist (pathname asdf:*central-registry*)
    (when (equalp pathname reg-pathname)
      (setf path-present T)))
  (unless path-present
    (push (make-pathname :directory (pathname-directory *load-truename*)) asdf:*central-registry*)))
(quicklisp:quickload "getopt")

(asdf:defsystem :shadowprover
  :serial t
  :description "A prover for DCEC, a first-order modal logic."
  :author "Naveen Sundar G."
  :license "MIT BSD"
  :depends-on (#:optima #:fiveam #:gtfl)
  :components ((:file "package")
               (:file "configs")
               (:file "params")
               (:file "./snark-20120808r022/snark-interface")
               (:file "./utils/misc")
               (:file "./utils/syntax")
               (:file "./utils/sorts")
               
               (:file "./inference-rules/expanders")
               (:file "./inference-rules/backward-rules")
               (:file "./inference-rules/folrules")
               (:file "./inference-rules/primitiverules")
               (:file "./inference-rules/derivedrules")

               (:file "./utils/show")
               
               (:file "ShadowProver")
	       (:file "converter")
               (:file "./tests/dev-tests")
               (:file "./projects/akrasia/akrasia")
               (:file "./projects/false-belief-task/false-belief-task")
               (:file "./projects/wise-men-puzzle/wise-men-puzzle")
               (:file "./projects/knights-and-knaves/knights-and-knaves")
               (:file "./tests/all-tests")))

(asdf:load-system :shadowprover)
