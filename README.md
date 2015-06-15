## Theory

![alt text](http://www.naveensundarg.com/images/shadow.png "shadow")

## Algorithm Sketch

Every atomic modal formula **m** is assigned a _unique propositional_
   variable **s**: We call **s** the *propositional shadow of* **m**. For any
   formula *f[* **m**,..*]*, the corresponding formula *f[* **s**,..*]*, with all atomic
   modal formulae replaced by their propositional shadows,  is called
   the shadow of *f[* **m**,..*]*.
			 
* **Step 1**: The prover first replaces all occurrences of atomic
             modal formulae by propositional variables (even nested
             occurrences).  Now we have a first-order problem.

* **Step 2**:  Call a first-order prover on this first-order problem.

* **Step 3**: If the first-order prover fails, we expand the premises with
 any legal modal rule (via forward reasoning natural deduction) and
 repeat the process from **Step 1**. If the prover succeeds, we return
 true.

See Usage example below to see how to run binary executable, where the argument string should be of 
this format:
"Prototypes:
[prototypes]
Axioms:
[axioms]
Conclusion:
[conclusion]"

or can specify a file with the necessary inputst in it. Usage of this is as follows:
./shadowprover.exe [file-name] -f
or
./shadowprover.exe [file-name] --file

TO COMPILE FROM REPL: 
(load (format NIL "~aloader.lisp" (namestring *default-pathname-defaults*)))

ENTRY POINT: (prove [list of Axioms] [list of conclusions])

To run the converter, make sure converter.lisp (found under the main directory) is loaded, and you
are working in package :shadowprover by running (in-package :shadowprover).  
Then run (prove-dcec [input-string]) where [input string] is the inputs as you would provide them 
to the DCEC.

TO BUILD IMAGE:
open sbcl in terminal and run following commands:
(load (format NIL "~aloader.lisp" (namestring *default-pathname-defaults*)))
(sb-ext:save-lisp-and-die "shadowprover.exe" :toplevel #'shadowprover:main :executable t)

usage example:
./shadowprover.exe "Prototypes:
typedef Function Object
typedef Set Object
Boolean w Object
Boolean BigV Set Function
Boolean isMember Object Set

Axioms:
exists([Object x] implies(BigV(s,w_obj),and(isMember(x,s),w(x))))
BigV(s w_obj)

Conclusion:
exists([Object x] w(x))"