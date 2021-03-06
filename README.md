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

## Dependencies 

* SBCL: if you are on linux, just run the command: `sudo apt-get install sbcl`, or if not look at their 
website: http://www.sbcl.org/platform-table.html

* Quicklisp: Follow the instructions on their website to install.


## Running The Prover

To run Shadowprover using the standard DCEC input format, simply run the following command wherever
you put the binary file:
`./shadowprover-<OS type> <input prototypes, axioms, and conclusion> <[-f] or [-s]>`

The argument string should be in this format, see the usage example for more details:
"Prototypes:
[prototypes]
Axioms:
[axioms]
Conclusion:
[conclusion]"

[-f] specifies to recognize the input as being in f notation, whereas [-s] specifies to 
recognize the input as s notation.

You also can specify a file with the necessary inputs in it. Usage of this is as follows:
`./shadowprover-<OS type> <file-name> <[-f] or [-s]> --file`


## Usage Notes

* TO COMPILE FROM REPL: 
Open an sbcl instance within the main DCECProver directory and run the command:
`(load (format NIL "~aloader.lisp" (namestring *default-pathname-defaults*)))`

* TO RUN WITHIN LISP:
To run the converter from within an sbcl instance, make sure converter.lisp (found under the main 
directory) is loaded, and you are working in package :shadowprover by running `(in-package :shadowprover)`.  
Then run `(prove-dcec [input-string])` where [input string] is the input as you would provide them 
to the DCEC or the binary executable.

* TO BUILD AN IMAGE:
Open sbcl in terminal and run following commands:
`(load (format NIL "~aloader.lisp" (namestring *default-pathname-defaults*)))`
`(sb-ext:save-lisp-and-die "shadowprover-linux" :toplevel #'shadowprover:main :executable t)`

* The entry point function within shadowprover is: (prove [list of Axioms] [list of conclusions])

* Right now, there are only linux and mac binary executables, with windows not being supported.

* Usage example:

./shadowprover-<OS type> "Prototypes:
typedef Function Object
typedef Set Object
Boolean w Object
Boolean BigV Set Function
Boolean isMember Object Set

Axioms:
exists([Object x] implies(BigV(s,w_obj),and(isMember(x,s),w(x))))
BigV(s w_obj)

Conclusion:
exists([Object x] w(x))" -f

## On Snark...

While woring with Shadowprover, it may become necessary to understand the groundword on which
it is built, i.e., Snark.  If so, the link to the Snark user guide is below, godspeed:

http://www.ai.sri.com/snark/tutorial/tutorial.html