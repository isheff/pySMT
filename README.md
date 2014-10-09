pySMT
=====

A script to convert a small subset of SMT and Z3's extensions thereof to QF_BV, and run analysis for Heterogeneous Fast Consensus

=====

Pysmt: your friend when converting z3 SMT2 extensions and such to QF_BV
    If you have define-sort or declare-datatypes with no arguments, this may
    help you.
    Likewise, if you have functions with only BitVec or Boolean (or declared
    or defined datatypes) as inputs, this may help you.
    If you meet the above requirements, this may be able to convert your smt2
    file into a QF_BV smt2 file. It will unroll all quantifiers, replace all
    declared datatypes and defined sorts with what you defined them to be,
    replace all boolean function inputs with single bit bitvectors, (and fix
    any usage appropriately), and convert all declared functions to lookup
    tables, allowing the system to solve for the values in the tables. 
    all tags are optional, save for the input file. It will generate output
    files in /tmp/ unless you give it an alternative.

    The resulting QF_BV input to your solver will be expanded by a constant
    factor in the overall length of your file times a constant factor of the
    length of your BitVecs. (Since BitVecs can be declared in a file of size
    logarithmic in their length, this is technically exponential expansion of
    the file.)

    you must supply an input file name as an argument
    
    -help or -h: brings up this dialogue 

    -QF_BV or -q: the filename to which to write the converted QF_BV version

    -solver or -s: the solver to apply to the result (NONE means don't solve)
                   default: z3

    -model or -m: the filename to which to write the solver's output

    -analysis or -a: if this tag is present, we execute analysis specific to 
                     Isaac's research. The remaining tags pertain to this.

    -html or -w: the html file to be opened in firefox and viewed.

    -iterative-optimize or -i: after solver has finished, try switching every
                               response that doesn't meet each threshold to 
                               meeting that threshold, one by one, testing
                               whether this violates the requirements, until
                               you either get one that works, and then start 
                               over, or get through all the response-threshold
                               pairs. In theory, this has the same basic effect
                               as -localmax, but it's slower, and less likely
                               to run out of memory and crash.

    -localmax or -l: requires from the solver that this set of thresholds is
                     locally maximal, which is to say that there there is no 
                     one set of possible responses which presently does not 
                     meet a threshold which can be made to meet that threshold
                     without violating a requirement.
                     DANGER: this option makes z3 (I don't know about other
                             solvers) take MUCH longer.
