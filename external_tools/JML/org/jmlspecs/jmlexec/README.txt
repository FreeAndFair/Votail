OVERVIEW:

  jmle executes JML specifications by translating them to constraint programs,
 which are then executed by the Java Constraint Kit (JCK).  The distribution
 includes a modified version of JCK, so installing and using JCK should be
 (relatively) transparent.

  If you have any suggestions or questions, please feel free to contact me
 (Tim Wahls - wahlst@dickinson.edu).

USAGE:

  To compile the JML specification contained (for example) in file Test.jml,
 execute:

     jmle Test.jml

 This first runs the JML checker, which reports any syntax errors in the
 specification.  Next, jmle reports any constructs which can not be executed.
 If compilation is successful, jmle creates Java bytecode (i.e. Test.class).
 In general, many .class files will be created (corresponding to nested
 classes created by jmle).

  To run the specification, write standard Java driver code (i.e. code that
 creates instances of the specified class and calls it's methods, or JUnit
 tests for the specified class), and compile and run it as usual (using
 javac and java).  Note that you must have $HOME/JML2 in your CLASSPATH
 for this to work (or use the jmlre script, which just runs java with the
 appropriate classpath settings).

  If your specification is divided into multiple files, you must specify
 all of them on the command line to jmle (even if the specified classes are
 related by inheritance), or compile them in order (parent or used class
 specification first, then subclass or client class specification).
 However, if your specification contains a refinement chain, only the file in
 that chain that you actually wish to execute should be specified.  Usually,
 this will be the last file in the chain, but it need not be.

EXAMPLES

  The samples directory contains three example specifications: IntList.jml
 (specifying a simple list of integers with a sort method), Graph.jml
 (undirected graphs with a clique method), and Digraph.jml (and associated
 files NodeType.java, Node.jml and ArcType.jml).  The Digraph specification
 is adapted from the org.jmlspecs.samples.digraph package.  Driver code for
 these specifications is in the files TestIntList.java, TestGraph.java and
 TestDigraph.java, respectively.  All of the samples can be compiled using
 the included Makefile by typing:

make buildsamples

 and run by typing:

make run

 To compile and run the IntList example individually:

 jmle IntList.jml
 javac TestIntList.java
 jmlre org.jmlspecs.jmlexec.samples.TestIntList

 Running the Graph example is similar.

 To compile and run the Digraph example:

 jmle Digraph.jml ArcType.jml NodeType.java Node.jml
 javac TestDigraph.java
 jmlre org.jmlspecs.jmlexec.samples.TestDigraph

 (Note: this example takes a long time to run.)

ADDITIONAL USAGE NOTES

 - jmle ignores ignores code in the bodies of methods (if you want to check
   code, you should be using the runtime assertion checker).  However, if
   you are specifying a nonabstract class in a .java file, you must put 
   stub code in the bodies of methods (i.e. to return some value of the
   return type) to satisfy the checker.

 - if you wish to see the Java Constraint Kit (JCK) constraint store
   and rewriting rule used at each step in constraint simplification,
   compile your specification(s) using the -c flag to jmle.  This is
   useful for debugging and generally for seeing how jmle works.

 - specifications that use the "Object" versions (JMLObjectSequence,
   JMLObjectSet, ...) of the JMLCollection classes are more likely to
   be executed successfully.  This results from the fact that s.has(elem)
   (for example) is a much stronger constraint if s is a JMLObjectSet
   rather than a JMLValueSet or JMLEqualsSet

 - for similar reasons, specifications that use == to compare objects 
   are more likely to be executed successfully that specifications that
   use .equals

 - of the built-in JML types, only the classes that implement the
   JMLCollection interface are treated as constraint domains.  
   Specifications that use other built-in JML types can be executed,
   but (for example) calls to methods of these classes in specifications
   will only be executed when all of the parameters to the method call
   (and the calling object) are ground.  Also, specifications that inherit
   from specifications of the built-in JML types (except JMLType) currently
   receive no special "constraint" support.

NOT YET IMPLEMENTED
  
  Use of the following JML constructs may result in a warning or error at 
 compile time, an error when the JCK program is compiled, or the construct
 may simply be ignored.

 model programs (but model methods are supported)
 \reach
 axioms
 \max
 \for_example
 universally quantified assertions where the domain of the bound variable
   is not explicitly given
 many specifications over types double and float, i.e. 
  \exists float f; f >= 3.1415 && f < 10.28;  f != 5.555
  (anything that would require solving nontrivial real constraints)
 set statements (for ghost variables) - since they are not part of
  specifications

MANIFEST

  README.txt                              this file
  ExecPrettyPrinter.java                  compiles JML specifications to JCK
                                          programs
  Main.java                               runs the compiler
  ExecOptions.opt                         command-line options
  ExecMessages.msg                        error messages and warnings
  Makefile
  jack                                    contains the (modified) source
                                          for the Java Constraint Kit (JCK)
  constraints                             contains JCK rewriting rules
                                          for the JML solvers
  runtime                                 contains library code called from
                                          executable specifications
  environment                             additional library code used
                                          at runtime
  samples                                 contains the examples mentioned
                                          above
  testcase                                contains the test specifications and
                                          JUnit test cases

REFERENCES

B. Krause and T. Wahls.  "jmle: A tool for Executing JML Specifications via
Constraint Programming".  In L. Brim, editor, Formal Methods for Industrial
Critical Systems (FMICS '06), volume 4345 of Lecture Notes in Computer Science,
pages 293 - 296.  Springer-Verlag, 2006.
http://users.dickinson.edu/~wahlst/papers/tool.pdf
