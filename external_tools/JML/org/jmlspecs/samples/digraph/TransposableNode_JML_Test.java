// This file was generated by jmlunit on Tue May 20 17:42:33 EDT 2008.

package org.jmlspecs.samples.digraph;

/** Automatically-generated test driver for JML and JUnit based
 * testing of TransposableNode. The superclass of this class should be edited
 * to supply test data. However it's best not to edit this class
 * directly; instead use the command
 * <pre>
 *  jmlunit TransposableNode.java
 * </pre>
 * to regenerate this class whenever TransposableNode.java changes.
 */
public class TransposableNode_JML_Test
     extends TransposableNode_JML_TestData
{
    /** Initialize this class. */
    public TransposableNode_JML_Test(java.lang.String name) {
        super(name);
    }

    /** Run the tests. */
    public static void main(java.lang.String[] args) {
        org.jmlspecs.jmlunit.JMLTestRunner.run(suite());
        // You can also use a JUnit test runner such as:
        // junit.textui.TestRunner.run(suite());
    }

    /** Test to see if the code for class TransposableNode
     * has been compiled with runtime assertion checking (i.e., by jmlc).
     * Code that is not compiled with jmlc would not make an effective test,
     * since no assertion checking would be done. */
    public void test$IsRACCompiled() {
        junit.framework.Assert.assertTrue("code for class TransposableNode"
                + " was not compiled with jmlc"
                + " so no assertions will be checked!",
            org.jmlspecs.jmlrac.runtime.JMLChecker.isRACCompiled(TransposableNode.class)
            );
    }

    /** Return the test suite for this test class.  This will have
    * added to it at least test$IsRACCompiled(), and any test methods
    * written explicitly by the user in the superclass.  It will also
    * have added test suites for each testing each method and
    * constructor.
    */
    //@ ensures \result != null;
    public static junit.framework.Test suite() {
        TransposableNode_JML_Test testobj
            = new TransposableNode_JML_Test("TransposableNode_JML_Test");
        junit.framework.TestSuite testsuite = testobj.overallTestSuite();
        // Add instances of Test found by the reflection mechanism.
        testsuite.addTestSuite(TransposableNode_JML_Test.class);
        testobj.addTestSuiteForEachMethod(testsuite);
        return testsuite;
    }

    /** A JUnit test object that can run a single test method.  This
     * is defined as a nested class solely for convenience; it can't
     * be defined once and for all because it must subclass its
     * enclosing class.
     */
    protected static abstract class OneTest extends TransposableNode_JML_Test {

        /** Initialize this test object. */
        public OneTest(String name) {
            super(name);
        }

        /** The result object that holds information about testing. */
        protected junit.framework.TestResult result;

        //@ also
        //@ requires result != null;
        public void run(junit.framework.TestResult result) {
            this.result = result;
            super.run(result);
        }

        /* Run a single test and decide whether the test was
         * successful, meaningless, or a failure.  This is the
         * Template Method pattern abstraction of the inner loop in a
         * JML/JUnit test. */
        public void runTest() throws java.lang.Throwable {
            try {
                // The call being tested!
                doCall();
            }
            catch (org.jmlspecs.jmlrac.runtime.JMLEntryPreconditionError e) {
                // meaningless test input
                addMeaningless();
            } catch (org.jmlspecs.jmlrac.runtime.JMLAssertionError e) {
                // test failure
                int l = org.jmlspecs.jmlrac.runtime.JMLChecker.getLevel();
                org.jmlspecs.jmlrac.runtime.JMLChecker.setLevel
                    (org.jmlspecs.jmlrac.runtime.JMLOption.NONE);
                try {
                    java.lang.String failmsg = this.failMessage(e);
                    junit.framework.AssertionFailedError err
                        = new junit.framework.AssertionFailedError(failmsg);
                    err.setStackTrace(new java.lang.StackTraceElement[]{});
                    err.initCause(e);
                    result.addFailure(this, err);
                } finally {
                    org.jmlspecs.jmlrac.runtime.JMLChecker.setLevel(l);
                }
            } catch (java.lang.Throwable e) {
                // test success
            }
        }

        /** Call the method to be tested with the appropriate arguments. */
        protected abstract void doCall() throws java.lang.Throwable;

        /** Format the error message for a test failure, based on the
         * method's arguments. */
        protected abstract java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e);

        /** Inform listeners that a meaningless test was run. */
        private void addMeaningless() {
            if (result instanceof org.jmlspecs.jmlunit.JMLTestResult) {
                ((org.jmlspecs.jmlunit.JMLTestResult)result)
                    .addMeaningless(this);
            }
        }
    }

    /** Create the tests that are to be run for testing the class
     * TransposableNode.  The framework will then run them.
     * @param overallTestSuite$ The suite accumulating all of the tests
     * for this driver class.
     */
    //@ requires overallTestSuite$ != null;
    public void addTestSuiteForEachMethod
        (junit.framework.TestSuite overallTestSuite$)
    {
        try {
            this.addTestSuiteFor$TestTransposableNode(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestEquals(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestClone(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestSetValue(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestGetValue(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestHashCode(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestToString(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
    }

    /** Add tests for the TransposableNode contructor
     * to the overall test suite. */
    private void addTestSuiteFor$TestTransposableNode
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("TransposableNode");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                vjava_lang_Object$1$iter
                = this.vjava_lang_ObjectIter("TransposableNode", 0);
            this.check_has_data
                (vjava_lang_Object$1$iter,
                 "this.vjava_lang_ObjectIter(\"TransposableNode\", 0)");
            while (!vjava_lang_Object$1$iter.atEnd()) {
                final java.lang.Object v
                    = (java.lang.Object) vjava_lang_Object$1$iter.get();
                methodTests$.addTest
                    (new TestTransposableNode(v));
                vjava_lang_Object$1$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the TransposableNode contructor. */
    protected static class TestTransposableNode extends OneTest {
        /** Argument v */
        private java.lang.Object v;

        /** Initialize this instance. */
        public TestTransposableNode(java.lang.Object v) {
            super("TransposableNode"+ ":" + (v==null? "null" :"{java.lang.Object}"));
            this.v = v;
        }

        protected void doCall() throws java.lang.Throwable {
            new TransposableNode(v);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tContructor 'TransposableNode' applied to";
            msg += "\n\tArgument v: " + this.v;
            return msg;
        }
    }

    /** Add tests for the equals method
     * to the overall test suite. */
    private void addTestSuiteFor$TestEquals
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("equals");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vorg_jmlspecs_samples_digraph_TransposableNodeIter("equals", 1));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vorg_jmlspecs_samples_digraph_TransposableNodeIter(\"equals\", 1))");
            while (!receivers$iter.atEnd()) {
                org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                    vjava_lang_Object$1$iter
                    = this.vjava_lang_ObjectIter("equals", 0);
                this.check_has_data
                    (vjava_lang_Object$1$iter,
                     "this.vjava_lang_ObjectIter(\"equals\", 0)");
                while (!vjava_lang_Object$1$iter.atEnd()) {
                    final org.jmlspecs.samples.digraph.TransposableNode receiver$
                        = (org.jmlspecs.samples.digraph.TransposableNode) receivers$iter.get();
                    final java.lang.Object o
                        = (java.lang.Object) vjava_lang_Object$1$iter.get();
                    methodTests$.addTest
                        (new TestEquals(receiver$, o));
                    vjava_lang_Object$1$iter.advance();
                }
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the equals method. */
    protected static class TestEquals extends OneTest {
        /** The receiver */
        private org.jmlspecs.samples.digraph.TransposableNode receiver$;
        /** Argument o */
        private java.lang.Object o;

        /** Initialize this instance. */
        public TestEquals(org.jmlspecs.samples.digraph.TransposableNode receiver$, java.lang.Object o) {
            super("equals"+ ":" + (o==null? "null" :"{java.lang.Object}"));
            this.receiver$ = receiver$;
            this.o = o;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.equals(o);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'equals' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            msg += "\n\tArgument o: " + this.o;
            return msg;
        }
    }

    /** Add tests for the clone method
     * to the overall test suite. */
    private void addTestSuiteFor$TestClone
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("clone");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vorg_jmlspecs_samples_digraph_TransposableNodeIter("clone", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vorg_jmlspecs_samples_digraph_TransposableNodeIter(\"clone\", 0))");
            while (!receivers$iter.atEnd()) {
                final org.jmlspecs.samples.digraph.TransposableNode receiver$
                    = (org.jmlspecs.samples.digraph.TransposableNode) receivers$iter.get();
                methodTests$.addTest
                    (new TestClone(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the clone method. */
    protected static class TestClone extends OneTest {
        /** The receiver */
        private org.jmlspecs.samples.digraph.TransposableNode receiver$;

        /** Initialize this instance. */
        public TestClone(org.jmlspecs.samples.digraph.TransposableNode receiver$) {
            super("clone");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.clone();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'clone' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the setValue method
     * to the overall test suite. */
    private void addTestSuiteFor$TestSetValue
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("setValue");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vorg_jmlspecs_samples_digraph_TransposableNodeIter("setValue", 1));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vorg_jmlspecs_samples_digraph_TransposableNodeIter(\"setValue\", 1))");
            while (!receivers$iter.atEnd()) {
                org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                    vjava_lang_Object$1$iter
                    = this.vjava_lang_ObjectIter("setValue", 0);
                this.check_has_data
                    (vjava_lang_Object$1$iter,
                     "this.vjava_lang_ObjectIter(\"setValue\", 0)");
                while (!vjava_lang_Object$1$iter.atEnd()) {
                    final org.jmlspecs.samples.digraph.TransposableNode receiver$
                        = (org.jmlspecs.samples.digraph.TransposableNode) receivers$iter.get();
                    final java.lang.Object arg1
                        = (java.lang.Object) vjava_lang_Object$1$iter.get();
                    methodTests$.addTest
                        (new TestSetValue(receiver$, arg1));
                    vjava_lang_Object$1$iter.advance();
                }
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the setValue method. */
    protected static class TestSetValue extends OneTest {
        /** The receiver */
        private org.jmlspecs.samples.digraph.TransposableNode receiver$;
        /** Argument arg1 */
        private java.lang.Object arg1;

        /** Initialize this instance. */
        public TestSetValue(org.jmlspecs.samples.digraph.TransposableNode receiver$, java.lang.Object arg1) {
            super("setValue"+ ":" + (arg1==null? "null" :"{java.lang.Object}"));
            this.receiver$ = receiver$;
            this.arg1 = arg1;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.setValue(arg1);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'setValue' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            msg += "\n\tArgument arg1: " + this.arg1;
            return msg;
        }
    }

    /** Add tests for the getValue method
     * to the overall test suite. */
    private void addTestSuiteFor$TestGetValue
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("getValue");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vorg_jmlspecs_samples_digraph_TransposableNodeIter("getValue", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vorg_jmlspecs_samples_digraph_TransposableNodeIter(\"getValue\", 0))");
            while (!receivers$iter.atEnd()) {
                final org.jmlspecs.samples.digraph.TransposableNode receiver$
                    = (org.jmlspecs.samples.digraph.TransposableNode) receivers$iter.get();
                methodTests$.addTest
                    (new TestGetValue(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the getValue method. */
    protected static class TestGetValue extends OneTest {
        /** The receiver */
        private org.jmlspecs.samples.digraph.TransposableNode receiver$;

        /** Initialize this instance. */
        public TestGetValue(org.jmlspecs.samples.digraph.TransposableNode receiver$) {
            super("getValue");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.getValue();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'getValue' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the hashCode method
     * to the overall test suite. */
    private void addTestSuiteFor$TestHashCode
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("hashCode");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vorg_jmlspecs_samples_digraph_TransposableNodeIter("hashCode", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vorg_jmlspecs_samples_digraph_TransposableNodeIter(\"hashCode\", 0))");
            while (!receivers$iter.atEnd()) {
                final org.jmlspecs.samples.digraph.TransposableNode receiver$
                    = (org.jmlspecs.samples.digraph.TransposableNode) receivers$iter.get();
                methodTests$.addTest
                    (new TestHashCode(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the hashCode method. */
    protected static class TestHashCode extends OneTest {
        /** The receiver */
        private org.jmlspecs.samples.digraph.TransposableNode receiver$;

        /** Initialize this instance. */
        public TestHashCode(org.jmlspecs.samples.digraph.TransposableNode receiver$) {
            super("hashCode");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.hashCode();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'hashCode' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the toString method
     * to the overall test suite. */
    private void addTestSuiteFor$TestToString
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("toString");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vorg_jmlspecs_samples_digraph_TransposableNodeIter("toString", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vorg_jmlspecs_samples_digraph_TransposableNodeIter(\"toString\", 0))");
            while (!receivers$iter.atEnd()) {
                final org.jmlspecs.samples.digraph.TransposableNode receiver$
                    = (org.jmlspecs.samples.digraph.TransposableNode) receivers$iter.get();
                methodTests$.addTest
                    (new TestToString(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the toString method. */
    protected static class TestToString extends OneTest {
        /** The receiver */
        private org.jmlspecs.samples.digraph.TransposableNode receiver$;

        /** Initialize this instance. */
        public TestToString(org.jmlspecs.samples.digraph.TransposableNode receiver$) {
            super("toString");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.toString();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'toString' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Check that the iterator is non-null and not empty. */
    private void
    check_has_data(org.jmlspecs.jmlunit.strategies.IndefiniteIterator iter,
                   String call)
    {
        if (iter == null) {
            junit.framework.Assert.fail(call + " returned null");
        }
        if (iter.atEnd()) {
            junit.framework.Assert.fail(call + " returned an empty iterator");
        }
    }

    /** Converts a char to a printable String for display */
    public static String charToString(char c) {
        if (c == '\n') {
            return "NL";
        } else if (c == '\r') {
            return "CR";
        } else if (c == '\t') {
            return "TAB";
        } else if (Character.isISOControl(c)) {
            int i = (int)c;
            return "\\u"
                    + Character.forDigit((i/2048)%16,16)
                    + Character.forDigit((i/256)%16,16)
                    + Character.forDigit((i/16)%16,16)
                    + Character.forDigit((i)%16,16);
        }
        return Character.toString(c);
    }
}
