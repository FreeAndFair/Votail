// This file was generated by jmlunit on Sun Jan 11 22:50:38 CST 2004.

package org.jmlspecs.models;

import java.util.Enumeration;

/** Supply test data for the JML and JUnit based testing of 
 *  Person.
 *
 *  <p>Test data is supplied by overriding methods in this class.  See
 *  the JML documentation and the comments below about how to do this.
 *
 *  <p>This class is also the place to override the <kbd>setUp()</kbd>
 *  and <kbd>tearDown()</kbd> methods if your testing needs some
 *  actions to be taken before and after each test is executed.
 *
 *  <p>This class is never rewritten by jmlunit.
 *
 */
public abstract class JMLObjectToObjectRelation_JML_TestData
    extends junit.framework.TestCase
{
    /** Initialize this class. */
    public JMLObjectToObjectRelation_JML_TestData(java.lang.String name) {
        super(name);
    }

    /** Return the overall test suite for accumulating tests; the
     * result will hold every test that will be run.  This factory
     * method can be altered to provide filtering of test suites, as
     * they are added to this overall test suite, based on various
     * criteria.  The test driver will first call the method
     * addTestSuite to add a test suite formed from custom programmed
     * test methods (named testX for some X), which you can add to
     * this class; this initial test suite will also include a method
     * to check that the code being tested was compiled with jmlc.
     * After that, for each method to be tested, a test suite
     * containing tests for that method will be added to this overall
     * test suite, using the addTest method.  Test suites added for a
     * method will have some subtype of TestSuite and that method's
     * name as their name. So, if you want to control the overall
     * suite of tests for testing some method, e.g., to limit the
     * number of tests for each method, return a special-purpose
     * subclass of junit.framework.TestSuite in which you override the
     * addTest method.
     * @see junit.framework.TestSuite
     */
    //@ assignable objectState;
    //@ ensures \result != null;
    public junit.framework.TestSuite overallTestSuite() {
        return new junit.framework.TestSuite("Overall tests for JMLObjectToObjectRelation");
    }

    /** Return an empty test suite for accumulating tests for the
     * named method.  This factory method can be altered to provide
     * filtering or limiting of the tests for the named method, as
     * they are added to the test suite for this method.  The driver
     * will add individual tests using the addTest method.  So, if you
     * want to filter individual tests, return a subclass of TestSuite
     * in which you override the addTest method.
     * @param methodName The method the tests in this suite are for.
     * @see junit.framework.TestSuite
     * @see org.jmlspecs.jmlunit.strategies.LimitedTestSuite
     */
    //@ assignable objectState;
    //@ ensures \result != null;
    public junit.framework.TestSuite emptyTestSuiteFor
        (java.lang.String methodName)
    {
        return new org.jmlspecs.jmlunit.strategies.LimitedTestSuite(methodName,
                                                                    20);
    }

    // You should edit the following code to supply test data.  In the
    // skeleton originally supplied below the jmlunit tool made a
    // guess as to a minimal strategy for generating test data for
    // each type of object used as a receiver, and each type used as
    // an argument.  There is a library of strategies for generating
    // test data in org.jmlspecs.jmlunit.strategies, which are used in
    // the tool's guesses.  See the documentation for JML and in
    // particular for the org.jmlspecs.jmlunit.strategies package for
    // a general discussion of how to do this.  (This package's
    // documentation is available through the JML.html file in the top
    // of the JML release, and also in the package.html file that
    // ships with the package.)
    //
    // You can change the strategies guessed by the jmlunit tool, and
    // you can also define new ones to suit your needs.  You can also
    // delete any useless sample test data that has been generated
    // for you to show you the pattern of how to add your own test
    // data.  The only requirement is that you implement the methods
    // below.
    //
    // If you change the type being tested in a way that introduces
    // new types of arguments for some methods, then you will have to
    // introduce (by hand) definitions that are similar to the ones
    // below, because jmlunit never rewrites this file.

    private final Integer i4 = new Integer(4);
    private final Integer i3 = new Integer(3);
    private final Integer i2 = new Integer(2);
    private final Integer i1 = new Integer(1);
    private final Integer i0 = new Integer(0);

    private final JMLObjectToObjectRelation intsToArrays
        = new JMLObjectToObjectRelation(i1, new int[] {1})
        .union(new JMLObjectToObjectRelation(i2, new int[] {2}))
        .union(new JMLObjectToObjectRelation(i3, new int[] {3}));
        
    private final JMLObjectToObjectRelation lessThan4
        = new JMLObjectToObjectRelation(i4, i3)
        .union(new JMLObjectToObjectRelation(i4, i2))
        .union(new JMLObjectToObjectRelation(i4, i1))
        .union(new JMLObjectToObjectRelation(i4, i0));
    private final JMLObjectToObjectRelation lessThan3
        = new JMLObjectToObjectRelation(i3, i2)
        .union(new JMLObjectToObjectRelation(i3, i1))
        .union(new JMLObjectToObjectRelation(i3, i0));
    private final JMLObjectToObjectRelation lessThan2
        = new JMLObjectToObjectRelation(i2, i1)
        .union(new JMLObjectToObjectRelation(i2, i0));

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * org.jmlspecs.models.JMLValueToObjectRelation
     * for testing the method named by the String methodName in
     * a loop that encloses loopsThisSurrounds many other loops.
     * @param methodName name of the method for which this
     *                      test data will be used.
     * @param loopsThisSurrounds number of loops that the test
     *                           contains inside this one.
     */
    //@ requires methodName != null && loopsThisSurrounds >= 0;
    //@ ensures \fresh(\result);
    protected org.jmlspecs.jmlunit.strategies.IndefiniteIterator
        vorg_jmlspecs_models_JMLValueToObjectRelationIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vorg_jmlspecs_models_JMLValueToObjectRelationStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.models.JMLValueToObjectRelation. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_models_JMLValueToObjectRelationStrategy
        = new org.jmlspecs.jmlunit.strategies.ImmutableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {
                    return new org.jmlspecs.models.JMLValueToObjectRelation[] {
                        new JMLValueToObjectRelation(new JMLInteger(0), i3),
                        new JMLValueToObjectRelation(new JMLInteger(0), i3)
                        .union(new JMLValueToObjectRelation(new JMLInteger(1), i2))
                        .union(new JMLValueToObjectRelation(new JMLInteger(2), i1))
                        .union(new JMLValueToObjectRelation(new JMLInteger(4), i0)),
                    };
                }
            };

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * org.jmlspecs.models.JMLObjectObjectPair
     * for testing the method named by the String methodName in
     * a loop that encloses loopsThisSurrounds many other loops.
     * @param methodName name of the method for which this
     *                      test data will be used.
     * @param loopsThisSurrounds number of loops that the test
     *                           contains inside this one.
     */
    //@ requires methodName != null && loopsThisSurrounds >= 0;
    //@ ensures \fresh(\result);
    protected org.jmlspecs.jmlunit.strategies.IndefiniteIterator
        vorg_jmlspecs_models_JMLObjectObjectPairIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vorg_jmlspecs_models_JMLObjectObjectPairStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.models.JMLObjectObjectPair. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_models_JMLObjectObjectPairStrategy
        = new org.jmlspecs.jmlunit.strategies.CloneableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {
                    return new org.jmlspecs.models.JMLObjectObjectPair[] {
                        new JMLObjectObjectPair(new Object(), new Object()),
                        new JMLObjectObjectPair(i4, i3),
                        new JMLObjectObjectPair(i3, i2),
                        new JMLObjectObjectPair(i2, i1),
                    };
                }

                //@ also
                //@ requires o$ != null;
                protected Object cloneElement(java.lang.Object o$) {
                    org.jmlspecs.models.JMLObjectObjectPair down$
                        = (org.jmlspecs.models.JMLObjectObjectPair) o$;
                    return down$.clone();
                }
            };

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * org.jmlspecs.models.JMLObjectSet
     * for testing the method named by the String methodName in
     * a loop that encloses loopsThisSurrounds many other loops.
     * @param methodName name of the method for which this
     *                      test data will be used.
     * @param loopsThisSurrounds number of loops that the test
     *                           contains inside this one.
     */
    //@ requires methodName != null && loopsThisSurrounds >= 0;
    //@ ensures \fresh(\result);
    protected org.jmlspecs.jmlunit.strategies.IndefiniteIterator
        vorg_jmlspecs_models_JMLObjectSetIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vorg_jmlspecs_models_JMLObjectSetStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.models.JMLObjectSet. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_models_JMLObjectSetStrategy
        = new org.jmlspecs.jmlunit.strategies.ImmutableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {
                    return new org.jmlspecs.models.JMLObjectSet[] {
                        new JMLObjectSet(),
                        new JMLObjectSet(new Integer(7)),
                        new JMLObjectSet(i4).insert(i3).insert(i2),
                        new JMLObjectSet(i1),
                    };
                }
            };

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * org.jmlspecs.models.JMLObjectToObjectRelation
     * for testing the method named by the String methodName in
     * a loop that encloses loopsThisSurrounds many other loops.
     * @param methodName name of the method for which this
     *                      test data will be used.
     * @param loopsThisSurrounds number of loops that the test
     *                           contains inside this one.
     */
    //@ requires methodName != null && loopsThisSurrounds >= 0;
    //@ ensures \fresh(\result);
    protected org.jmlspecs.jmlunit.strategies.IndefiniteIterator
        vorg_jmlspecs_models_JMLObjectToObjectRelationIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vorg_jmlspecs_models_JMLObjectToObjectRelationStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.models.JMLObjectToObjectRelation. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_models_JMLObjectToObjectRelationStrategy
        = new org.jmlspecs.jmlunit.strategies.ImmutableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {
                    return new org.jmlspecs.models.JMLObjectToObjectRelation[] {
                        new JMLObjectToObjectRelation(),
                        new JMLObjectToObjectRelation(new Object(), new Object()),
                        intsToArrays,
                        lessThan4,
                        lessThan3,
                        lessThan3.union(new JMLObjectToObjectRelation(i2, i4)),
                        lessThan2,
                        lessThan4.union(lessThan3).union(lessThan2),
                        lessThan2.union(lessThan4),
                        new JMLObjectToObjectRelation(i4, new java.util.HashSet())
                        .union(new JMLObjectToObjectRelation(i4,
                                                             new
                                                             java.util.Hashtable()))
                        .union(new JMLObjectToObjectRelation(i4, i3)),
                    };
                }
            };

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * java.lang.Object
     * for testing the method named by the String methodName in
     * a loop that encloses loopsThisSurrounds many other loops.
     * @param methodName name of the method for which this
     *                      test data will be used.
     * @param loopsThisSurrounds number of loops that the test
     *                           contains inside this one.
     */
    //@ requires methodName != null && loopsThisSurrounds >= 0;
    //@ ensures \fresh(\result);
    protected org.jmlspecs.jmlunit.strategies.IndefiniteIterator
        vjava_lang_ObjectIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vjava_lang_ObjectStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * java.lang.Object. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vjava_lang_ObjectStrategy
        = new org.jmlspecs.jmlunit.strategies.ObjectStrategy()
            {
                protected Object make(int n) {
                    switch (n) {
                    case 0:
                        return new JMLObjectSet();
                    case 1:
                        return i4;
                    case 2:
                        return i3;
                    case 3:
                        return i2;
                    case 4:
                        return i1;
                    case 5:
                        return i0;
                    default:
                        break;
                    }
                    throw new java.util.NoSuchElementException();
                }
            };
}
