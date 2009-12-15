// @(#)$Id: Purse_JML_TestData.java,v 1.5 2004/07/20 22:43:33 leavens Exp $

// Copyright (C) 2004 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

/** Supply test data for the JML and JUnit based testing of 
 *  Purse.
 *
 *  <p>Test data is supplied by overriding methods in this class.  See
 *  the JML documentation and the comments below about how to do this.
 *
 *  <p>This class is also the place to override the <kbd>setUp()</kbd>
 *  and <kbd>tearDown()</kbd> methods if your testing needs some
 *  actions to be taken before and after each test is executed.
 *
 *  <p>This class is never rewritten by jmlunit.
 */
public abstract class Purse_JML_TestData
    extends junit.framework.TestCase
{
    /** Initialize this class. */
    public Purse_JML_TestData(java.lang.String name) {
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
     * subclass of {@link junit.framework.TestSuite} in which you override the
     * addTest method.
     * @see junit.framework.TestSuite
     */
    //@ assignable objectState;
    //@ ensures \result != null;
    public junit.framework.TestSuite overallTestSuite() {
        return new junit.framework.TestSuite("Overall tests for Purse");
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
        return new junit.framework.TestSuite(methodName);
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

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * int
     * for testing the method named by the String methodName in
     * a loop that encloses loopsThisSurrounds many other loops.
     * @param methodName name of the method for which this
     *                      test data will be used.
     * @param loopsThisSurrounds number of loops that the test
     *                           contains inside this one.
     */
    //@ requires methodName != null && loopsThisSurrounds >= 0;
    //@ ensures \fresh(\result);
    protected org.jmlspecs.jmlunit.strategies.IntIterator
        vintIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vintStrategy.intIterator();
    }

    /** The strategy for generating test data of type
     * int. */
    private org.jmlspecs.jmlunit.strategies.IntStrategyType
        vintStrategy
        = new org.jmlspecs.jmlunit.strategies.IntStrategy()
            {
                protected int[] addData() {
                    return new int[] {
                        -22, 20, 53, 100, 101,
                    };
                }
            };

    byte p[] = new byte[] { 0, 1, 2, 3, };

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * Purse
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
        vPurseIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vPurseStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * Purse. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vPurseStrategy
        = new org.jmlspecs.jmlunit.strategies.NewObjectAbstractStrategy()
            {
                protected Object make(int n) {
                    switch (n) {
                    case 0:
                        return new Purse(1,0,p);
                    case 1:
                        return new Purse(1,1,p);
                    case 2:
                        return new Purse(100,53,p);
                    default:
                        break;
                    }
                    throw new java.util.NoSuchElementException();
                }
            };

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * byte[]
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
        vbyte$_Iter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vbyte$_Strategy.iterator();
    }

    /** The strategy for generating test data of type
     * byte[]. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vbyte$_Strategy
        = new org.jmlspecs.jmlunit.strategies.CloneableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {
                    return new byte[][] {
                        new byte[] { },
                        new byte[] { 0, 0, 0, },
                        new byte[] { 0, 0, 0, 0, },
                        new byte[] { 0, 0, 0, 0, 0 },
                        new byte[] { 1, 2, 3, 4 },
                        new byte[] { 1, 2, 3, 5 },
                        new byte[] { 9, 1, 2, 3 },
                        new byte[] { 6, 2, 3, 4 },
                        new byte[] { 1, 2, 7, 4 },
                        new byte[] { 1, 5, 3, 4 },
                        new byte[] { 4, 3, 2, 1 },
                        (byte[]) p.clone(),
                    };
                }

                //@ also
                //@ requires o$ != null;
                protected Object cloneElement(java.lang.Object o$) {
                    byte[] down$
                        = (byte[]) o$;
                    return down$.clone();
                }
            };
}
