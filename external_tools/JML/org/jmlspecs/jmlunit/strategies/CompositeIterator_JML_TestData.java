// @(#)$Id: CompositeIterator_JML_TestData.java,v 1.2 2005/07/07 21:03:04 leavens Exp $

// Copyright (C) 2005 Iowa State University
//
// This file is part of the runtime library of the Java Modeling Language.
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation; either version 2.1,
// of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with JML; see the file LesserGPL.txt.  If not, write to the Free
// Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
// 02110-1301  USA.

package org.jmlspecs.jmlunit.strategies;

import java.util.NoSuchElementException;

/** Supply test data for the JML and JUnit based testing of 
 *  CompositeIterator.
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
public abstract class CompositeIterator_JML_TestData
    extends junit.framework.TestCase
{
    /** Initialize this class. */
    public CompositeIterator_JML_TestData(java.lang.String name) {
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
        return new junit.framework.TestSuite("Overall tests for CompositeIterator");
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
     * org.jmlspecs.jmlunit.strategies.CompositeIterator
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
        vorg_jmlspecs_jmlunit_strategies_CompositeIteratorIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vorg_jmlspecs_jmlunit_strategies_CompositeIteratorStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.jmlunit.strategies.CompositeIterator. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_jmlunit_strategies_CompositeIteratorStrategy
        = new org.jmlspecs.jmlunit.strategies.CloneableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {
                    return new org.jmlspecs.jmlunit.strategies.CompositeIterator[] {
                        new CompositeIterator(new IntStrategy().intIterator()),
                        new CompositeIterator(new ObjectStrategy().iterator(),
                                              new EmptyNewObjectIterator()),
                        new CompositeIterator
                        (new IndefiniteIterator[] {
                            new IntStrategy().iterator(),
                            new IntBigStrategy().intIterator(),
                            new CharBigStrategy().charIterator(),
                            new ShortBigStrategy().shortIterator(),
                        }),
                        new CompositeIterator
                        (new IndefiniteIterator[] {
                            new IntStrategy().iterator(),
                            new IntBigStrategy().intIterator(),
                            new CompositeIterator
                            (new CharBigStrategy().charIterator(),
                             new ShortBigStrategy().shortIterator()),
                        }),
                    };
                }

                //@ also
                //@ requires o$ != null;
                protected Object cloneElement(java.lang.Object o$) {
                    org.jmlspecs.jmlunit.strategies.CompositeIterator down$
                        = (org.jmlspecs.jmlunit.strategies.CompositeIterator) o$;
                    return down$.clone();
                }
            };

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * org.jmlspecs.jmlunit.strategies.IndefiniteIterator[]
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
        vorg_jmlspecs_jmlunit_strategies_IndefiniteIterator$_Iter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vorg_jmlspecs_jmlunit_strategies_IndefiniteIterator$_Strategy.iterator();
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.jmlunit.strategies.IndefiniteIterator[]. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_jmlunit_strategies_IndefiniteIterator$_Strategy
        = new org.jmlspecs.jmlunit.strategies.CloneableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {
                    return new org.jmlspecs.jmlunit.strategies.IndefiniteIterator[][] {
                        new IndefiniteIterator[]{},
                        new IndefiniteIterator[] {
                            new IntStrategy().intIterator(),
                        },
                        new IndefiniteIterator[] {
                            new IntStrategy().iterator(),
                            new IntBigStrategy().intIterator(),
                            new CharBigStrategy().charIterator(),
                            new ShortBigStrategy().shortIterator(),
                        },
                    };
                }

                //@ also
                //@ requires o$ != null;
                protected Object cloneElement(java.lang.Object o$) {
                    org.jmlspecs.jmlunit.strategies.IndefiniteIterator[] down$
                        = (org.jmlspecs.jmlunit.strategies.IndefiniteIterator[]) o$;
                    return down$.clone();
                }
            };

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * org.jmlspecs.jmlunit.strategies.IndefiniteIterator
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
        vorg_jmlspecs_jmlunit_strategies_IndefiniteIteratorIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vorg_jmlspecs_jmlunit_strategies_IndefiniteIteratorStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.jmlunit.strategies.IndefiniteIterator. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_jmlunit_strategies_IndefiniteIteratorStrategy
        = new org.jmlspecs.jmlunit.strategies.CloneableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {
                    return new org.jmlspecs.jmlunit.strategies.IndefiniteIterator[] {
                        new ObjectStrategy().iterator(),
                        new IntStrategy().iterator(),
                        new IntBigStrategy().intIterator(),
                        new CharBigStrategy().charIterator(),
                        new ShortBigStrategy().shortIterator(),
                    };
                }

                //@ also
                //@ requires o$ != null;
                protected Object cloneElement(java.lang.Object o$) {
                    org.jmlspecs.jmlunit.strategies.IndefiniteIterator down$
                        = (org.jmlspecs.jmlunit.strategies.IndefiniteIterator) o$;
                    return down$.clone();
                }
            };
}
