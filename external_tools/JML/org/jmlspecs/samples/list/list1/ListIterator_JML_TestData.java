// @(#)$Id: ListIterator_JML_TestData.java,v 1.3 2004/01/22 20:00:50 leavens Exp $

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

package org.jmlspecs.samples.list.list1;

import org.jmlspecs.samples.list.iterator.Iterator;
import org.jmlspecs.samples.list.iterator.RestartableIterator;

/** Supply test data for the JML and JUnit based testing of 
 *  ListIterator.
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
public abstract class ListIterator_JML_TestData
    extends junit.framework.TestCase
{
    /** Initialize this class. */
    public ListIterator_JML_TestData(java.lang.String name) {
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
        return new junit.framework.TestSuite("Overall tests for ListIterator");
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
     * org.jmlspecs.samples.list.list1.E_SLList
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
        vorg_jmlspecs_samples_list_list1_E_SLListIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vorg_jmlspecs_samples_list_list1_E_SLListStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.samples.list.list1.E_SLList. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_samples_list_list1_E_SLListStrategy
        = new org.jmlspecs.jmlunit.strategies.CloneableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {
                    org.jmlspecs.samples.list.list1.E_SLList[] vE_SLList
                        = new org.jmlspecs.samples.list.list1.E_SLList[] { 
                            new org.jmlspecs.samples.list.list1.E_SLList(),
                            new org.jmlspecs.samples.list.list1.E_SLList(),
                            new org.jmlspecs.samples.list.list1.E_SLList(),
                            new org.jmlspecs.samples.list.list1.E_SLList(),
                            new org.jmlspecs.samples.list.list1.E_SLList(),
                            new org.jmlspecs.samples.list.list1.E_SLList(),
                            new org.jmlspecs.samples.list.list1.E_SLList(),
                            new org.jmlspecs.samples.list.list1.E_SLList(),
                            new org.jmlspecs.samples.list.list1.E_SLList(),
                            null,
                        };
                    vE_SLList[1].insertBeforeCursor("it");
                    vE_SLList[1].firstEntry();

                    vE_SLList[2].insertBeforeCursor("first");
                    vE_SLList[2].firstEntry();
                    vE_SLList[2].insertAfterCursor("second");
                    vE_SLList[2].incrementCursor();
                    vE_SLList[2].incrementCursor();

                    vE_SLList[3].insertBeforeCursor("first");
                    vE_SLList[3].insertBeforeCursor("second");
                    vE_SLList[3].insertBeforeCursor("third");
                    vE_SLList[3].insertBeforeCursor("fourth");
                    vE_SLList[3].firstEntry();
                    vE_SLList[3].incrementCursor();
                    vE_SLList[3].incrementCursor();

                    vE_SLList[4].insertBeforeCursor(new int[1]);
                    vE_SLList[4].insertBeforeCursor(new int[2]);
                    vE_SLList[4].insertBeforeCursor(new int[3]);
                    vE_SLList[4].insertBeforeCursor(new int[4]);
                    vE_SLList[4].firstEntry();

                    vE_SLList[5].insertBeforeCursor("it");
                    vE_SLList[5].decreaseCursor();
                    vE_SLList[5].decreaseCursor();

                    vE_SLList[6].insertBeforeCursor("it");

                    vE_SLList[7] = new E_SLList(vE_SLList[4]);
                    return vE_SLList;
                }

                //@ also
                //@ requires o$ != null;
                protected Object cloneElement(java.lang.Object o$) {
                    org.jmlspecs.samples.list.list1.E_SLList down$
                        = (org.jmlspecs.samples.list.list1.E_SLList) o$;
                    return down$.clone();
                }
            };

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * org.jmlspecs.samples.list.list1.ListIterator
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
        vorg_jmlspecs_samples_list_list1_ListIteratorIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vorg_jmlspecs_samples_list_list1_ListIteratorStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.samples.list.list1.ListIterator. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_samples_list_list1_ListIteratorStrategy
        = new org.jmlspecs.jmlunit.strategies.NewObjectAbstractStrategy()
            {
                protected Object make(int n) {
                    E_SLList list = new E_SLList();
                    switch (n) {
                    case 0:
                        break;
                    case 1:
                        break;
                    case 2:
                        list.insertBeforeCursor("it");
                        list.firstEntry();
                        break;
                    case 3:
                        list.insertBeforeCursor("first");
                        list.firstEntry();
                        list.insertAfterCursor("second");
                        list.incrementCursor();
                        list.incrementCursor();
                        break;
                    case 4:
                        list.insertBeforeCursor("first");
                        list.insertBeforeCursor("second");
                        list.insertBeforeCursor("third");
                        list.insertBeforeCursor("fourth");
                        list.firstEntry();
                        list.incrementCursor();
                        list.incrementCursor();
                        break;
                    case 5:
                        list.insertBeforeCursor(new int[1]);
                        list.insertBeforeCursor(new int[2]);
                        list.insertBeforeCursor(new int[3]);
                        list.insertBeforeCursor(new int[4]);
                        list.firstEntry();
                        break;
                    case 6:
                        list.insertBeforeCursor("it");
                        list.decreaseCursor();
                        list.decreaseCursor();
                        break;
                    case 7:
                        list.insertBeforeCursor("it");
                        break;
                    case 8:
                        list = new E_SLList(new E_SLList());
                        break;
                    default:
                        break;
                    }
                    if (n == 0) {
                        return null;
                    } else if (0 < n && n <= 8) {
                        return new ListIterator(list);
                    }
                    throw new java.util.NoSuchElementException();
                }
            };
}
