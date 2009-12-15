// @(#)$Id: DLNode_JML_TestData.java,v 1.5 2004/07/14 20:08:04 cruby Exp $

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

package org.jmlspecs.samples.list.list1.node;

/** Supply test data for the JML and JUnit based testing of 
 *  DLNode.
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
public abstract class DLNode_JML_TestData
    extends junit.framework.TestCase
{
    /** Initialize this class. */
    public DLNode_JML_TestData(java.lang.String name) {
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
        return new junit.framework.TestSuite("Overall tests for DLNode");
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
     * org.jmlspecs.samples.list.list1.node.DLNode
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
        vorg_jmlspecs_samples_list_list1_node_DLNodeIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vorg_jmlspecs_samples_list_list1_node_DLNodeStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.samples.list.list1.node.DLNode. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_samples_list_list1_node_DLNodeStrategy
        = new org.jmlspecs.jmlunit.strategies.CloneableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {

                    DLNode node0 = new DLNode(null);
                    DLNode node1 = new DLNode("it");
                    DLNode node2 = new DLNode("first");
                    node2.insertAfter("fourth");
                    node2.insertAfter("third");
                    node2.insertAfter("second");
                    DLNode node3 = new DLNode("second");
                    node3.insertBefore("first");
                    DLNode node4 = new DLNode("fifth",
                                              null, new DLNode("sixth"));
                    DLNode node5 = new DLNode("eighth",
                                              new DLNode("seventh"), null);
                    DLNode node6 = new DLNode("tenth",
                                              new DLNode("ninth"), null);
                    DLNode node7 = new DLNode("8", null, new DLNode("9"));

                    return new DLNode[] {
                        node0,
                        node1,
                        node2,
                        node3,
                        node4,
                        node5,
                        node6,
                        node7,
                        null,
                    };

                }

                //@ also
                //@ requires o$ != null;
                protected Object cloneElement(java.lang.Object o$) {
                    org.jmlspecs.samples.list.list1.node.DLNode down$
                        = (org.jmlspecs.samples.list.list1.node.DLNode) o$;
                    return down$.clone();
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
        = new org.jmlspecs.jmlunit.strategies.CompositeStrategy
        (new org.jmlspecs.jmlunit.strategies.StrategyType[] {
            new org.jmlspecs.jmlunit.strategies.ObjectStrategy(),
            vorg_jmlspecs_samples_list_list1_node_DLNodeStrategy,
        });


    static private org.jmlspecs.samples.list.list1.node.DLNode nullNode = null;

    public void testNode04() {
	org.jmlspecs.samples.list.list1.node.DLNode var10 
	    = new org.jmlspecs.samples.list.list1.node.DLNode("t04-a", 
							      nullNode,
							      nullNode);
	var10.insertAfter("t04-b");
	var10.insertBefore("t04-c");
	org.jmlspecs.samples.list.list1.node.DLNode var143 
	    = var10.getPrevNode();
	var143.removeNextNode();
	var10.insertAfter("t04-d");
    }
    public void testNode07() {
	org.jmlspecs.samples.list.list1.node.DLNode var10 
	    = new org.jmlspecs.samples.list.list1.node.DLNode((Object)null,
							      nullNode,
							      nullNode);
	org.jmlspecs.samples.list.list1.node.DLNode var38 
	    = new org.jmlspecs.samples.list.list1.node.DLNode((Object)null, 
							      nullNode,
							      var10);
	var10.insertBefore((Object)null);
	new org.jmlspecs.samples.list.list1.node.DLNode((Object)null, 
							var10, var38);
    }
    public void testNode08() {
	org.jmlspecs.samples.list.list1.node.DLNode var0 = 
	    new org.jmlspecs.samples.list.list1.node.DLNode((Object)null);
	new org.jmlspecs.samples.list.list1.node.DLNode((Object)null, 
							var0, var0);
    }
    public void testNode09() {
	org.jmlspecs.samples.list.list1.node.DLNode var10 
	    = new org.jmlspecs.samples.list.list1.node.DLNode((Object)null, 
							      nullNode,
							      nullNode);
	new org.jmlspecs.samples.list.list1.node.DLNode((Object)null, 
							var10, var10);
    }
    public void testNode11() {
	org.jmlspecs.samples.list.list1.node.DLNode var0 
	    = new org.jmlspecs.samples.list.list1.node.DLNode((Object)null);
	java.lang.Object var40 = var0.clone();
	org.jmlspecs.samples.list.list1.node.DLNode var10 
	    = new org.jmlspecs.samples.list.list1.node.DLNode((Object)null, 
							      nullNode,
							      nullNode);
	var10.removeNextNode();
	var10.insertBefore(var40);
	var10.insertAfter((java.lang.Object)null);
	org.jmlspecs.samples.list.list1.node.DLNode var34 
	    = new org.jmlspecs.samples.list.list1.node.DLNode((Object)null, 
							      var0, var10);
	java.lang.Object var277 = var34.clone();
	new org.jmlspecs.samples.list.list1.node.DLNode(var277, var10, var10);
    }
    public void testNode12() {
	org.jmlspecs.samples.list.list1.node.DLNode var10 
	    = new org.jmlspecs.samples.list.list1.node.DLNode((Object)null, 
							      nullNode,
							      nullNode);
	org.jmlspecs.samples.list.list1.node.DLNode var0 
	    = new org.jmlspecs.samples.list.list1.node.DLNode((Object)null);
	org.jmlspecs.samples.list.list1.node.DLNode var33 
	    = new org.jmlspecs.samples.list.list1.node.DLNode((Object)null, 
							      var10, var0);
	java.lang.Object var269 = var33.clone();
	org.jmlspecs.samples.list.list1.node.DLNode var140 = var0.getPrevNode();
	var140.insertAfter(var269);
	java.lang.Object var726 = var140.clone();
	var0.removeNextNode();
	org.jmlspecs.samples.list.list1.node.DLNode var420 = var0.getPrevNode();
	var10.removeNextNode();
	var420.removeNextNode();
	java.lang.Object var304 = var10.clone();
	var10.insertBefore((Object)null);
	var10.insertBefore(var304);
	new org.jmlspecs.samples.list.list1.node.DLNode(var726, var420, var10);
    }
}
