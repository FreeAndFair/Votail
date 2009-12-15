// @(#)$Id: CloneableObjectAbstractStrategyTest.java,v 1.3 2005/07/07 21:03:04 leavens Exp $

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

import junit.framework.*;
import org.jmlspecs.jmlunit.*;
import java.util.*;

/** Hand-coded JUnit test for testing CloneableObjectAbstractStrategy.
 * @author Gary T. Leavens
 */
public class CloneableObjectAbstractStrategyTest extends TestCase
{
    /** Initialize this class. */
    public CloneableObjectAbstractStrategyTest(String name) {
        super(name);
    }

    /** Run the tests. */
    public static void main(String[] args) {
        junit.textui.TestRunner.run(suite());
    }

    /** Return the test suite for this test class. */
    //@ ensures \result != null;
    public static Test suite() {
        return new junit.framework.TestSuite
            (CloneableObjectAbstractStrategyTest.class);
    }

    /** A class that just provides null */
    protected class SmallestCOAS extends CloneableObjectAbstractStrategy
    {
        protected /*@ pure @*/ Object cloneElement(Object elem)
            throws InternalError
        {
            throw new InternalError();
        }
    }

    /** A class that just provides null and one more value of type double[] */
    protected class SingletonCOAS extends CloneableObjectAbstractStrategy
    {
        double[] newObj;

        //@ requires o != null;
        public SingletonCOAS(double[] o) {
            newObj = o;
        }

        // doc comment and specification inherited
        protected Object[] addData() {
            return new Object[] { newObj, };
        }

        // doc comment and specification inherited
        protected /*@ pure @*/ Object cloneElement(Object elem) {
            return ((double[])elem).clone();
        }
    }

    /** Test SmallestCOAS's iterator */
    public void testSmallestCOAS() {
        IndefiniteIterator iter = new SmallestCOAS().iterator();
        assertTrue(!iter.atEnd());
        assertEquals(null, iter.get());
        assertEquals(null, iter.get());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(iter.atEnd());
    }

    /** Test SingletonCOAS's iterator */
    public void testSingletonCOAS() {
        double[] obj  = new double[] { 2.73, 3.14159, };
        IndefiniteIterator iter = new SingletonCOAS(obj).iterator();
        assertTrue(!iter.atEnd());
        assertEquals(null, iter.get());
        assertEquals(null, iter.get());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(!iter.atEnd());
        assertTrue(Arrays.equals(obj, (double[])iter.get())); //@ nowarn Cast;
        assertTrue(Arrays.equals(obj, (double[])iter.get())); //@ nowarn Cast;
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(iter.atEnd());
    }

    /** Test freshness of this strategy. */
    public void testCloneableObjectAbstractStrategyFreshness() {
        IndefiniteIterator[] iters = new IndefiniteIterator[2];
        StrategyType strat
            = new SingletonCOAS(new double[] { 2.73, 3.14159, 1.141, });
        iters[0] = strat.iterator();
        iters[1] = strat.iterator();
        for (int i = 0; i < iters.length; i++) {
            assertTrue(iters[i] != null);
            for (int j = i+1; j < iters.length; j++) {
                assertTrue(iters[i] != iters[j]);
            }
        }
    }

    /** Test extension of this strategy. */
    public void testCloneableObjectAbstractStrategyExtension() {
        final int[] obj1 = new int[] { 3, 4, 2, };
        final int[] obj2 = new int[] { 5, 4, 1, 6, 4, 1, };
        StrategyType strat
            = new CloneableObjectAbstractStrategy()
                {
                    protected Object[] addData() {
                        return new Object[] { obj1, obj2, };
                    }

                    protected /*@ pure @*/ Object cloneElement(Object elem) {
                        return ((int[])elem).clone();
                    }
                };

        // should start with the null from CloneableObjectAbstractStrategy...
        IndefiniteIterator iter = strat.iterator();
        assertFalse(iter.atEnd());
        assertTrue(iter.get() == null);
        // and should have a clone of obj1...
        iter.advance();
        assertFalse(iter.atEnd());
        assertTrue(Arrays.equals(obj1, (int[])iter.get()));
        assertTrue(obj1 != iter.get());
        // and should have obj2...
        iter.advance();
        assertFalse(iter.atEnd());
        assertTrue(Arrays.equals(obj2, (int[])iter.get())); //@ nowarn Cast;
        assertTrue(obj2 != iter.get());
        // and no duplicates.
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (strat.iterator()));
        assertEquals(3, IndefiniteIteratorUtilities.size(strat.iterator()));
    }
}
