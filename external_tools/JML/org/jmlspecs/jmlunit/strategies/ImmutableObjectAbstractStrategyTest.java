// @(#)$Id: ImmutableObjectAbstractStrategyTest.java,v 1.2 2005/07/07 21:03:04 leavens Exp $

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

/** Hand-coded JUnit test for testing ImmutableObjectAbstractStrategy.
 * @author Gary T. Leavens
 */
public class ImmutableObjectAbstractStrategyTest extends TestCase
{
    /** Initialize this class. */
    public ImmutableObjectAbstractStrategyTest(String name) {
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
            (ImmutableObjectAbstractStrategyTest.class);
    }

    /** A class that just provides null */
    protected class SmallestIOAS extends ImmutableObjectAbstractStrategy
    {
    }

    /** A class that just provides null and one more value */
    protected class SingletonIOAS extends ImmutableObjectAbstractStrategy
    {
        Object newObj;

        //@ requires o != null;
        public SingletonIOAS(Object o) {
            newObj = o;
        }

        protected Object[] addData() {
            return new Object[] { newObj, };
        }
    }

    /** Test SmallestIOAS's iterator */
    public void testSmallestIOAS() {
        IndefiniteIterator iter = new SmallestIOAS().iterator();
        assertTrue(!iter.atEnd());
        assertEquals(null, iter.get());
        assertEquals(null, iter.get());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(iter.atEnd());
    }

    /** Test SingletonIOAS's iterator */
    public void testSingletonIOAS() {
        Object obj = "a string for JML/JUnit testing, ok?";
        IndefiniteIterator iter = new SingletonIOAS(obj).iterator();
        assertTrue(!iter.atEnd());
        assertEquals(null, iter.get());
        assertEquals(null, iter.get());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(!iter.atEnd());
        assertTrue(obj == iter.get());
        assertTrue(obj == iter.get());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(iter.atEnd());
    }

    /** Test freshness of this strategy. */
    public void testImmutableObjectAbstractStrategyFreshness() {
        IndefiniteIterator[] iters = new IndefiniteIterator[2];
        StrategyType strat = new SingletonIOAS("a test obj");
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
    public void testImmutableObjectAbstractStrategyExtension() {
        final Object obj1 = "an added Object 123$#$&^";
        final Object obj2 = new Integer(541227);
        StrategyType strat
            = new ImmutableObjectAbstractStrategy()
                {
                    protected Object[] addData() {
                        return new Object[] { obj1, obj2, };
                    }
                };

        // should start with the null from ImmutableObjectAbstractStrategy...
        IndefiniteIterator iter = strat.iterator();
        assertFalse(iter.atEnd());
        assertTrue(iter.get() == null);
        // and should have obj1...
        assertTrue(IndefiniteIteratorUtilities.contains
                   (strat.iterator(), obj1));
        // and should have obj2...
        assertTrue(IndefiniteIteratorUtilities.contains
                   (strat.iterator(), obj2));
        // and no duplicates.
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (strat.iterator()));
        assertEquals(3, IndefiniteIteratorUtilities.size(strat.iterator()));
    }
}
