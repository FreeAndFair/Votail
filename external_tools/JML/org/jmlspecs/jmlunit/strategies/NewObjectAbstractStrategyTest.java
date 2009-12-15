// @(#)$Id: NewObjectAbstractStrategyTest.java,v 1.2 2005/07/07 21:03:04 leavens Exp $

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

/** Hand-coded JUnit test for testing NewObjectAbstractStrategy.
 * @author Gary T. Leavens
 */
public class NewObjectAbstractStrategyTest extends TestCase
{
    /** Initialize this class. */
    public NewObjectAbstractStrategyTest(String name) {
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
            (NewObjectAbstractStrategyTest.class);
    }

    /** A class that just provides null */
    protected class SmallestNOAS extends NewObjectAbstractStrategy
    {
        protected Object make(int n) {
            throw new NoSuchElementException();
        }
    }

    /** A class that just provides null and one more object */
    protected class SingletonNOAS extends NewObjectAbstractStrategy
    {
        protected Object make(int n) {
            switch (n) {
            case 0:
                return new ArrayList();
            default:
                break;
            }
            throw new NoSuchElementException();
        }
    }

    /** Test SmallestNOAS's iterator */
    public void testSmallestNOAS() {
        IndefiniteIterator iter = new SmallestNOAS().iterator();
        assertTrue(!iter.atEnd());
        assertEquals(null, iter.get());
        assertEquals(null, iter.get());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(iter.atEnd());
    }

    /** Test SingletonNOAS's iterator */
    public void testSingletonNOAS() {
        IndefiniteIterator iter = new SingletonNOAS().iterator();
        assertTrue(!iter.atEnd());
        assertEquals(null, iter.get());
        assertEquals(null, iter.get());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(!iter.atEnd());
        Object o1 = iter.get();
        assertTrue(o1 != null && o1.equals(new ArrayList()));
        assertTrue(o1 != iter.get());
        assertTrue(o1.equals(iter.get()));
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(iter.atEnd());
    }

    /** Test freshness of this strategy. */
    public void testNewObjectAbstractStrategyFreshness() {
        IndefiniteIterator[] iters = new IndefiniteIterator[2];
        StrategyType strat
            = new SingletonNOAS();
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
    public void testNewObjectAbstractStrategyExtension() {
        StrategyType strat = new CollectionStrategy();
        // should start with the null from NewObjectAbstractStrategy...
        IndefiniteIterator iter = strat.iterator();
        assertFalse(iter.atEnd());
        assertTrue(iter.get() == null);
        // and should have a hashset
        iter.advance();
        assertFalse(iter.atEnd());
        assertTrue(iter.get() instanceof HashSet);
        // and should have an ArrayList
        iter.advance();
        assertFalse(iter.atEnd());
        assertTrue(iter.get() instanceof ArrayList);
        // and no duplicates.
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (strat.iterator()));
        assertEquals(3, IndefiniteIteratorUtilities.size(strat.iterator()));
    }
}
