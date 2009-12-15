// @(#)$Id: ObjectStrategyTest.java,v 1.3 2005/07/07 21:03:05 leavens Exp $

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

/** Hand-coded JUnit test for testing ObjectStrategy.
 * @author Gary T. Leavens
 */
public class ObjectStrategyTest extends TestCase
{
    /** Initialize this class. */
    public ObjectStrategyTest(String name) {
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
            (ObjectStrategyTest.class);
    }

    /** Test ObjectStrategy's iterator */
    public void testObjectStrategy() {
        IndefiniteIterator iter = new ObjectStrategy().iterator();
        // first is a null...
        assertTrue(!iter.atEnd());
        assertEquals(null, iter.get());
        assertEquals(null, iter.get());

        // then a new Object()...
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(!iter.atEnd());
        Object o = iter.get();
        assertTrue(o != null && o.getClass() == Object.class);

        // and that's all...
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(iter.atEnd());
    }

    /** Test freshness of this strategy. */
    public void testObjectStrategyFreshness() {
        IndefiniteIterator[] iters = new IndefiniteIterator[2];
        iters[0] = new ObjectStrategy().iterator();
        iters[1] = new ObjectStrategy().iterator();
        for (int i = 0; i < iters.length; i++) {
            assertTrue(iters[i] != null);
            for (int j = i+1; j < iters.length; j++) {
                assertTrue(iters[i] != iters[j]);
            }
        }
    }

    /** Test extension of this strategy. */
    public void testObjectStrategyExtension() {
        final Object obj1 = "an added Object 123$#$&^";
        final Object obj2 = new Integer(541227);
        StrategyType strat
            = new ObjectStrategy()
                {
                    protected Object make(int n) {
                        switch (n) {
                        case 0:
                            return obj1;
                        case 1:
                            return obj2;
                        default:
                            break;
                        }
                        throw new NoSuchElementException();
                    }
                };

        // should start with the stuff in ObjectStrategy...
        IndefiniteIterator iter = strat.iterator();
        assertFalse(iter.atEnd());
        assertTrue(iter.get() == null);
        iter.advance();
        assertFalse(iter.atEnd());
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
        assertEquals
            (IndefiniteIteratorUtilities.size(new ObjectStrategy().iterator())
             + 2,
             IndefiniteIteratorUtilities.size(strat.iterator()));
    }
}
