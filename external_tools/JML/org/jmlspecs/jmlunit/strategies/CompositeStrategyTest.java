// @(#)$Id: CompositeStrategyTest.java,v 1.2 2005/07/07 21:03:04 leavens Exp $

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

/** Hand-coded JUnit test for testing CompositeStrategy.
 * @author Gary T. Leavens
 */
public class CompositeStrategyTest extends TestCase
{
    /** Initialize this class. */
    public CompositeStrategyTest(String name) {
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
            (CompositeStrategyTest.class);
    }

    /** Test the empty CompositeStrategy's iterator */
    public void testEmptyComposite() {
        StrategyType strat
            = new CompositeStrategy(new StrategyType[]{});
        IndefiniteIterator iter = strat.iterator();
        assertTrue(iter.atEnd());
    }

    /** Test a singleton CompositeStrategy's iterator */
    public void testSingletonComposite() {
        StrategyType strat
            = new CompositeStrategy(new BooleanStrategy());
        IndefiniteIterator iter = strat.iterator();
        assertTrue(!iter.atEnd());
        assertEquals(new Boolean(false), iter.get());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(!iter.atEnd());
        assertEquals(new Boolean(true), iter.get());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(iter.atEnd());
    }

    /** Test a pair CompositeStrategy's iterator */
    public void testPairComposite() {
        StrategyType strat
            = new CompositeStrategy(new BooleanStrategy(),
                                    new IntStrategy());
        IndefiniteIterator iter = strat.iterator();
        assertTrue(!iter.atEnd());
        assertEquals(new Boolean(false), iter.get());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(!iter.atEnd());
        assertEquals(new Boolean(true), iter.get());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(!iter.atEnd());
        assertEquals(new Integer(0), iter.get());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(!iter.atEnd());
        assertEquals(new Integer(1), iter.get());
        iter.advance();
        assertTrue(!iter.atEnd());
        assertEquals(new Integer(-1), iter.get());
        iter.advance();
        assertTrue(iter.atEnd());
    }

    /** Test a larger CompositeStrategy's iterator */
    public void testLargerComposite() {
        StrategyType strat
            = new CompositeStrategy
            (new StrategyType[] {
                new BooleanStrategy(),
                new IntStrategy(),
                new DoubleStrategy(),
            });
        assertEquals(IndefiniteIteratorUtilities.size
                     (new BooleanStrategy().iterator())
                     + IndefiniteIteratorUtilities.size
                     (new IntStrategy().iterator())
                     + IndefiniteIteratorUtilities.size
                      (new DoubleStrategy().iterator()),
                     IndefiniteIteratorUtilities.size(strat.iterator()));
    }

    /** Test freshness of this strategy. */
    public void testCompositeStrategyFreshness() {
        IndefiniteIterator[] iters = new IndefiniteIterator[2];
        StrategyType strat
            = new CompositeStrategy
            (new StrategyType[] {
                new BooleanStrategy(),
                new IntStrategy(),
                new DoubleStrategy(),
            });
        iters[0] = strat.iterator();
        iters[1] = strat.iterator();
        for (int i = 0; i < iters.length; i++) {
            assertTrue(iters[i] != null);
            for (int j = i+1; j < iters.length; j++) {
                assertTrue(iters[i] != iters[j]);
            }
        }
    }

}
