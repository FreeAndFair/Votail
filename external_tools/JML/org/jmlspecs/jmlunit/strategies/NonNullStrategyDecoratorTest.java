// @(#)$Id: NonNullStrategyDecoratorTest.java,v 1.3 2007/12/19 01:59:43 chalin Exp $

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

/** Hand-coded JUnit test for testing NonNullStrategyDecorator.
 * @author Gary T. Leavens
 */
public class NonNullStrategyDecoratorTest extends TestCase
{
    /** Initialize this class. */
    public NonNullStrategyDecoratorTest(String name) {
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
            (NonNullStrategyDecoratorTest.class);
    }

    /** Test NonNullStrategyDecorator's iterator */
    public void testNonNullStrategyDecorator() {
        StrategyType strat
            = new NonNullStrategyDecorator(new StringStrategy());
        assertFalse(IndefiniteIteratorUtilities.containsNull
                    (strat.iterator()));
        assertFalse(IndefiniteIteratorUtilities.containsNull
                    (strat.iterator()));
        assertTrue(IndefiniteIteratorUtilities.size
                    (strat.iterator())
                   <= IndefiniteIteratorUtilities.size
                   (new StringStrategy().iterator()));
    }

    /** Test NonNullStrategyDecorator's iterator */
    public void testNonNullStrategyDecorator2() {
        StrategyType strat
            = new NonNullStrategyDecorator
            (new StrategyType() {
                    public /*@non_null*/ IndefiniteIterator iterator() {
                        return new ImmutableObjectArrayIterator
                            (new Object[] {
                                new Integer(703), null, null,
                                "a few more", null, "x", null,
                            });
                    }
                });
        assertFalse(IndefiniteIteratorUtilities.containsNull
                    (strat.iterator()));
        assertEquals(3,
                     IndefiniteIteratorUtilities.size(strat.iterator()));
    }

    /** Test freshness of this strategy. */
    public void testNonNullStrategyDecoratorFreshness() {
        IndefiniteIterator[] iters = new IndefiniteIterator[2];
        StrategyType strat
            = new NonNullStrategyDecorator(new ObjectStrategy());
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
