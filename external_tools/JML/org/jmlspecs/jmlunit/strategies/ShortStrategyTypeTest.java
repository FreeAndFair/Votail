// @(#)$Id: shortStrategyTypeTest.java-generic,v 1.5 2005/12/06 19:54:59 chalin Exp $

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

/** Hand-coded JUnit test for subtypes of ShortStrategyType.
 * @author Gary T. Leavens
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class ShortStrategyTypeTest extends TestCase
{
    /** Initialize this class. */
    public ShortStrategyTypeTest(String name) {
        super(name);
    }

    /** Run the tests. */
    public static void main(java.lang.String[] args) {
        junit.textui.TestRunner.run(suite());
    }

    /** Return the test suite for this test class. */
    //@ ensures \result != null;
    public static Test suite() {
        return new junit.framework.TestSuite
            (ShortStrategyTypeTest.class);
    }

//     /** Test ShortStrategy's iterator by printing it. */
//     public void testShortBigStrategyPrint() {
//         ShortIterator iter = new ShortBigStrategy().shortIterator();
//         System.out.println("");
//         while (!iter.atEnd()) {
//             System.out.print("'" + iter.getShort() + "'");
//             System.out.print(", ");
//             iter.advance();
//         }
//         System.out.println("");
//     }

    /** Test ShortStrategy's size */
    public void testShortStrategySize() {
        ShortIterator iter;
        iter = new ShortStrategy().shortIterator();
        long len = IndefiniteIteratorUtilities.size(iter);
        assertTrue("Not big enough", 1 <= len);
        assertTrue("Too big", len <= 5);
    }

    /** Test ShortBigStrategy's size */
    public void testShortBigStrategySize() {
        ShortIterator iter;
        iter = new ShortBigStrategy().shortIterator();
        long len = IndefiniteIteratorUtilities.size(iter);
        assertTrue("Not big enough", 6 <= len);
        assertTrue("Too big", len <= 30);
    }

    /** Test contents of ShortStrategy. */
    public void testShortStrategyContents() {
        assertTrue("Missing 0",
                   IndefiniteIteratorUtilities.contains
                   (new ShortStrategy().shortIterator(),
                    new Short((short)0)));
        assertTrue("Missing 1",
                   IndefiniteIteratorUtilities.contains
                   (new ShortStrategy().shortIterator(),
                    new Short((short)1)));
        assertTrue("Missing -1",
                   IndefiniteIteratorUtilities.contains
                   (new ShortStrategy().shortIterator(),
                    new Short((short)-1)));
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (new ShortStrategy().shortIterator()));
    }

    /** Test contents of ShortBigStrategy. */
    public void testShortBigStrategyContents() {
        assertTrue("Missing 0",
                   IndefiniteIteratorUtilities.contains
                   (new ShortBigStrategy().shortIterator(),
                    new Short((short)0)));
        assertTrue("Missing 1",
                   IndefiniteIteratorUtilities.contains
                   (new ShortBigStrategy().shortIterator(),
                    new Short((short)1)));
        assertTrue("Missing -1",
                   IndefiniteIteratorUtilities.contains
                   (new ShortBigStrategy().shortIterator(),
                    new Short((short)-1)));
        assertTrue("Missing smallest value",
                   IndefiniteIteratorUtilities.contains
                   (new ShortBigStrategy().shortIterator(),
                    new Short(Short.MIN_VALUE)));
        assertTrue("Missing largest value",
                   IndefiniteIteratorUtilities.contains
                   (new ShortBigStrategy().shortIterator(),
                    new Short(Short.MAX_VALUE)));
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (new ShortBigStrategy().shortIterator()));
    }

    /** Test freshness of these strategies. */
    public void testShortStrategyFreshness() {
        ShortIterator[] iters = new ShortIterator[4];
        iters[0] = new ShortStrategy().shortIterator();
        iters[1] = new ShortStrategy().shortIterator();
        iters[2] = new ShortBigStrategy().shortIterator();
        iters[3] = new ShortBigStrategy().shortIterator();
        for (int i = 0; i < iters.length; i++) {
            assertTrue(iters[i] != null);
            for (int j = i+1; j < iters.length; j++) {
                assertTrue(iters[i] != iters[j]);
            }
        }
    }

    /** Test the empty CompositeStrategy's iterator */
    public void testEmptyComposite() {
        ShortStrategyType strat
            = new ShortCompositeStrategy(new ShortStrategyType[]{});
        ShortIterator iter = strat.shortIterator();
        assertTrue(iter.atEnd());
    }

    /** Test a singleton CompositeStrategy's iterator */
    public void testSingletonComposite() {
        ShortStrategyType strat
            = new ShortCompositeStrategy(new ShortStrategy());
        assertEquals(IndefiniteIteratorUtilities.size
                     (new ShortStrategy().shortIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.shortIterator()));
    }

    /** Test a pair CompositeStrategy's iterator */
    public void testPairComposite() {
        ShortStrategyType strat
            = new ShortCompositeStrategy
            (new ShortStrategy(),
             new ShortBigStrategy());
        assertEquals(IndefiniteIteratorUtilities.size
                     (new ShortStrategy().shortIterator())
                     + IndefiniteIteratorUtilities.size
                     (new ShortBigStrategy().shortIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.shortIterator()));
    }

    /** Test a larger CompositeStrategy's iterator */
    public void testLargerComposite() {
        ShortStrategyType strat
            = new ShortCompositeStrategy
            (new ShortStrategyType[] {
                new ShortStrategy(),
                new ShortBigStrategy(),
                new ShortStrategy(),
            });
        assertEquals(2 * IndefiniteIteratorUtilities.size
                     (new ShortStrategy().shortIterator())
                     + IndefiniteIteratorUtilities.size
                     (new ShortBigStrategy().shortIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.shortIterator()));
    }

    /** Test ShortNonNegativeStrategyDecorator */
    public void testNonNegativeStrategyDecorator() {
        ShortStrategyType strat
            = new ShortNonNegativeStrategyDecorator
            (new ShortCompositeStrategy
             (new ShortStrategyType[] {
                 new ShortStrategy(),
                 new ShortBigStrategy(),
                 new ShortStrategy(),
             }));
        assertFalse(IndefiniteIteratorUtilities.contains
                     (strat.shortIterator(),
                      new Short((short)-1)));
    }

}
