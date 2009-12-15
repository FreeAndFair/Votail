// @(#)$Id: longStrategyTypeTest.java-generic,v 1.5 2005/12/06 19:54:59 chalin Exp $

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

/** Hand-coded JUnit test for subtypes of LongStrategyType.
 * @author Gary T. Leavens
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class LongStrategyTypeTest extends TestCase
{
    /** Initialize this class. */
    public LongStrategyTypeTest(String name) {
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
            (LongStrategyTypeTest.class);
    }

//     /** Test LongStrategy's iterator by printing it. */
//     public void testLongBigStrategyPrint() {
//         LongIterator iter = new LongBigStrategy().longIterator();
//         System.out.println("");
//         while (!iter.atEnd()) {
//             System.out.print("'" + iter.getLong() + "'");
//             System.out.print(", ");
//             iter.advance();
//         }
//         System.out.println("");
//     }

    /** Test LongStrategy's size */
    public void testLongStrategySize() {
        LongIterator iter;
        iter = new LongStrategy().longIterator();
        long len = IndefiniteIteratorUtilities.size(iter);
        assertTrue("Not big enough", 1 <= len);
        assertTrue("Too big", len <= 5);
    }

    /** Test LongBigStrategy's size */
    public void testLongBigStrategySize() {
        LongIterator iter;
        iter = new LongBigStrategy().longIterator();
        long len = IndefiniteIteratorUtilities.size(iter);
        assertTrue("Not big enough", 6 <= len);
        assertTrue("Too big", len <= 30);
    }

    /** Test contents of LongStrategy. */
    public void testLongStrategyContents() {
        assertTrue("Missing 0",
                   IndefiniteIteratorUtilities.contains
                   (new LongStrategy().longIterator(),
                    new Long((long)0)));
        assertTrue("Missing 1",
                   IndefiniteIteratorUtilities.contains
                   (new LongStrategy().longIterator(),
                    new Long((long)1)));
        assertTrue("Missing -1",
                   IndefiniteIteratorUtilities.contains
                   (new LongStrategy().longIterator(),
                    new Long((long)-1)));
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (new LongStrategy().longIterator()));
    }

    /** Test contents of LongBigStrategy. */
    public void testLongBigStrategyContents() {
        assertTrue("Missing 0",
                   IndefiniteIteratorUtilities.contains
                   (new LongBigStrategy().longIterator(),
                    new Long((long)0)));
        assertTrue("Missing 1",
                   IndefiniteIteratorUtilities.contains
                   (new LongBigStrategy().longIterator(),
                    new Long((long)1)));
        assertTrue("Missing -1",
                   IndefiniteIteratorUtilities.contains
                   (new LongBigStrategy().longIterator(),
                    new Long((long)-1)));
        assertTrue("Missing smallest value",
                   IndefiniteIteratorUtilities.contains
                   (new LongBigStrategy().longIterator(),
                    new Long(Long.MIN_VALUE)));
        assertTrue("Missing largest value",
                   IndefiniteIteratorUtilities.contains
                   (new LongBigStrategy().longIterator(),
                    new Long(Long.MAX_VALUE)));
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (new LongBigStrategy().longIterator()));
    }

    /** Test freshness of these strategies. */
    public void testLongStrategyFreshness() {
        LongIterator[] iters = new LongIterator[4];
        iters[0] = new LongStrategy().longIterator();
        iters[1] = new LongStrategy().longIterator();
        iters[2] = new LongBigStrategy().longIterator();
        iters[3] = new LongBigStrategy().longIterator();
        for (int i = 0; i < iters.length; i++) {
            assertTrue(iters[i] != null);
            for (int j = i+1; j < iters.length; j++) {
                assertTrue(iters[i] != iters[j]);
            }
        }
    }

    /** Test the empty CompositeStrategy's iterator */
    public void testEmptyComposite() {
        LongStrategyType strat
            = new LongCompositeStrategy(new LongStrategyType[]{});
        LongIterator iter = strat.longIterator();
        assertTrue(iter.atEnd());
    }

    /** Test a singleton CompositeStrategy's iterator */
    public void testSingletonComposite() {
        LongStrategyType strat
            = new LongCompositeStrategy(new LongStrategy());
        assertEquals(IndefiniteIteratorUtilities.size
                     (new LongStrategy().longIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.longIterator()));
    }

    /** Test a pair CompositeStrategy's iterator */
    public void testPairComposite() {
        LongStrategyType strat
            = new LongCompositeStrategy
            (new LongStrategy(),
             new LongBigStrategy());
        assertEquals(IndefiniteIteratorUtilities.size
                     (new LongStrategy().longIterator())
                     + IndefiniteIteratorUtilities.size
                     (new LongBigStrategy().longIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.longIterator()));
    }

    /** Test a larger CompositeStrategy's iterator */
    public void testLargerComposite() {
        LongStrategyType strat
            = new LongCompositeStrategy
            (new LongStrategyType[] {
                new LongStrategy(),
                new LongBigStrategy(),
                new LongStrategy(),
            });
        assertEquals(2 * IndefiniteIteratorUtilities.size
                     (new LongStrategy().longIterator())
                     + IndefiniteIteratorUtilities.size
                     (new LongBigStrategy().longIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.longIterator()));
    }

    /** Test LongNonNegativeStrategyDecorator */
    public void testNonNegativeStrategyDecorator() {
        LongStrategyType strat
            = new LongNonNegativeStrategyDecorator
            (new LongCompositeStrategy
             (new LongStrategyType[] {
                 new LongStrategy(),
                 new LongBigStrategy(),
                 new LongStrategy(),
             }));
        assertFalse(IndefiniteIteratorUtilities.contains
                     (strat.longIterator(),
                      new Long((long)-1)));
    }

}
