// @(#)$Id: intStrategyTypeTest.java-generic,v 1.5 2005/12/06 19:54:59 chalin Exp $

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

/** Hand-coded JUnit test for subtypes of IntStrategyType.
 * @author Gary T. Leavens
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class IntStrategyTypeTest extends TestCase
{
    /** Initialize this class. */
    public IntStrategyTypeTest(String name) {
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
            (IntStrategyTypeTest.class);
    }

//     /** Test IntStrategy's iterator by printing it. */
//     public void testIntBigStrategyPrint() {
//         IntIterator iter = new IntBigStrategy().intIterator();
//         System.out.println("");
//         while (!iter.atEnd()) {
//             System.out.print("'" + iter.getInt() + "'");
//             System.out.print(", ");
//             iter.advance();
//         }
//         System.out.println("");
//     }

    /** Test IntStrategy's size */
    public void testIntStrategySize() {
        IntIterator iter;
        iter = new IntStrategy().intIterator();
        long len = IndefiniteIteratorUtilities.size(iter);
        assertTrue("Not big enough", 1 <= len);
        assertTrue("Too big", len <= 5);
    }

    /** Test IntBigStrategy's size */
    public void testIntBigStrategySize() {
        IntIterator iter;
        iter = new IntBigStrategy().intIterator();
        long len = IndefiniteIteratorUtilities.size(iter);
        assertTrue("Not big enough", 6 <= len);
        assertTrue("Too big", len <= 30);
    }

    /** Test contents of IntStrategy. */
    public void testIntStrategyContents() {
        assertTrue("Missing 0",
                   IndefiniteIteratorUtilities.contains
                   (new IntStrategy().intIterator(),
                    new Integer((int)0)));
        assertTrue("Missing 1",
                   IndefiniteIteratorUtilities.contains
                   (new IntStrategy().intIterator(),
                    new Integer((int)1)));
        assertTrue("Missing -1",
                   IndefiniteIteratorUtilities.contains
                   (new IntStrategy().intIterator(),
                    new Integer((int)-1)));
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (new IntStrategy().intIterator()));
    }

    /** Test contents of IntBigStrategy. */
    public void testIntBigStrategyContents() {
        assertTrue("Missing 0",
                   IndefiniteIteratorUtilities.contains
                   (new IntBigStrategy().intIterator(),
                    new Integer((int)0)));
        assertTrue("Missing 1",
                   IndefiniteIteratorUtilities.contains
                   (new IntBigStrategy().intIterator(),
                    new Integer((int)1)));
        assertTrue("Missing -1",
                   IndefiniteIteratorUtilities.contains
                   (new IntBigStrategy().intIterator(),
                    new Integer((int)-1)));
        assertTrue("Missing smallest value",
                   IndefiniteIteratorUtilities.contains
                   (new IntBigStrategy().intIterator(),
                    new Integer(Integer.MIN_VALUE)));
        assertTrue("Missing largest value",
                   IndefiniteIteratorUtilities.contains
                   (new IntBigStrategy().intIterator(),
                    new Integer(Integer.MAX_VALUE)));
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (new IntBigStrategy().intIterator()));
    }

    /** Test freshness of these strategies. */
    public void testIntStrategyFreshness() {
        IntIterator[] iters = new IntIterator[4];
        iters[0] = new IntStrategy().intIterator();
        iters[1] = new IntStrategy().intIterator();
        iters[2] = new IntBigStrategy().intIterator();
        iters[3] = new IntBigStrategy().intIterator();
        for (int i = 0; i < iters.length; i++) {
            assertTrue(iters[i] != null);
            for (int j = i+1; j < iters.length; j++) {
                assertTrue(iters[i] != iters[j]);
            }
        }
    }

    /** Test the empty CompositeStrategy's iterator */
    public void testEmptyComposite() {
        IntStrategyType strat
            = new IntCompositeStrategy(new IntStrategyType[]{});
        IntIterator iter = strat.intIterator();
        assertTrue(iter.atEnd());
    }

    /** Test a singleton CompositeStrategy's iterator */
    public void testSingletonComposite() {
        IntStrategyType strat
            = new IntCompositeStrategy(new IntStrategy());
        assertEquals(IndefiniteIteratorUtilities.size
                     (new IntStrategy().intIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.intIterator()));
    }

    /** Test a pair CompositeStrategy's iterator */
    public void testPairComposite() {
        IntStrategyType strat
            = new IntCompositeStrategy
            (new IntStrategy(),
             new IntBigStrategy());
        assertEquals(IndefiniteIteratorUtilities.size
                     (new IntStrategy().intIterator())
                     + IndefiniteIteratorUtilities.size
                     (new IntBigStrategy().intIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.intIterator()));
    }

    /** Test a larger CompositeStrategy's iterator */
    public void testLargerComposite() {
        IntStrategyType strat
            = new IntCompositeStrategy
            (new IntStrategyType[] {
                new IntStrategy(),
                new IntBigStrategy(),
                new IntStrategy(),
            });
        assertEquals(2 * IndefiniteIteratorUtilities.size
                     (new IntStrategy().intIterator())
                     + IndefiniteIteratorUtilities.size
                     (new IntBigStrategy().intIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.intIterator()));
    }

    /** Test IntNonNegativeStrategyDecorator */
    public void testNonNegativeStrategyDecorator() {
        IntStrategyType strat
            = new IntNonNegativeStrategyDecorator
            (new IntCompositeStrategy
             (new IntStrategyType[] {
                 new IntStrategy(),
                 new IntBigStrategy(),
                 new IntStrategy(),
             }));
        assertFalse(IndefiniteIteratorUtilities.contains
                     (strat.intIterator(),
                      new Integer((int)-1)));
    }

}
