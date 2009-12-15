// @(#)$Id: doubleStrategyTypeTest.java-generic,v 1.5 2005/12/06 19:54:59 chalin Exp $

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

/** Hand-coded JUnit test for subtypes of DoubleStrategyType.
 * @author Gary T. Leavens
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class DoubleStrategyTypeTest extends TestCase
{
    /** Initialize this class. */
    public DoubleStrategyTypeTest(String name) {
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
            (DoubleStrategyTypeTest.class);
    }

//     /** Test DoubleStrategy's iterator by printing it. */
//     public void testDoubleBigStrategyPrint() {
//         DoubleIterator iter = new DoubleBigStrategy().doubleIterator();
//         System.out.println("");
//         while (!iter.atEnd()) {
//             System.out.print("'" + iter.getDouble() + "'");
//             System.out.print(", ");
//             iter.advance();
//         }
//         System.out.println("");
//     }

    /** Test DoubleStrategy's size */
    public void testDoubleStrategySize() {
        DoubleIterator iter;
        iter = new DoubleStrategy().doubleIterator();
        long len = IndefiniteIteratorUtilities.size(iter);
        assertTrue("Not big enough", 1 <= len);
        assertTrue("Too big", len <= 5);
    }

    /** Test DoubleBigStrategy's size */
    public void testDoubleBigStrategySize() {
        DoubleIterator iter;
        iter = new DoubleBigStrategy().doubleIterator();
        long len = IndefiniteIteratorUtilities.size(iter);
        assertTrue("Not big enough", 6 <= len);
        assertTrue("Too big", len <= 30);
    }

    /** Test contents of DoubleStrategy. */
    public void testDoubleStrategyContents() {
        assertTrue("Missing 0",
                   IndefiniteIteratorUtilities.contains
                   (new DoubleStrategy().doubleIterator(),
                    new Double((double)0)));
        assertTrue("Missing 1",
                   IndefiniteIteratorUtilities.contains
                   (new DoubleStrategy().doubleIterator(),
                    new Double((double)1)));
        assertTrue("Missing -1",
                   IndefiniteIteratorUtilities.contains
                   (new DoubleStrategy().doubleIterator(),
                    new Double((double)-1)));
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (new DoubleStrategy().doubleIterator()));
    }

    /** Test contents of DoubleBigStrategy. */
    public void testDoubleBigStrategyContents() {
        assertTrue("Missing 0",
                   IndefiniteIteratorUtilities.contains
                   (new DoubleBigStrategy().doubleIterator(),
                    new Double((double)0)));
        assertTrue("Missing 1",
                   IndefiniteIteratorUtilities.contains
                   (new DoubleBigStrategy().doubleIterator(),
                    new Double((double)1)));
        assertTrue("Missing -1",
                   IndefiniteIteratorUtilities.contains
                   (new DoubleBigStrategy().doubleIterator(),
                    new Double((double)-1)));
        assertTrue("Missing smallest value",
                   IndefiniteIteratorUtilities.contains
                   (new DoubleBigStrategy().doubleIterator(),
                    new Double(Double.MIN_VALUE)));
        assertTrue("Missing largest value",
                   IndefiniteIteratorUtilities.contains
                   (new DoubleBigStrategy().doubleIterator(),
                    new Double(Double.MAX_VALUE)));
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (new DoubleBigStrategy().doubleIterator()));
    }

    /** Test freshness of these strategies. */
    public void testDoubleStrategyFreshness() {
        DoubleIterator[] iters = new DoubleIterator[4];
        iters[0] = new DoubleStrategy().doubleIterator();
        iters[1] = new DoubleStrategy().doubleIterator();
        iters[2] = new DoubleBigStrategy().doubleIterator();
        iters[3] = new DoubleBigStrategy().doubleIterator();
        for (int i = 0; i < iters.length; i++) {
            assertTrue(iters[i] != null);
            for (int j = i+1; j < iters.length; j++) {
                assertTrue(iters[i] != iters[j]);
            }
        }
    }

    /** Test the empty CompositeStrategy's iterator */
    public void testEmptyComposite() {
        DoubleStrategyType strat
            = new DoubleCompositeStrategy(new DoubleStrategyType[]{});
        DoubleIterator iter = strat.doubleIterator();
        assertTrue(iter.atEnd());
    }

    /** Test a singleton CompositeStrategy's iterator */
    public void testSingletonComposite() {
        DoubleStrategyType strat
            = new DoubleCompositeStrategy(new DoubleStrategy());
        assertEquals(IndefiniteIteratorUtilities.size
                     (new DoubleStrategy().doubleIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.doubleIterator()));
    }

    /** Test a pair CompositeStrategy's iterator */
    public void testPairComposite() {
        DoubleStrategyType strat
            = new DoubleCompositeStrategy
            (new DoubleStrategy(),
             new DoubleBigStrategy());
        assertEquals(IndefiniteIteratorUtilities.size
                     (new DoubleStrategy().doubleIterator())
                     + IndefiniteIteratorUtilities.size
                     (new DoubleBigStrategy().doubleIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.doubleIterator()));
    }

    /** Test a larger CompositeStrategy's iterator */
    public void testLargerComposite() {
        DoubleStrategyType strat
            = new DoubleCompositeStrategy
            (new DoubleStrategyType[] {
                new DoubleStrategy(),
                new DoubleBigStrategy(),
                new DoubleStrategy(),
            });
        assertEquals(2 * IndefiniteIteratorUtilities.size
                     (new DoubleStrategy().doubleIterator())
                     + IndefiniteIteratorUtilities.size
                     (new DoubleBigStrategy().doubleIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.doubleIterator()));
    }

    /** Test DoubleNonNegativeStrategyDecorator */
    public void testNonNegativeStrategyDecorator() {
        DoubleStrategyType strat
            = new DoubleNonNegativeStrategyDecorator
            (new DoubleCompositeStrategy
             (new DoubleStrategyType[] {
                 new DoubleStrategy(),
                 new DoubleBigStrategy(),
                 new DoubleStrategy(),
             }));
        assertFalse(IndefiniteIteratorUtilities.contains
                     (strat.doubleIterator(),
                      new Double((double)-1)));
    }

}
