// @(#)$Id: floatStrategyTypeTest.java-generic,v 1.5 2005/12/06 19:54:59 chalin Exp $

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

/** Hand-coded JUnit test for subtypes of FloatStrategyType.
 * @author Gary T. Leavens
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class FloatStrategyTypeTest extends TestCase
{
    /** Initialize this class. */
    public FloatStrategyTypeTest(String name) {
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
            (FloatStrategyTypeTest.class);
    }

//     /** Test FloatStrategy's iterator by printing it. */
//     public void testFloatBigStrategyPrint() {
//         FloatIterator iter = new FloatBigStrategy().floatIterator();
//         System.out.println("");
//         while (!iter.atEnd()) {
//             System.out.print("'" + iter.getFloat() + "'");
//             System.out.print(", ");
//             iter.advance();
//         }
//         System.out.println("");
//     }

    /** Test FloatStrategy's size */
    public void testFloatStrategySize() {
        FloatIterator iter;
        iter = new FloatStrategy().floatIterator();
        long len = IndefiniteIteratorUtilities.size(iter);
        assertTrue("Not big enough", 1 <= len);
        assertTrue("Too big", len <= 5);
    }

    /** Test FloatBigStrategy's size */
    public void testFloatBigStrategySize() {
        FloatIterator iter;
        iter = new FloatBigStrategy().floatIterator();
        long len = IndefiniteIteratorUtilities.size(iter);
        assertTrue("Not big enough", 6 <= len);
        assertTrue("Too big", len <= 30);
    }

    /** Test contents of FloatStrategy. */
    public void testFloatStrategyContents() {
        assertTrue("Missing 0",
                   IndefiniteIteratorUtilities.contains
                   (new FloatStrategy().floatIterator(),
                    new Float((float)0)));
        assertTrue("Missing 1",
                   IndefiniteIteratorUtilities.contains
                   (new FloatStrategy().floatIterator(),
                    new Float((float)1)));
        assertTrue("Missing -1",
                   IndefiniteIteratorUtilities.contains
                   (new FloatStrategy().floatIterator(),
                    new Float((float)-1)));
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (new FloatStrategy().floatIterator()));
    }

    /** Test contents of FloatBigStrategy. */
    public void testFloatBigStrategyContents() {
        assertTrue("Missing 0",
                   IndefiniteIteratorUtilities.contains
                   (new FloatBigStrategy().floatIterator(),
                    new Float((float)0)));
        assertTrue("Missing 1",
                   IndefiniteIteratorUtilities.contains
                   (new FloatBigStrategy().floatIterator(),
                    new Float((float)1)));
        assertTrue("Missing -1",
                   IndefiniteIteratorUtilities.contains
                   (new FloatBigStrategy().floatIterator(),
                    new Float((float)-1)));
        assertTrue("Missing smallest value",
                   IndefiniteIteratorUtilities.contains
                   (new FloatBigStrategy().floatIterator(),
                    new Float(Float.MIN_VALUE)));
        assertTrue("Missing largest value",
                   IndefiniteIteratorUtilities.contains
                   (new FloatBigStrategy().floatIterator(),
                    new Float(Float.MAX_VALUE)));
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (new FloatBigStrategy().floatIterator()));
    }

    /** Test freshness of these strategies. */
    public void testFloatStrategyFreshness() {
        FloatIterator[] iters = new FloatIterator[4];
        iters[0] = new FloatStrategy().floatIterator();
        iters[1] = new FloatStrategy().floatIterator();
        iters[2] = new FloatBigStrategy().floatIterator();
        iters[3] = new FloatBigStrategy().floatIterator();
        for (int i = 0; i < iters.length; i++) {
            assertTrue(iters[i] != null);
            for (int j = i+1; j < iters.length; j++) {
                assertTrue(iters[i] != iters[j]);
            }
        }
    }

    /** Test the empty CompositeStrategy's iterator */
    public void testEmptyComposite() {
        FloatStrategyType strat
            = new FloatCompositeStrategy(new FloatStrategyType[]{});
        FloatIterator iter = strat.floatIterator();
        assertTrue(iter.atEnd());
    }

    /** Test a singleton CompositeStrategy's iterator */
    public void testSingletonComposite() {
        FloatStrategyType strat
            = new FloatCompositeStrategy(new FloatStrategy());
        assertEquals(IndefiniteIteratorUtilities.size
                     (new FloatStrategy().floatIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.floatIterator()));
    }

    /** Test a pair CompositeStrategy's iterator */
    public void testPairComposite() {
        FloatStrategyType strat
            = new FloatCompositeStrategy
            (new FloatStrategy(),
             new FloatBigStrategy());
        assertEquals(IndefiniteIteratorUtilities.size
                     (new FloatStrategy().floatIterator())
                     + IndefiniteIteratorUtilities.size
                     (new FloatBigStrategy().floatIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.floatIterator()));
    }

    /** Test a larger CompositeStrategy's iterator */
    public void testLargerComposite() {
        FloatStrategyType strat
            = new FloatCompositeStrategy
            (new FloatStrategyType[] {
                new FloatStrategy(),
                new FloatBigStrategy(),
                new FloatStrategy(),
            });
        assertEquals(2 * IndefiniteIteratorUtilities.size
                     (new FloatStrategy().floatIterator())
                     + IndefiniteIteratorUtilities.size
                     (new FloatBigStrategy().floatIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.floatIterator()));
    }

    /** Test FloatNonNegativeStrategyDecorator */
    public void testNonNegativeStrategyDecorator() {
        FloatStrategyType strat
            = new FloatNonNegativeStrategyDecorator
            (new FloatCompositeStrategy
             (new FloatStrategyType[] {
                 new FloatStrategy(),
                 new FloatBigStrategy(),
                 new FloatStrategy(),
             }));
        assertFalse(IndefiniteIteratorUtilities.contains
                     (strat.floatIterator(),
                      new Float((float)-1)));
    }

}
