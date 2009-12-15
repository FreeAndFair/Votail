// @(#)$Id: byteStrategyTypeTest.java-generic,v 1.5 2005/12/06 19:54:59 chalin Exp $

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

/** Hand-coded JUnit test for subtypes of ByteStrategyType.
 * @author Gary T. Leavens
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class ByteStrategyTypeTest extends TestCase
{
    /** Initialize this class. */
    public ByteStrategyTypeTest(String name) {
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
            (ByteStrategyTypeTest.class);
    }

//     /** Test ByteStrategy's iterator by printing it. */
//     public void testByteBigStrategyPrint() {
//         ByteIterator iter = new ByteBigStrategy().byteIterator();
//         System.out.println("");
//         while (!iter.atEnd()) {
//             System.out.print("'" + iter.getByte() + "'");
//             System.out.print(", ");
//             iter.advance();
//         }
//         System.out.println("");
//     }

    /** Test ByteStrategy's size */
    public void testByteStrategySize() {
        ByteIterator iter;
        iter = new ByteStrategy().byteIterator();
        long len = IndefiniteIteratorUtilities.size(iter);
        assertTrue("Not big enough", 1 <= len);
        assertTrue("Too big", len <= 5);
    }

    /** Test ByteBigStrategy's size */
    public void testByteBigStrategySize() {
        ByteIterator iter;
        iter = new ByteBigStrategy().byteIterator();
        long len = IndefiniteIteratorUtilities.size(iter);
        assertTrue("Not big enough", 6 <= len);
        assertTrue("Too big", len <= 30);
    }

    /** Test contents of ByteStrategy. */
    public void testByteStrategyContents() {
        assertTrue("Missing 0",
                   IndefiniteIteratorUtilities.contains
                   (new ByteStrategy().byteIterator(),
                    new Byte((byte)0)));
        assertTrue("Missing 1",
                   IndefiniteIteratorUtilities.contains
                   (new ByteStrategy().byteIterator(),
                    new Byte((byte)1)));
        assertTrue("Missing -1",
                   IndefiniteIteratorUtilities.contains
                   (new ByteStrategy().byteIterator(),
                    new Byte((byte)-1)));
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (new ByteStrategy().byteIterator()));
    }

    /** Test contents of ByteBigStrategy. */
    public void testByteBigStrategyContents() {
        assertTrue("Missing 0",
                   IndefiniteIteratorUtilities.contains
                   (new ByteBigStrategy().byteIterator(),
                    new Byte((byte)0)));
        assertTrue("Missing 1",
                   IndefiniteIteratorUtilities.contains
                   (new ByteBigStrategy().byteIterator(),
                    new Byte((byte)1)));
        assertTrue("Missing -1",
                   IndefiniteIteratorUtilities.contains
                   (new ByteBigStrategy().byteIterator(),
                    new Byte((byte)-1)));
        assertTrue("Missing smallest value",
                   IndefiniteIteratorUtilities.contains
                   (new ByteBigStrategy().byteIterator(),
                    new Byte(Byte.MIN_VALUE)));
        assertTrue("Missing largest value",
                   IndefiniteIteratorUtilities.contains
                   (new ByteBigStrategy().byteIterator(),
                    new Byte(Byte.MAX_VALUE)));
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (new ByteBigStrategy().byteIterator()));
    }

    /** Test freshness of these strategies. */
    public void testByteStrategyFreshness() {
        ByteIterator[] iters = new ByteIterator[4];
        iters[0] = new ByteStrategy().byteIterator();
        iters[1] = new ByteStrategy().byteIterator();
        iters[2] = new ByteBigStrategy().byteIterator();
        iters[3] = new ByteBigStrategy().byteIterator();
        for (int i = 0; i < iters.length; i++) {
            assertTrue(iters[i] != null);
            for (int j = i+1; j < iters.length; j++) {
                assertTrue(iters[i] != iters[j]);
            }
        }
    }

    /** Test the empty CompositeStrategy's iterator */
    public void testEmptyComposite() {
        ByteStrategyType strat
            = new ByteCompositeStrategy(new ByteStrategyType[]{});
        ByteIterator iter = strat.byteIterator();
        assertTrue(iter.atEnd());
    }

    /** Test a singleton CompositeStrategy's iterator */
    public void testSingletonComposite() {
        ByteStrategyType strat
            = new ByteCompositeStrategy(new ByteStrategy());
        assertEquals(IndefiniteIteratorUtilities.size
                     (new ByteStrategy().byteIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.byteIterator()));
    }

    /** Test a pair CompositeStrategy's iterator */
    public void testPairComposite() {
        ByteStrategyType strat
            = new ByteCompositeStrategy
            (new ByteStrategy(),
             new ByteBigStrategy());
        assertEquals(IndefiniteIteratorUtilities.size
                     (new ByteStrategy().byteIterator())
                     + IndefiniteIteratorUtilities.size
                     (new ByteBigStrategy().byteIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.byteIterator()));
    }

    /** Test a larger CompositeStrategy's iterator */
    public void testLargerComposite() {
        ByteStrategyType strat
            = new ByteCompositeStrategy
            (new ByteStrategyType[] {
                new ByteStrategy(),
                new ByteBigStrategy(),
                new ByteStrategy(),
            });
        assertEquals(2 * IndefiniteIteratorUtilities.size
                     (new ByteStrategy().byteIterator())
                     + IndefiniteIteratorUtilities.size
                     (new ByteBigStrategy().byteIterator()),
                     IndefiniteIteratorUtilities.size
                     (strat.byteIterator()));
    }

    /** Test ByteNonNegativeStrategyDecorator */
    public void testNonNegativeStrategyDecorator() {
        ByteStrategyType strat
            = new ByteNonNegativeStrategyDecorator
            (new ByteCompositeStrategy
             (new ByteStrategyType[] {
                 new ByteStrategy(),
                 new ByteBigStrategy(),
                 new ByteStrategy(),
             }));
        assertFalse(IndefiniteIteratorUtilities.contains
                     (strat.byteIterator(),
                      new Byte((byte)-1)));
    }

}
