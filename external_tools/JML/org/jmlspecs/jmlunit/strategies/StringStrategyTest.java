// @(#)$Id: StringStrategyTest.java,v 1.3 2005/07/07 21:03:05 leavens Exp $

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

/** Hand-coded JUnit test for testing StringStrategy.
 * @author Gary T. Leavens
 */
public class StringStrategyTest extends TestCase
{
    /** Initialize this class. */
    public StringStrategyTest(String name) {
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
            (StringStrategyTest.class);
    }

    /** Test StringStrategy's iterator */
    public void testStringStrategy() {
        IndefiniteIterator iter = new StringStrategy().iterator();
        assertTrue(!iter.atEnd());
        assertEquals(null, iter.get());
        assertEquals(null, iter.get());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(!iter.atEnd());
        assertEquals("", iter.get());
        assertEquals("", iter.get());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(iter.atEnd());
    }

    /** Test freshness of this strategy. */
    public void testStringStrategyFreshness() {
        IndefiniteIterator[] iters = new IndefiniteIterator[2];
        iters[0] = new StringStrategy().iterator();
        iters[1] = new StringStrategy().iterator();
        for (int i = 0; i < iters.length; i++) {
            assertTrue(iters[i] != null);
            for (int j = i+1; j < iters.length; j++) {
                assertTrue(iters[i] != iters[j]);
            }
        }
    }

    /** Test extension of this strategy. */
    public void testStringStrategyExtension() {
        final String str1 = "an added String 123$#$&^";
        final String str2 = "a second added String 324115141";
        StrategyType strat = new StringStrategy() {
                protected Object[] addData() {
                    return new Object[] { str1, str2, };
                }
            };
        assertTrue(IndefiniteIteratorUtilities.contains
                   (strat.iterator(), str1));
        assertTrue(IndefiniteIteratorUtilities.contains
                   (strat.iterator(), str2));
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (strat.iterator()));
        assertEquals
            (IndefiniteIteratorUtilities.size(new StringStrategy().iterator())
             + 2,
             IndefiniteIteratorUtilities.size(strat.iterator()));
    }
}
