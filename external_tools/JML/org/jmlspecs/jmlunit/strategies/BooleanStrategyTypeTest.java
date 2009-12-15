// @(#)$Id: BooleanStrategyTypeTest.java,v 1.3 2005/07/07 21:03:04 leavens Exp $

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

/** Hand-coded JUnit test for subtypes of BooleanStrategyType.  (Of
 * course, there's really only one such strategy, as
 * BooleanBigStrategy is in essence the same as BooleanStrategy.)
 * @author Gary T. Leavens
 */
public class BooleanStrategyTypeTest extends TestCase
{
    /** Initialize this class. */
    public BooleanStrategyTypeTest(String name) {
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
            (BooleanStrategyTypeTest.class);
    }

    /** Test BooleanStrategy's iterator */
    public void testBooleanStrategy() {
        checkBooleanIterator(new BooleanStrategy().booleanIterator());
    }

    /** Test BooleanStrategy's iterator */
    public void testBooleanBigStrategy() {
        checkBooleanIterator(new BooleanBigStrategy().booleanIterator());
    }

    /** Check for the expected values in the iterator. */
    //@ requires iter != null;
    protected void checkBooleanIterator(BooleanIterator iter) {
        assertTrue(iter != null);
        assertTrue(!iter.atEnd());
        assertEquals(false, iter.getBoolean());
        assertEquals(false, iter.getBoolean());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(!iter.atEnd());
        assertEquals(true, iter.getBoolean());
        assertEquals(true, iter.getBoolean());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(iter.atEnd());
    }

    /** Test freshness of these strategies. */
    public void testBooleanStrategyFreshness() {
        BooleanIterator[] iters = new BooleanIterator[4];
        iters[0] = new BooleanStrategy().booleanIterator();
        iters[1] = new BooleanStrategy().booleanIterator();
        iters[2] = new BooleanBigStrategy().booleanIterator();
        iters[3] = new BooleanBigStrategy().booleanIterator();
        for (int i = 0; i < iters.length; i++) {
            assertTrue(iters[i] != null);
            for (int j = i+1; j < iters.length; j++) {
                assertTrue(iters[i] != iters[j]);
            }
        }
    }

}
