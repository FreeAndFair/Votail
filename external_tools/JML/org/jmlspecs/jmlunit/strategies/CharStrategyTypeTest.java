// @(#)$Id: CharStrategyTypeTest.java,v 1.2 2005/07/07 21:03:04 leavens Exp $

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

/** Hand-coded JUnit test for subtypes of CharStrategyType.
 * @author Gary T. Leavens
 */
public class CharStrategyTypeTest extends TestCase
{
    /** Initialize this class. */
    public CharStrategyTypeTest(String name) {
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
            (CharStrategyTypeTest.class);
    }

    /** Test CharStrategy's iterator */
    public void testCharStrategy() {
        CharIterator iter = new CharStrategy().charIterator();
        assertTrue(!iter.atEnd());
        assertEquals('J', iter.getChar());
        assertEquals('J', iter.getChar());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(!iter.atEnd());
        assertEquals('m', iter.getChar());
        assertEquals('m', iter.getChar());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(!iter.atEnd());
        assertEquals(' ', iter.getChar());
        assertEquals(' ', iter.getChar());
        assertTrue(!iter.atEnd());
        iter.advance();
        assertTrue(iter.atEnd());
    }

//     /** Test CharStrategy's iterator by printing it. */
//     public void testCharBigStrategyPrint() {
//         CharIterator iter = new CharBigStrategy().charIterator();
//         System.out.println("");
//         while (!iter.atEnd()) {
//             System.out.print("'" + iter.getChar() + "'");
//             System.out.print(", ");
//             iter.advance();
//         }
//         System.out.println("");
//     }

    /** Test CharBigStrategy's size */
    public void testCharBigStrategySize() {
        CharIterator iter;
        iter = new CharBigStrategy().charIterator();
        long len = IndefiniteIteratorUtilities.size(iter);
        assertTrue("Not big enough", 6 <= len);
        assertTrue("Too big", len <= 30);
    }

    /** Test contents of CharBigStrategy. */
    public void testCharBigStrategyContents() {
        assertTrue("Missing smallest value",
                   IndefiniteIteratorUtilities.contains
                   (new CharBigStrategy().charIterator(),
                    new Character(Character.MIN_VALUE)));
        assertTrue("Missing largest value",
                   IndefiniteIteratorUtilities.contains
                   (new CharBigStrategy().charIterator(),
                    new Character(Character.MAX_VALUE)));
        assertTrue("Duplicate values ",
                   IndefiniteIteratorUtilities.distinctValues
                   (new CharBigStrategy().charIterator()));
    }

    /** Test freshness of these strategies. */
    public void testCharStrategyFreshness() {
        CharIterator[] iters = new CharIterator[4];
        iters[0] = new CharStrategy().charIterator();
        iters[1] = new CharStrategy().charIterator();
        iters[2] = new CharBigStrategy().charIterator();
        iters[3] = new CharBigStrategy().charIterator();
        for (int i = 0; i < iters.length; i++) {
            assertTrue(iters[i] != null);
            for (int j = i+1; j < iters.length; j++) {
                assertTrue(iters[i] != iters[j]);
            }
        }
    }

}
