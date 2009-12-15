// @(#)$Id: IndefiniteIteratorUtilities.java,v 1.3 2005/07/07 21:03:04 leavens Exp $

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

import java.util.*;

/** Static functions to aid in testing subtypes of {@link IndefiniteIterator}
 * and hence, the testing of various strategies.
 * @author Gary T. Leavens
 */
public class IndefiniteIteratorUtilities
{
    /** No instances of this class */
    private IndefiniteIteratorUtilities() { }

    /** Return the size of the given indefinite iterator */
    //@ requires iter != null;
    //@ assignable iter.objectState;
    public static long size(IndefiniteIterator iter)
    {
        iter = (IndefiniteIterator)iter.clone();
        long count = 0L;
        while (count < Long.MAX_VALUE && !iter.atEnd()) {
            count++;
            iter.advance();
        }
        if (count == Long.MAX_VALUE) {
            throw new InternalError("Can't count more than Long.MAX_VALUE!");
        }
        return count;
    }

    /** Does the given iterator return something equals to the given
     * object? */
    //@ requires iter != null && o != null;
    //@ assignable iter.objectState;
    public static boolean contains(IndefiniteIterator iter, Object o) {
        boolean found = false;
        while (!iter.atEnd()) {
            if (o.equals(iter.get())) {
                return true;
            }
            iter.advance();
        }
        return false;
    }

    /** Does the given iterator return null? */
    //@ requires iter != null;
    //@ assignable iter.objectState;
    public static boolean containsNull(IndefiniteIterator iter) {
        boolean found = false;
        while (!iter.atEnd()) {
            if (iter.get() == null) {
                return true;
            }
            iter.advance();
        }
        return false;
    }

    /** Does the given iterator have distinct values it returns? */
    //@ requires iter != null;
    //@ assignable iter.objectState;
    public static boolean distinctValues(IndefiniteIterator iter) {
        HashSet s = new HashSet();
        while (!iter.atEnd()) {
            if (s.contains(iter.get())) {
                // System.out.println("duplicate is: " + iter.get());
                return false;
            } else {
                s.add(iter.get());
            }
            iter.advance();
        }
        return true;
    }

}
