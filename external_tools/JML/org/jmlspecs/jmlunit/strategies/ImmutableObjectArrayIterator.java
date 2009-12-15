// @(#)$Id: ImmutableObjectArrayIterator.java,v 1.9 2005/12/23 17:02:07 chalin Exp $

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

import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Arrays;

/** An iterator that provides test data by returning the current object from
 * an array of immutable objects passed to its constructor.
 *
 * <p>
 * This can only handle iterations up to Integer.MAX_VALUE elements.
 *
 * @author Gary T. Leavens
 */
public class ImmutableObjectArrayIterator
    extends ObjectArrayAbstractIterator
{
    /** Initialize this iterator to iterate over a clone of the array */
    /*@ public normal_behavior
      @   assignable this.elems, next;
      @   ensures next == 0;
      @   ensures (* this.elems is a clone of elems *);
      @   ensures \fresh(this.elems);
      @   ensures_redundantly this.elems != null && this.elems != elems;
      @   ensures this.elems.length == elems.length;
      @*/
    public ImmutableObjectArrayIterator(Object [] elems) {
        super(elems);
    }

    /** Return the argument (which is presumed to be immutable, and
     * therefore not cloned). */
    /*@ also
      @  protected normal_behavior
      @    assignable \nothing;
      @    ensures \result == elems[next];
      @*/
    protected /*@ pure nullable @*/ Object duplicateIfNeeded(/*@ nullable @*/ Object elem) {
        return elem;
    }
}
