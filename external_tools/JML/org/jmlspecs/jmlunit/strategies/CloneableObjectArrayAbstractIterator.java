// @(#)$Id: CloneableObjectArrayAbstractIterator.java,v 1.7 2005/12/23 17:02:07 chalin Exp $

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

/** An iterator that provides test data by returning a clone of the
 * current object from an array of cloneable objects passed to its
 * constructor.
 * @see ObjectArrayAbstractIterator
 * @author Gary T. Leavens
 */
public abstract class CloneableObjectArrayAbstractIterator
    extends ObjectArrayAbstractIterator
{
    /** Initialize this iterator to iterate over a clone of the array */
    /*@ public normal_behavior
      @   requires elems != null;
      @   assignable this.elems, next;
      @   ensures next == 0;
      @   ensures (* this.elems is a clone of elems *);
      @   ensures \fresh(this.elems);
      @   ensures_redundantly this.elems != null && this.elems != elems;
      @   ensures this.elems.length == elems.length;
      @*/
    public CloneableObjectArrayAbstractIterator(Object [] elems) {
        super(elems);
    }

    /** Return a clone of the argument, or null if it is null. */
    // specification inherited
    protected /*@ pure nullable @*/ Object duplicateIfNeeded(/*@ nullable @*/ Object elem) {
        if (elem == null) {
            return elem;
        } else {
            return cloneElement(elem);
        }
    }

    /** Return a clone of the argument, which is assumed not to be null. */
    /*@ protected normal_behavior
      @   requires elem != null;
      @   assignable \nothing;
      @   ensures \result != null;
      @   ensures (* \result is a clone of elem *);
      @   ensures_redundantly \result != null;
      @*/
    protected abstract /*@ pure @*/ Object cloneElement(Object elem);
}
