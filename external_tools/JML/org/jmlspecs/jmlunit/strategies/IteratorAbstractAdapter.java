// @(#)$Id: IteratorAbstractAdapter.java,v 1.2 2005/07/07 21:03:04 leavens Exp $

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

/** Make a java.util.Iterator into an IndefiniteIterator.
 * @author Gary T. Leavens
 */
public abstract class IteratorAbstractAdapter implements IndefiniteIterator {

    /** The underlying iterator */
    private /*@ spec_public non_null @*/ Iterator iter;

    /** Initialize this indefinite iterator to iterate over the
     * elements that iter iterates over. */
    /*@ public normal_behavior
      @   requires iter != null;
      @   assignable this.iter, objectState;
      @   ensures (* this.iter is a clone of iter *);
      @*/
    public IteratorAbstractAdapter(Iterator iter) {
        this.iter = cloneIterator(iter);
        if (iter.hasNext()) {
            item = iter.next();
        } else {
            atEnd = true;
        }
    }   

    private boolean atEnd = false; //@ in objectState;
    private Object item;  //@ in objectState;

    // doc comment and specification inherited
    public boolean atEnd() {
        return atEnd;
    }

    // doc comment and specification inherited
    public /*@ pure @*/ Object get() {
        return item;
    }

    // doc comment and specification inherited
    public void advance() {
        if (!atEnd && iter.hasNext()) {
            item = iter.next();
        } else {
            atEnd = true;
        }
    }

    /** Return a clone of this iterator adapter, which contains a
     * clone of the underlying iterator. This has to be done by
     * subclasses. */
    public abstract Object clone();

    /** Return a clone of the argument iterator */
    /*@ protected normal_behavior
      @   assignable \nothing;
      @   ensures \result != null && (* result is a clone of iter *);
      @*/
    protected abstract Iterator cloneIterator(Iterator iter);
}
