// @(#)$Id: NewObjectAbstractIterator.java,v 1.10 2007/12/19 01:59:43 chalin Exp $

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

import java.util.NoSuchElementException;

/** An iterator that provides test data by creating (in general) the
 * objects each time the get() method is called.  The idea is to
 * track a number for what item to return, and to pass that to a
 * "make" method which creates the required object, or throws an
 * exception if there are no more.
 * <p>
 * If you want to have aliasing, arrange it so that the same object is
 * returned multiple times by the get() method.
 * <p>
 * This can only handle iterations up to Integer.MAX_VALUE elements.
 *
 * @author Gary T. Leavens
 */
public abstract class NewObjectAbstractIterator implements IndefiniteIterator {

    /** Is this iteration at it's end? */
    private boolean atEnd = false;  //@ in objectState;

    /** The number of the current data item to return. */
    private int cursor = 0; //@ in objectState;

    /** Initialize this iterator.  This must be called if the iterator
     * can start off at its end, which is unusual but possible.
     * @see NewObjectAbstractStrategy
     */
    //@ assignable objectState;
    public void initialize() {
        // initialize atEnd
        try {
            make(0);
            atEnd = false;
        } catch (NoSuchElementException e) {
            atEnd = true;
        }
    }

    // doc comment and specification inherited
    public void advance() {
        // can't handle more than Integer.MAX_VALUE items
        if (cursor == Integer.MAX_VALUE) {
            atEnd = true;
        } else {
            cursor++;
            try {
                make(cursor);
            } catch (NoSuchElementException e) {
                atEnd = true;
            }
        }
    }

    // doc comment and specification inherited
    public /*@ pure @*/ boolean atEnd() {
        return atEnd;
    }

    // doc comment and specification inherited
    public /*@pure*/ /*@nullable*/ Object get() {
        return make(cursor);
    }

    /** Return the nth test data item. */
    /*@ public behavior
      @   requires 0 <= n;
      @   assignable \nothing;
      @   signals_only NoSuchElementException;
      @*/
    public /*@pure*//*@nullable*/ abstract Object make(int n);

    // doc comment and specification inherited
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            //@ unreachable;
            throw new InternalError(e.toString());
        }
    }

}
