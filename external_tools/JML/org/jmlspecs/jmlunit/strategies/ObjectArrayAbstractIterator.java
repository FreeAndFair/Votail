// @(#)$Id: ObjectArrayAbstractIterator.java,v 1.12 2005/12/23 17:02:07 chalin Exp $

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
//@ model import org.jmlspecs.models.JMLNullSafe;

/** An indefinite iterator that provides test data from an array of
 * objects passed to its constructor.
 *
 * <p>
 * This can only handle iterations up to Integer.MAX_VALUE elements.
 *
 * @author Gary T. Leavens
 */
public abstract class ObjectArrayAbstractIterator
    implements IndefiniteIterator
{
    /** The next element's index (zero based) */
    private /*@ spec_public @*/ int next = 0;  //@ in objectState;

    /** The elements */
    private /*@ spec_public non_null @*/ Object[] elems;  //@ in objectState;

    //@ public invariant 0 <= next && next <= elems.length;

    /** Initialize this iterator to iterate over a clone of the array */
    /*@ public normal_behavior
      @   requires elems != null;
      @   assignable this.elems, next;
      @   ensures next == 0 && Arrays.equals(elems, this.elems);
      @   ensures \fresh(this.elems);
      @   ensures_redundantly this.elems != null && this.elems != elems;
      @   ensures_redundantly this.elems.length == elems.length;
      @*/
    public ObjectArrayAbstractIterator(Object[] elems) {
        this.elems = (Object[]) elems.clone();
    }

    // doc comment inherited
    /*@ also
      @   public normal_behavior
      @    ensures \result <==> !(next < elems.length);
      @*/
    public /*@ pure @*/ boolean atEnd() {
        return !(next < elems.length);
    }

    // doc comment inherited
    /*@ also
      @   public normal_behavior
      @    requires next < elems.length;
      @    assignable \nothing;
      @ also
      @   public exceptional_behavior
      @     requires next >= elems.length;
      @     assignable \nothing;
      @     signals_only NoSuchElementException;
      @*/
    public /*@ pure nullable @*/ Object get() {
        if (next < elems.length) {
            return duplicateIfNeeded(elems[next]);
        } else {
            throw new NoSuchElementException();
        }
    }

    /** Duplicate the argument if needed.  This is a hook for subclasses.
     * @param elem the object to perhaps be duplicated, which may be null
     */
    /*@  public normal_behavior
      @    assignable \nothing;
      @*/
    protected abstract /*@ spec_public pure @*/
    /*@ nullable @*/ Object duplicateIfNeeded(/*@ nullable @*/ Object elem);

    /*@ also
      @ public normal_behavior
      @    requires next < elems.length;
      @    assignable next;
      @    ensures next == \old(next + 1);
      @ also
      @ public normal_behavior
      @    requires next == elems.length;
      @    assignable \nothing;
      @*/
    public void advance() {
        if (next < elems.length) {
            next++;
        }
    }

    // doc comment and specification inherited
    public Object clone() {
        try {
           ObjectArrayAbstractIterator ret
               = (ObjectArrayAbstractIterator) super.clone();
            ret.elems = (Object[]) elems.clone();
            return ret;
        } catch (CloneNotSupportedException e) {
            //@ unreachable;
            throw new InternalError(e.toString());
        }
    }

    public String toString() {
        return "ObjectArrayAbstractIterator(" + next + ","
            + elementsString() + ")";
    }

    //@ ensures \result != null;
    protected /*@ pure @*/ String elementsString() {
        String ret = "Object[] {";
        for (int i = 0; i < elems.length; i++) {
            ret += elems[i];
            ret += ",";
        }
        ret += "}";
        return ret;
    }
}
