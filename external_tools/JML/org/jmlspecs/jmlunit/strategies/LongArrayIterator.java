// @(#)$Id: longArrayIterator.java-generic,v 1.9 2005/12/24 21:20:31 chalin Exp $

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
import java.util.Arrays;

/** A LongIterator over arrays of long elements.
 * @author Gary T. Leavens
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class LongArrayIterator
    extends LongAbstractIterator
{

    /** The next element's index (zero based) */
    private /*@ spec_public @*/ int next = 0;  //@ in objectState;

    /** The elements */
    private /*@ spec_public non_null @*/ long[] elems;

    //@ public invariant 0 <= next && next <= elems.length;

    /** Initialize this iterator to iterate over a clone of the array */
    /*@ public normal_behavior
      @   assignable this.elems, next;
      @   ensures next == 0 && Arrays.equals(elems, this.elems);
      @*/
    public LongArrayIterator(/*@ non_null @*/ long[] elems) {
        this.elems = (long[]) elems.clone();
    }

    /** Initialize this iterator to iterate over a clone of the array,
     * starting at the given next index */
    /*@ protected normal_behavior
      @   requires 0 <= next && next <= elems.length;
      @   assignable this.elems, this.next;
      @   ensures this.next == next && Arrays.equals(elems, this.elems);
      @*/
    protected LongArrayIterator
        (int next, /*@ non_null @*/ long[] elems)
    {
        this.elems = (long[]) elems.clone();
        this.next = next;
    }

    // doc comment inherited
    /*@ also
      @   public normal_behavior
      @    ensures \result <==> !(next < elems.length);
      @ implies_that
      @   public normal_behavior
      @    ensures !\result <==> next == elems.length;
      @*/
    public /*@ pure @*/ boolean atEnd() {
        return !(next < elems.length);
    }

    // doc comment inherited
    /*@ also
      @   public normal_behavior
      @    requires next < elems.length;
      @    assignable \nothing;
      @    ensures new Long(\result).equals(new Long(elems[next]));
      @ also
      @   public exceptional_behavior
      @     requires next >= elems.length;
      @     assignable \nothing;
      @     signals_only NoSuchElementException;
      @ implies_that
      @   public behavior
      @     assignable \nothing;
      @     signals_only NoSuchElementException;
      @     signals (NoSuchElementException e) atEnd();
      @*/
    public /*@ pure @*/ long getLong() {
        if (next < elems.length) {
            return elems[next];
        } else {
            //@ assume !(next < elems.length);
            //@ hence_by (* specification of atEnd() *);
            //@ assume atEnd();
            throw new NoSuchElementException();
        }
    }

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
    public /*@ non_null @*/ Object clone() {
        return new LongArrayIterator(next, elems);
    }

    // doc comment and specification inherited
    public /*@ non_null @*/ String toString() {
        String ret =
            "LongArrayIterator(" + next + ", new long[] {";
        for (int i = 0; i < elems.length; i++) {
            ret += elems[i] + ", ";
        }
        return ret + "})";
    }
}
