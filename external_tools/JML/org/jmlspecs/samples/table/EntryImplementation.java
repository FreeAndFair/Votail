// @(#)$Id: EntryImplementation.java,v 1.8 2005/12/23 17:02:04 chalin Exp $

// Copyright (C) 1998, 1999 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.


package org.jmlspecs.samples.table;

import org.jmlspecs.models.JMLType;

/** Entries for Tables that map an index to a value.
 * @author Katie Becker
 * @author Gary T. Leavens
 */
public /*@ pure @*/ class EntryImplementation implements Entry {

    /** The index stored for this entry. */
    private /*@ non_null @*/ JMLType ind;
    //@               in index;

    /** The value stored for this entry. */
    private /*@ non_null @*/ JMLType val;
    //@               in value;

    /*@  private represents index <- ind; 
      @  private represents value <- val;
      @*/

    /** Initialize this entry. */
    /*@ public normal_behavior
      @   requires ind != null && val != null;
      @   assignable index, value;
      @     ensures index != null && value != null && 
      @       index.equals(ind) && value.equals(val);
      @*/
    public EntryImplementation(JMLType ind, JMLType val) {
        this.ind = ind;
        this.val = val;
    }

    public /*@ non_null @*/ JMLType getIndex() {
        return ind;
    }

    public /*@ non_null @*/ JMLType getValue() {
        return val;
    }

    /*@ also
      @   public normal_behavior
      @     requires o instanceof Entry;
      @     ensures \result == 
      @       (    ((Entry)o).index.equals(index)
      @         && ((Entry)o).value.equals(value) );
      @ also
      @   public normal_behavior
      @     requires !(o instanceof Entry);
      @     ensures \result == false;
      @*/
    public boolean equals(/*@ nullable @*/ Object o) {
        if (o == null || !(o instanceof EntryImplementation)) {
            return false;
        }
        return ((EntryImplementation)o).ind.equals(ind)
            && ((EntryImplementation)o).val.equals(val);
    }

    public int hashCode() {
        return ind.hashCode() + val.hashCode();
    }

    /*@ also
      @   public normal_behavior
      @     ensures \result instanceof Entry && \fresh(\result)
      @          && ((Entry)\result).equals(this);
      @     ensures_redundantly \result != this;
      @*/
    public Object clone() {
        return new EntryImplementation(ind, val);
    }
}
