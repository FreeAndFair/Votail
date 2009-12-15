// @(#)$Id: Entry.java,v 1.7 2005/12/23 17:02:04 chalin Exp $

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

/** Table entries, which are pairs of an index and a value.  These are
 * both JMLType objects.
 * @author Gary T. Leavens
 * @author Albert L. Baker
 */
public /*@ pure @*/ interface Entry extends JMLType {

    /** The model of the index of this entry. */
    //@ public model instance JMLType index;
    //@ public initially index != null;

    /** The model of the value of this entry. */
    //@ public model instance JMLType value;
    //@ public initially value != null;

    //@ public instance invariant index != null && value != null;
  
    /** Return this entry's index. */
    /*@ public normal_behavior
      @     ensures \result.equals(index);
      @*/
    public JMLType getIndex();

    /** Return this entry's value. */
    /*@ public normal_behavior
      @     ensures \result.equals(value);
      @*/
    public JMLType getValue();

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
    public boolean equals(/*@ nullable @*/ Object o);

    /*@ also
      @   public normal_behavior
      @     ensures \result instanceof Entry && \fresh(\result)
      @          && ((Entry)\result).equals(this);
      @     ensures_redundantly \result != this;
      @*/
    public Object clone();
}
