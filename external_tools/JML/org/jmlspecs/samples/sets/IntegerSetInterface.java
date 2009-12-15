// @(#)$Id: IntegerSetInterface.java,v 1.10 2005/12/09 04:20:16 leavens Exp $

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


package org.jmlspecs.samples.sets;

//@ model import org.jmlspecs.models.*;

/** Sets of integers. */
public interface IntegerSetInterface {
    /*@ public model instance JMLValueSet theSet;
      @ public instance invariant_redundantly theSet != null;
      @ public initially theSet.isEmpty();
      @ public instance invariant
      @        (\forall JMLType e; theSet.has(e);
      @                            e instanceof JMLInteger);
      @*/

    /** Insert the given integer into this set. */
    /*@ public normal_behavior
      @	  assignable theSet;
      @	  ensures theSet.equals(\old(theSet.insert(new JMLInteger(elem))));
      @*/
    public void insert(int elem);

    /** Tell if the argument is in this set. */
    /*@ public normal_behavior	
      @	  ensures \result == theSet.has(new JMLInteger(elem));
      @*/
    public /*@ pure @*/ boolean isMember(int elem);

    /** Remove the given integer from this set. */
    /*@ public normal_behavior
      @   assignable theSet;
      @   ensures theSet.equals( \old(theSet.remove(new JMLInteger(elem))) );
      @*/
    public void remove(int elem);
}
