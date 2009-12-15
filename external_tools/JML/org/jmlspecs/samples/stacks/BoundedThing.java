// @(#)$Id: BoundedThing.java,v 1.9 2005/11/28 03:52:30 leavens Exp $

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


package org.jmlspecs.samples.stacks;

public interface BoundedThing {

    //@ public model instance int MAX_SIZE;
    //@ public model instance int size;

    /*@ public instance invariant MAX_SIZE > 0;
        public instance invariant
                0 <= size && size <= MAX_SIZE;
        public instance constraint
                MAX_SIZE == \old(MAX_SIZE);
      @*/

    /*@  public normal_behavior
           ensures \result == MAX_SIZE;
      @*/
    public /*@ pure @*/ int getSizeLimit();

    /*@  public normal_behavior
           ensures \result <==> size == 0;
      @*/
    public /*@ pure @*/ boolean isEmpty();

    /*@  public normal_behavior
          ensures \result <==> size == MAX_SIZE;
      @*/
    public /*@ pure @*/ boolean isFull();

    /*@ also
         public behavior
           assignable \nothing;
           ensures \result instanceof BoundedThing
               && size == ((BoundedThing)\result).size;
           signals_only CloneNotSupportedException;
      @*/
    public Object clone ()
       throws CloneNotSupportedException;
}
