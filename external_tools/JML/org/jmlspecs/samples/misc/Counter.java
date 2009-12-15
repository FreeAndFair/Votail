// @(#)$Id: Counter.java,v 1.2 2004/11/22 04:55:48 leavens Exp $

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


package org.jmlspecs.samples.misc;

/** A simple Counter.  This class is a demo of behavioral subtyping. */
public interface Counter {

    /** The capacity of this counter. */
    int CAPACITY = 100;  // implicitly public, static, final

    /** A model of the value of this counter. */
    //@ public model instance int val;
    //@ public instance invariant 0 <= val && val < CAPACITY;

    /** Increment this counter */
    /*@ requires val < CAPACITY;
      @ assignable val;
      @ ensures val == \old(val + 1);
      @*/
    public void inc();

    /** Return the value of this counter. */
    //@ ensures \result == val;
    public /*@ pure @*/ int value();

}
