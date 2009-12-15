// @(#)$Id: Meter.java,v 1.4 2004/11/22 04:55:48 leavens Exp $

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

/** A behavioral subtype of Counter. */
public class Meter implements Counter {

    /** The count of how many times inc has been called. */
    protected int count;
    //@               in val;
    //@ protected represents val <- count;

    // doc comment and specification inherited.
    public void inc() { count++; }

    // doc comment and specification inherited.
    public /*@ pure @*/ int value() { return count; }

    /** Initialize this Meter. */
    /*@ assignable val;
      @ ensures val == 0;
      @*/
    public Meter() { count = 0; }
}
