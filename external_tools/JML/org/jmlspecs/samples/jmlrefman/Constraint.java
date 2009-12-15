// @(#)$Id: Constraint.java,v 1.5 2003/11/24 02:51:50 davidcok Exp $

// Copyright (C) 2002 Iowa State University

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


package org.jmlspecs.samples.jmlrefman;

public abstract class Constraint {

    int a;
    //@ constraint a == \old(a);
 
    boolean[] b; 

    //@ invariant b != null;
    //@ constraint b.length == \old(b.length) ;

    boolean[] c;

    //@ invariant c != null;
    //@ constraint c.length >= \old(c.length) ;

    //@ requires bLength >= 0 && cLength >= 0;
    Constraint(int bLength, int cLength) {
      b = new boolean[bLength];
      c = new boolean[cLength];
    }
}

