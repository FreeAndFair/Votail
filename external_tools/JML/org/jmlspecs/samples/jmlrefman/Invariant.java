// @(#)$Id: Invariant.java,v 1.2 2002/08/18 01:14:31 leavens Exp $

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
 
public abstract class Invariant {

    boolean[] b; 

    //@ invariant b != null && b.length == 6;

    //@ assignable b;
    Invariant() {
        b = new boolean[6];
    }
}
