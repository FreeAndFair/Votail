// @(#)$Id: IntHeap.java,v 1.2 2002/08/16 22:11:56 leavens Exp $

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


package org.jmlspecs.samples.jmlrefman;               // line 1
                                                      // line 2
public abstract class IntHeap {                       // line 3
                                                      // line 4
    //@ public model non_null int [] elements;        // line 5
                                                      // line 6
    /*@ public normal_behavior                        // line 7
      @   requires elements.length >= 1;              // line 8
      @   assignable \nothing;                        // line 9
      @   ensures \result                             // line 10
      @        == (\max int j;                        // line 11
      @               0 <= j && j < elements.length;  // line 12
      @               elements[j]);                   // line 13
      @*/                                             // line 14
    public abstract /*@ pure @*/ int largest();       // line 15
                                                      // line 16
    //@ ensures \result == elements.length;           // line 17
    public abstract /*@ pure @*/ int size();          // line 18
};                                                    // line 19  
