// @(#)$Id: IntMathOps.java,v 1.9 2005/12/04 18:09:42 leavens Exp $

// Copyright (C) 1998-2003 Iowa State University

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

package org.jmlspecs.samples.prelimdesign;

public class IntMathOps {                                // 1
                                                         // 2
  /*@ public normal_behavior                             // 3
    @   requires y >= 0;                                 // 4
    @   assignable \nothing;                             // 5
    @   ensures 0 <= \result                             // 6
    @        && \result * \result <= y                   // 7
    @        && ((0 <= (\result + 1) * (\result + 1))    // 8
    @            ==> y < (\result + 1) * (\result + 1)); // 9
    @*/                                                  //10
  public static int isqrt(int y)                         //11
  {                                                      //12
    return (int) Math.sqrt(y);                           //13
  }                                                      //14
}                                                        //15
