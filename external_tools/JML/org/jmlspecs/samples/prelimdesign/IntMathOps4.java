// @(#)$Id: IntMathOps4.java,v 1.10 2005/12/04 18:09:42 leavens Exp $

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

package org.jmlspecs.samples.prelimdesign;

public class IntMathOps4 { 

  /** Integer square root function.
   * @param y the number to take the root of
   * @return an integer approximating
   *         the positive square root of y
   * <pre><jml>
   *   public normal_behavior
   *     requires y >= 0;   
   *     assignable \nothing; 
   *     ensures 0 <= \result
   *        && \result * \result <= y
   *        && ((0 <= (\result + 1) * (\result + 1))
   *            ==> y < (\result + 1) * (\result + 1));
   * </jml></pre>
   **/
  public static int isqrt(int y)
  {
     return (int) Math.sqrt(y);
  }
}
