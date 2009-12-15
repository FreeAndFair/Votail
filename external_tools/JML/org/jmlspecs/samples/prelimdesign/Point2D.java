// @(#)$Id: Point2D.java,v 1.3 2005/11/28 03:52:30 leavens Exp $

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

//@ model import org.jmlspecs.models.JMLDouble;

public class Point2D
{
  private /*@ spec_public @*/ double x = 0.0;
  private /*@ spec_public @*/ double y = 0.0;

  //@ public invariant !Double.isNaN(x);
  //@ public invariant !Double.isNaN(y);
  //@ public invariant !Double.isInfinite(x);
  //@ public invariant !Double.isInfinite(y);

  //@ ensures x == 0.0 && y == 0.0;
  public Point2D() { }

  /*@ requires !Double.isNaN(xc);
    @ requires !Double.isNaN(yc);
    @ requires !Double.isInfinite(xc);
    @ requires !Double.isInfinite(yc);
    @ assignable x, y;
    @ ensures x == xc && y == yc;
    @*/
  public Point2D(double xc, double yc) {
    x = xc;
    y = yc;
  }

  //@ ensures \result == x;
  public /*@ pure @*/ double getX() {
    return x;
  }

  //@ ensures \result == y;
  public /*@ pure @*/ double getY() {
    return y;
  }
  
  /*@ requires !Double.isNaN(x+dx);
    @ requires !Double.isInfinite(x+dx);
    @ assignable x;
    @ ensures JMLDouble.approximatelyEqualTo(x,
    @                       \old(x+dx), 1e-10);
    @*/
  public void moveX(double dx) {
    x += dx;
  }
  
  /*@ requires !Double.isNaN(y+dy);
    @ requires !Double.isInfinite(y+dy);
    @ assignable y;
    @ ensures JMLDouble.approximatelyEqualTo(y,
    @                       \old(y+dy), 1e-10);
    @*/
  public void moveY(double dy) {
    y += dy;
  }
}
