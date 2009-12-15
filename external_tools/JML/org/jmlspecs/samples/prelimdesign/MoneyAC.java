// @(#)$Id: MoneyAC.java,v 1.8 2005/12/23 17:02:04 chalin Exp $

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

public /*@ pure @*/ abstract class MoneyAC implements Money
{
  protected long numCents;
  //@                in pennies;

  //@ protected represents pennies <- numCents;

  /*@ protected constraint_redundantly
    @            numCents == \old(numCents); @*/

  public long dollars() {
    return numCents / 100;
  }

  public long cents() {
    return numCents % 100;
  }

  public boolean equals(/*@ nullable @*/ Object o2) {
    if (o2 instanceof Money) {
      Money m2 = (Money)o2;
      return numCents
             == (100 * m2.dollars() + m2.cents());
    } else {
      return false;
    }
  }

  public int hashCode() {
    return (int)numCents;
  }

  public Object clone() {
    return this;
  }
}
