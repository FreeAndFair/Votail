// @(#)$Id: MoneyComparableAC.java,v 1.4 2005/11/28 03:52:30 leavens Exp $

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

public /*@ pure @*/ abstract class MoneyComparableAC
    extends MoneyAC implements MoneyComparable
{
  protected static /*@ pure @*/
  long totalCents(Money m2)
  {
    long res = 100 * m2.dollars() + m2.cents();
    //@ assert res == m2.pennies;
    return res;
  }

  public boolean greaterThan(Money m2)
  {
    return numCents > totalCents(m2);
  }

  public boolean greaterThanOrEqualTo(Money m2)
  {
    return numCents >= totalCents(m2);
  }

  public boolean lessThan(Money m2)
  {
    return numCents < totalCents(m2);
  }

  public boolean lessThanOrEqualTo(Money m2)
  {
    return numCents <= totalCents(m2);
  }
}

