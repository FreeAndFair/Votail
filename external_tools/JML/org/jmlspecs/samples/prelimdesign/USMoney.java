// @(#)$Id: USMoney.java,v 1.5 2007/07/01 14:19:37 chalin Exp $

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

public /*@ pure @*/ class USMoney
                extends MoneyComparableAC implements MoneyOps
{
  /*@   public normal_behavior
    @     assignable pennies;
    @     ensures pennies == cs;
    @ implies_that
    @   protected normal_behavior
    @     assignable pennies, numCents;
    @     ensures numCents == cs;
    @*/
  public USMoney(long cs)
  {
    numCents = cs;
  }

  /*@ public normal_behavior
    @   assignable pennies;
    @   ensures pennies == (long)(100.0 * amt);
    @   // ensures_redundantly (* pennies holds amt dollars *);
    @*/
  public USMoney(double amt)
  {
    numCents = (long)(100.0 * amt);
  }

  public MoneyOps plus(Money m2)
  {
    return new USMoney(numCents + totalCents(m2));
  }

  public MoneyOps minus(Money m2)
  {
    return new USMoney(numCents - totalCents(m2));
  }
    
  public MoneyOps scaleBy(double factor)
  {
    return new USMoney(numCents * factor / 100.0);
  }

  public String toString()
  {
    return "$" + dollars() + "." + cents();
  }
}
