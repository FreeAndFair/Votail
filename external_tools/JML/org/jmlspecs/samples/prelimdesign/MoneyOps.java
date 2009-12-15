// @(#)$Id: MoneyOps.java,v 1.6 2007/07/01 14:39:10 chalin Exp $

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

public /*@ pure @*/ interface MoneyOps extends MoneyComparable
{
  /*@  public normal_behavior
    @     old double epsilon = 1.0;
    @     assignable \nothing;
    @     ensures \result
    @        <==> Long.MIN_VALUE + epsilon < d
    @             && d < Long.MAX_VALUE - epsilon;
    @ public model boolean inRange(double d);
    @
    @  public normal_behavior
    @     requires m2!= null;
    @     assignable \nothing;
    @     ensures \result
    @        <==> inRange((double) pennies + m2.pennies);
    @ public model boolean can_add(Money m2);
    @
    @  public normal_behavior
    @     ensures \result <==> inRange(factor * pennies);
    @ public model boolean can_scaleBy(double factor);
    @*/

  /*@   public normal_behavior
    @     old boolean can_add = can_add(m2); // FIXME: inline.
    @     requires m2 != null && can_add;
    @     assignable \nothing;
    @     ensures \result != null
    @          && \result.pennies == this.pennies + m2.pennies;
    @ for_example
    @   public normal_example
    @     requires this.pennies == 300 && m2.pennies == 400;
    @     assignable \nothing;
    @     ensures \result != null && \result.pennies == 700;
    @*/
  public MoneyOps plus(Money m2);

  /*@   public normal_behavior
    @     old boolean inRange = inRange((double) pennies - m2.pennies); // FIXME: inline.
    @     requires m2 != null
    @           && inRange;
    @     assignable \nothing;
    @     ensures \result != null
    @          && \result.pennies == this.pennies - m2.pennies;
    @ for_example
    @   public normal_example
    @     requires this.pennies == 400 && m2.pennies == 300;
    @     assignable \nothing;
    @     ensures  \result != null && \result.pennies == 100;
    @*/
  public MoneyOps minus(Money m2);

  /*@   public normal_behavior
    @     requires can_scaleBy(factor);
    @     assignable \nothing;
    @     ensures \result != null
    @          && \result.pennies == (long)(factor * pennies);
    @ for_example
    @   public normal_example
    @     requires pennies == 400 && factor == 1.01;
    @     assignable \nothing;
    @     ensures \result != null && \result.pennies == 404;
    @*/
  public MoneyOps scaleBy(double factor);
}
