// @(#)$Id: Money.java,v 1.7 2005/12/23 17:02:04 chalin Exp $

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

import org.jmlspecs.models.JMLType;

public /*@ pure @*/ interface Money extends JMLType
{
  //@ public model instance long pennies;

  //@ public instance constraint pennies == \old(pennies);

  /*@     public normal_behavior
    @       assignable \nothing;
    @       ensures \result == pennies / 100;
    @ for_example
    @     public normal_example
    @       requires pennies == 703;
    @       assignable \nothing;
    @       ensures \result == 7;
    @   also
    @     public normal_example
    @       requires pennies == 799;
    @       assignable \nothing;
    @       ensures \result == 7;
    @   also
    @     public normal_example
    @       requires pennies == -503;
    @       assignable \nothing;
    @       ensures \result == -5;
    @*/
  public long dollars();

  /*@   public normal_behavior
    @     assignable \nothing;
    @     ensures \result == pennies % 100;
    @ for_example
    @     requires pennies == 703;
    @     assignable \nothing;
    @     ensures \result == 3;
    @   also
    @     requires pennies == -503;
    @     assignable \nothing;
    @     ensures \result == -3;
    @*/
  public long cents();

  /*@ also
    @   public normal_behavior
    @     assignable \nothing;
    @     ensures \result
    @        <==> o2 instanceof Money
    @             && pennies == ((Money)o2).pennies;
    @*/
  public boolean equals(/*@ nullable @*/ Object o2);

  /*@ also
    @   public normal_behavior
    @     assignable \nothing;
    @     ensures \result instanceof Money
    @       && ((Money)\result).pennies == pennies;
    @*/
  public Object clone();
}
