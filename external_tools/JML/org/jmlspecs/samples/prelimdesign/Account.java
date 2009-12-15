// @(#)$Id: Account.java,v 1.9 2004/01/10 12:17:35 davidcok Exp $

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

//@ refine "Account.jml";

public class Account {

  protected MoneyOps credit_;
  //@                    in credit;
  protected String accountOwner_;
  //@                  in accountOwner;

  //@ protected represents credit <- credit_;
  //@ protected represents accountOwner <- accountOwner_;

  //@ protected invariant accountOwner_ != null && credit_ != null;
  /*@ protected invariant_redundantly
                       credit_.greaterThanOrEqualTo(new USMoney(0));
   @*/
  //@ protected constraint_redundantly accountOwner_.equals(\old(accountOwner_));

  public Account(MoneyOps amt, String own)
  {
    /*@ assume own != null && amt != null
            && (new USMoney(1)).lessThanOrEqualTo(amt);  @*/
    credit_ = amt;
    accountOwner_ = own;
  }

  public /*@ pure @*/ MoneyOps balance()
  {
    return credit_;
  }

  public void payInterest(double rate)
  {
    //@ assume 0.0 <= rate && rate <= 1.0;
    credit_ = credit_.scaleBy(1.0 + rate);
  }

  public void deposit(MoneyOps amt)
  {
    //@ assume amt != null && amt.greaterThanOrEqualTo(new USMoney(0));
    credit_ = credit_.plus(amt);
  }

  public void withdraw(MoneyOps amt)
  {
    /*@ assume amt != null && (new USMoney(0)).lessThanOrEqualTo(amt)
            && amt.lessThanOrEqualTo(credit_);  @*/
    credit_ = credit_.minus(amt);
  }

  public String toString()
  {
    return this.getClass().toString() + " owner:" + accountOwner_
         + " credit: " + credit_;
  }
}
