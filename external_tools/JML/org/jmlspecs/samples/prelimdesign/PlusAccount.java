// @(#)$Id: PlusAccount.java,v 1.6 2005/07/11 21:28:17 leavens Exp $

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

//@ refine "PlusAccount.jml";

public class PlusAccount extends Account {

    private /*@ non_null @*/ MoneyOps checkingPart;
    //@                                   in savings, checking;

    //@ private represents savings <- credit_.minus(checkingPart);
    //@ private represents checking <- checkingPart;

    //@ private invariant checkingPart.greaterThanOrEqualTo(new USMoney(0));
    //@ private invariant checkingPart.lessThanOrEqualTo(credit_);

    public PlusAccount(MoneyOps sav, MoneyOps chk, String own) {
        super(sav.plus(chk), own);
        checkingPart = chk;
    }

    public void payInterest(double rate) {
        super.payInterest(rate);
        checkingPart = checkingPart.scaleBy(1.0 + rate);
    }

    public void withdraw(MoneyOps amt) {
        super.withdraw(amt);
        if (credit_.lessThan(checkingPart)) {
            MoneyOps toSavings = checkingPart.minus(credit_);
            checkingPart = checkingPart.minus(toSavings);
        }
    }

    // should be able to have
    public void deposit(MoneyOps amt) { super.deposit(amt); }
    // be inherited without change.

    public void depositToChecking(MoneyOps amt) {
        super.deposit(amt);
        checkingPart = checkingPart.plus(amt);
    }

    public void payCheck(MoneyOps amt) {
        super.withdraw(amt);
        if (amt.lessThanOrEqualTo(checkingPart)) {
            checkingPart = checkingPart.minus(amt);
        } else {
            checkingPart = new USMoney(0);
        }
    }

    public String toString() {
        return super.toString() + " checking: " + checkingPart;
    }
}
