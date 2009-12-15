// @(#)$Id: longNonNegativeStrategyDecorator.java-generic,v 1.4 2005/12/06 19:54:59 chalin Exp $

// Copyright (C) 2005 Iowa State University
//
// This file is part of the runtime library of the Java Modeling Language.
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation; either version 2.1,
// of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with JML; see the file LesserGPL.txt.  If not, write to the Free
// Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
// 02110-1301  USA.

package org.jmlspecs.jmlunit.strategies;

/** A decorator for strategies that filters out that filters out
 * negative test data.
 *
 * @author Gary T. Leavens
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class LongNonNegativeStrategyDecorator
    extends LongAbstractFilteringStrategyDecorator
{
    //@ public normal_behavior
    //@   requires strat != null;
    //@   assignable rawData;
    //@   ensures rawData == strat;
    public LongNonNegativeStrategyDecorator
        (LongStrategyType strat)
    {
        super(strat);
    }

    // doc comment and specification inherited
    public /*@ pure @*/ boolean approve(long elem) {
        return !(elem < 0);
    }
}

