// @(#)$Id: doubleCompositeStrategy.java-generic,v 1.6 2005/12/24 21:20:31 chalin Exp $

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

//@ model import java.util.Arrays;

/** A composition of several DoubleStrategys
 * @author Gary T. Leavens
 * @see CompositeIterator
 */
public class DoubleCompositeStrategy
    extends DoubleAbstractStrategy
{
    /** The indefinite iterators being concatenated. */
    private /*@ spec_public non_null @*/ DoubleStrategyType[] strats;
    //@ in objectState;
    //+@ maps strats[*].objectState \into objectState;

    //@ public invariant \nonnullelements(strats);

    /** Initialize this composite to return the iterator given by the
     * given argument strategy. */
    //@ assignable strats;
    public DoubleCompositeStrategy
        (/*@ non_null @*/ DoubleStrategyType s)
    {
        this(new DoubleStrategyType[] {s});
    }

    /** Initialize this composite to return the iterator given by the
     * given argument strategies, in order. */
    //@ assignable strats;
    public DoubleCompositeStrategy
        (/*@ non_null @*/ DoubleStrategyType s1, 
         /*@ non_null @*/ DoubleStrategyType s2)
    {
        this(new DoubleStrategyType[] {s1, s2});
    }

    /** Initialize this composite to return the iterator given by the
     * given argument strategies, in order. */
    /*@ requires \nonnullelements(strats);
      @ assignable this.strats;
      @ ensures Arrays.equals(this.strats, strats);
      @*/
    public DoubleCompositeStrategy
        (/*@ non_null @*/ DoubleStrategyType[] strats)
    {
        this.strats = (DoubleStrategyType[]) strats.clone(); 
    }

    // doc comment and specification inherited
    public DoubleIterator doubleIterator() {
        DoubleIterator[] iters
            = new DoubleIterator[strats.length];
        for (int i = 0; i < iters.length; i++) {
            iters[i] = strats[i].doubleIterator();
        }
        return new DoubleCompositeIterator(iters);
    }
}

