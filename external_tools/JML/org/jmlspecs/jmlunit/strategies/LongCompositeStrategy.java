// @(#)$Id: longCompositeStrategy.java-generic,v 1.6 2005/12/24 21:20:31 chalin Exp $

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

/** A composition of several LongStrategys
 * @author Gary T. Leavens
 * @see CompositeIterator
 */
public class LongCompositeStrategy
    extends LongAbstractStrategy
{
    /** The indefinite iterators being concatenated. */
    private /*@ spec_public non_null @*/ LongStrategyType[] strats;
    //@ in objectState;
    //+@ maps strats[*].objectState \into objectState;

    //@ public invariant \nonnullelements(strats);

    /** Initialize this composite to return the iterator given by the
     * given argument strategy. */
    //@ assignable strats;
    public LongCompositeStrategy
        (/*@ non_null @*/ LongStrategyType s)
    {
        this(new LongStrategyType[] {s});
    }

    /** Initialize this composite to return the iterator given by the
     * given argument strategies, in order. */
    //@ assignable strats;
    public LongCompositeStrategy
        (/*@ non_null @*/ LongStrategyType s1, 
         /*@ non_null @*/ LongStrategyType s2)
    {
        this(new LongStrategyType[] {s1, s2});
    }

    /** Initialize this composite to return the iterator given by the
     * given argument strategies, in order. */
    /*@ requires \nonnullelements(strats);
      @ assignable this.strats;
      @ ensures Arrays.equals(this.strats, strats);
      @*/
    public LongCompositeStrategy
        (/*@ non_null @*/ LongStrategyType[] strats)
    {
        this.strats = (LongStrategyType[]) strats.clone(); 
    }

    // doc comment and specification inherited
    public LongIterator longIterator() {
        LongIterator[] iters
            = new LongIterator[strats.length];
        for (int i = 0; i < iters.length; i++) {
            iters[i] = strats[i].longIterator();
        }
        return new LongCompositeIterator(iters);
    }
}

