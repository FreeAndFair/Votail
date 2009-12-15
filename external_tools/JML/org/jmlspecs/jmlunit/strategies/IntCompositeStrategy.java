// @(#)$Id: intCompositeStrategy.java-generic,v 1.6 2005/12/24 21:20:31 chalin Exp $

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

/** A composition of several IntStrategys
 * @author Gary T. Leavens
 * @see CompositeIterator
 */
public class IntCompositeStrategy
    extends IntAbstractStrategy
{
    /** The indefinite iterators being concatenated. */
    private /*@ spec_public non_null @*/ IntStrategyType[] strats;
    //@ in objectState;
    //+@ maps strats[*].objectState \into objectState;

    //@ public invariant \nonnullelements(strats);

    /** Initialize this composite to return the iterator given by the
     * given argument strategy. */
    //@ assignable strats;
    public IntCompositeStrategy
        (/*@ non_null @*/ IntStrategyType s)
    {
        this(new IntStrategyType[] {s});
    }

    /** Initialize this composite to return the iterator given by the
     * given argument strategies, in order. */
    //@ assignable strats;
    public IntCompositeStrategy
        (/*@ non_null @*/ IntStrategyType s1, 
         /*@ non_null @*/ IntStrategyType s2)
    {
        this(new IntStrategyType[] {s1, s2});
    }

    /** Initialize this composite to return the iterator given by the
     * given argument strategies, in order. */
    /*@ requires \nonnullelements(strats);
      @ assignable this.strats;
      @ ensures Arrays.equals(this.strats, strats);
      @*/
    public IntCompositeStrategy
        (/*@ non_null @*/ IntStrategyType[] strats)
    {
        this.strats = (IntStrategyType[]) strats.clone(); 
    }

    // doc comment and specification inherited
    public IntIterator intIterator() {
        IntIterator[] iters
            = new IntIterator[strats.length];
        for (int i = 0; i < iters.length; i++) {
            iters[i] = strats[i].intIterator();
        }
        return new IntCompositeIterator(iters);
    }
}

