// @(#)$Id: charExtensibleStrategyDecorator.java-generic,v 1.6 2005/12/24 21:20:31 chalin Exp $

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

/** A decorator for strategies (which provide test data of type type
 * char) that allows for easy extension to the test data of the
 * underlying strategy.
 *
 * <p>
 * This type provides an extension mechanism that is easier to use
 * than a composite. To extend the test data, make a subclass that
 * overrides the addData() method; this method provides the additional
 * data for testing.
 *
 * @author Gary T. Leavens
 */
public class CharExtensibleStrategyDecorator
    extends CharAbstractStrategy
{
    /** The default data, returned first in the iterations. */
    private /*@ spec_public non_null @*/ CharStrategyType defaultData;
    //@ in objectState; maps defaultData.objectState \into objectState;

    /** The added data, returned after the default data in the iterations. */
    private /*@ spec_public non_null @*/ CharStrategyType addedData;
    //@ in objectState; maps addedData.objectState \into objectState;

    //@ public normal_behavior
    //@   assignable objectState, defaultData, addedData, owner, strat.owner;
    //@   ensures defaultData == strat;
    public CharExtensibleStrategyDecorator
        (/*@ non_null @*/ CharStrategyType strat)
    {
        defaultData = strat;
        addedData = new CharExtensibleStrategy() {
                protected char[] defaultData() {
                    return CharExtensibleStrategyDecorator
                        .this.addData();
                }
            };
        //@ set defaultData.owner = this;
        //@ set addedData.owner = this;
        //@ set owner = null;
    }

    // doc comment inherited
    public /*@ non_null @*/ CharIterator charIterator() {
        return new CharCompositeIterator
            (defaultData.charIterator(),
             addedData.charIterator());
    }

    /** Subclasses can override this to make simple extensions to the
     * data used. This should only be called once when the object is
     * being constructed. */
    /*@ protected normal_behavior
      @   assignable objectState;
      @   ensures \result != null;
      @*/
    protected char[] addData() {
        return new char[] {};
    }
}
