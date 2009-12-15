// @(#)$Id: AbstractExtensibleStrategyDecorator.java,v 1.7 2007/12/19 01:59:43 chalin Exp $

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

/** A decorator for strategies that allows for easy extension to the
 * test data of the underlying strategy.
 *
 * <p>
 * This type provides an extension mechanism that is easier to use
 * than a composite. To extend the test data, make a subclass that
 * overrides the addData() method; this method provides the additional
 * data for testing.
 *
 * @author Gary T. Leavens
 */
public abstract class AbstractExtensibleStrategyDecorator
    implements StrategyType
{
    /** The default data, returned first in the iterations. */
    private final /*@ spec_public non_null @*/ StrategyType defaultData;
    //@ in objectState; maps defaultData.objectState \into objectState;

    /** The added data, returned after the default data in the iterations. */
    private final /*@ spec_public non_null @*/ StrategyType addedData;
    //@ in objectState; maps addedData.objectState \into objectState;

    /*@ public normal_behavior
      @   requires strat != null;
      @   assignable defaultData, addedData, objectState, owner, strat.owner;
      @   ensures defaultData == strat;
      @   ensures owner == null && strat.owner == this;
      @*/
    public AbstractExtensibleStrategyDecorator(StrategyType strat)
    {
        defaultData = strat;
        addedData = addedDataStrategy(addData());
        //@ set defaultData.owner = this;
        //@ set addedData.owner = this;
        //@ set owner = null;
    }

    //@ protected normal_behavior
    //@   requires added != null;
    //@   assignable addedData, objectState;
    //@   ensures \result != null;
    protected abstract StrategyType addedDataStrategy(Object[] added);

    // doc comment inherited
    public /*@non_null*/ IndefiniteIterator iterator() {
        return new CompositeIterator
            (defaultData.iterator(), addedData.iterator());
    }

    /** Subclasses can override this to make simple extensions to the
     * data used. This should only be called once when the object is
     * being construted. */
    /*@ protected normal_behavior
      @   assignable objectState;
      @   ensures \result != null && defaultData == \old(defaultData);
      @*/
    protected Object[] addData() {
        return new Object[] {};
    }
}

