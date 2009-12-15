// @(#)$Id: ImmutableObjectExtensibleStrategyDecorator.java,v 1.2 2005/07/07 21:03:04 leavens Exp $

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

/** A decorator for immutable object strategies that allows for easy
 * extension with immutable test data.
 *
 * <p>
 * This type provides an extension mechanism that is easier to use
 * than a composite. To extend the test data, make a subclass that
 * overrides the addData() method; this method provides the additional
 * data for testing.
 *
 * @author Gary T. Leavens
 */
public class ImmutableObjectExtensibleStrategyDecorator
    extends AbstractExtensibleStrategyDecorator
{
    //@ public normal_behavior
    //@   requires strat != null;
    //@   assignable defaultData, addedData, objectState;
    //@   ensures defaultData == strat;
    public ImmutableObjectExtensibleStrategyDecorator(StrategyType strat)
    {
        super(strat);
    }

    protected StrategyType addedDataStrategy(final Object[] added) {
        return new ImmutableObjectAbstractStrategy() {
                protected Object[] defaultData() {
                    return (Object[]) added.clone();
                }
            };
    }
}

