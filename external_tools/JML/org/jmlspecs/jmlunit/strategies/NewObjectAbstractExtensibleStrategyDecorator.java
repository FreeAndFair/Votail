// @(#)$Id: NewObjectAbstractExtensibleStrategyDecorator.java,v 1.5 2007/12/19 01:59:43 chalin Exp $

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

import java.util.NoSuchElementException;

/** A decorator for strategies that allows for easy extension in the
 * "new object" style to the test data of the underlying strategy.
 *
 * <p>
 * This type provides an extension mechanism that is easier to use
 * than a composite. To extend the test data, make a subclass that
 * overrides the make(int) method; that method provides the additional
 * data for testing.
 *
 * @author Gary T. Leavens
 */
public abstract class NewObjectAbstractExtensibleStrategyDecorator
    implements StrategyType
{
    /** The default data, returned first in the iterations. */
    private /*@ spec_public non_null @*/ StrategyType defaultData;
    //@ in objectState; maps defaultData.objectState \into objectState;

    /** The added data, returned after the default data in the iterations. */
    private /*@ spec_public non_null @*/ StrategyType addedData;
    //@ in objectState; maps addedData.objectState \into objectState;

    //@ public normal_behavior
    //@   requires strat != null;
    //@   assignable defaultData, addedData, objectState;
    //@   ensures defaultData == strat;
    public NewObjectAbstractExtensibleStrategyDecorator(StrategyType strat)
    {
        defaultData = strat;
        addedData = new StrategyType()
            {
                // doc comment and specification inherited
                public /*@non_null*/ IndefiniteIterator iterator() {
                    /** An iterator that extends
                     *  NewObjectAbstractIterator and takes care of
                     *  proper linkage between initialization and the
                     *  make method. */
                    class NewIter extends NewObjectAbstractIterator {
                        /** Initialize the superclass.  This needs to
                         * be done so that the initialize method is
                         * called after this object is constructed,
                         * otherwise a downcall to make here gives a
                         * null pointer exception.
                         * @see NewObjectAbstractIterator#initialize()
                         */
                        //@ assignable objectState;
                        public NewIter() {
                            super.initialize();
                        }

                        /** Return null for index 0, and for n &gt; 0,
                         * return the object returned
                         * NewObjectAbstractStrategy.this.make(n-1);
                         */
                        public /*@ pure @*/ Object make(int n) {
                            return NewObjectAbstractExtensibleStrategyDecorator
                                .this.make(n);
                        }
                    }
                    return new NewIter();
                }
            };
    }

    /** Return the nth test data item. The default implementation of
     * this method provides no data.  To provide additional test data,
     * you should override this method, without making a super call to
     * it.*/
    /*@ protected behavior
      @   requires 0 <= n;
      @   assignable objectState;
      @   signals_only NoSuchElementException;
      @*/
    protected Object make(int n) {
        throw new NoSuchElementException();
    }

    // doc comment inherited
    public /*@non_null*/ IndefiniteIterator iterator() {
        return new CompositeIterator
            (defaultData.iterator(), addedData.iterator());
    }
}

