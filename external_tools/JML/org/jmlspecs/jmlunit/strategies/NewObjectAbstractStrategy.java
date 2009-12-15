// @(#)$Id: NewObjectAbstractStrategy.java,v 1.7 2007/12/19 01:59:43 chalin Exp $

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

/** A strategy that provides test data by creating (in general) the
 * objects each time the make() method is called for a particular
 * argument.  The idea is to prevent aliasing without cloning.
 *
 * <p>Hoewver, If you want to have aliasing, arrange it so that the
 * same object is returned multiple times by make().
 *
 * <p>This strategy provides <kbd>null</kbd> by default, so users
 * never need to return null in the body of the {@link #make()} method
 * they provide.
 *
 * @author Gary T. Leavens
 */
public abstract class NewObjectAbstractStrategy implements StrategyType {

    // doc comment and specification inherited
    public /*@non_null*/ IndefiniteIterator iterator() {
        return new NewObjectAbstractIterator()
            {
                /** Return null for index 0, and for n &gt; 0, return
                 * the object returned by
                 * NewObjectAbstractStrategy.this.make(n-1);
                 */
                public /*@pure*/ /*@nullable*/ Object make(int n) {
                    if (n == 0) {
                        return null;
                    } else {
                        return NewObjectAbstractStrategy.this.make(n-1);
                    }
                }
            };
    }

    /** Return the nth test data item. */
    /*@ protected behavior
      @   requires 0 <= n;
      @   assignable objectState;
      @   signals_only NoSuchElementException;
      @*/
    protected abstract /*@nullable*/ Object make(int n);
}
