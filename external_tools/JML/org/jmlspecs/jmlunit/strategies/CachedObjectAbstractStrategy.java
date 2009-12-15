// @(#)$Id: CachedObjectAbstractStrategy.java,v 1.6 2007/12/19 01:59:43 chalin Exp $

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

/** A strategy for producing (test) data of an immutable
 * or cloneable reference types from cached data provided by the user.
 * The data used is cached, and thus only has to be produced once.
 *
 * <p>By default, <kbd>null</kbd> is the only test data provided,
 * but this means that subclasses don't have to provide <kbd>null</kbd>
 * as data, unless they override the {@link #defaultData()} method.
 *
 * <p>This type also provides an extension mechanism that is easier to
 * use than a composite, wherein subclasses of subclasses can override
 * the {@link #addData()} method to provide additional data for testing.
 *
 * @author Gary T. Leavens
 */
public abstract class CachedObjectAbstractStrategy implements StrategyType {

    /** The data to return in the iterations */
    private /*@ nullable @*/ Object[] data = null; //@ in objectState;

    // doc comment inherited
    public synchronized /*@non_null*/ IndefiniteIterator iterator() {
        if (data == null) {
            data = getData();
            //@ assert data != null;
        }
        return iteratorFor(data);
    }

    /** Return an appropriate iterator for the data. */
    /*@ protected normal_behavior
      @   assignable objectState;
      @   ensures \fresh(\result);
      @*/
    protected abstract IndefiniteIterator iteratorFor(Object[] data);

    /** Create and return the data for the iterations.
     *  This is should only be called once for this object.
     */
    /*@ protected normal_behavior
      @   assignable objectState;
      @   ensures \result != null;
      @*/
    protected Object[] getData() {
        Object[] defd = defaultData();
        Object[] ret = defd;
        Object[] added = addData();
        if (added.length != 0) {
            ret = new Object[defd.length + added.length];
            System.arraycopy(defd, 0, ret, 0, defd.length);
            System.arraycopy(added, 0, ret, defd.length, added.length);
        }
        return ret;
    }

    /** Create and return the default data for the iterations.
     *  This is should only be called once for this object.
     */
    /*@ protected normal_behavior
      @   assignable objectState;
      @   ensures \result != null;
      @*/
    protected Object[] defaultData() {
        return new Object[] { null };
    }

    /** Subclasses can override this to make simple extensions to the
     * data used. */
    /*@ protected normal_behavior
      @   assignable objectState;
      @   ensures \result != null;
      @*/
    protected Object[] addData() {
        return new Object[] {};
    }
}
