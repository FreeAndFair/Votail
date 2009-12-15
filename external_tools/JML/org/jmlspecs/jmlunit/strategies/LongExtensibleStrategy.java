// @(#)$Id: longExtensibleStrategy.java-generic,v 1.5 2005/12/24 21:20:31 chalin Exp $

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

/** Common code for extensible strategies for providing test data of
 * type long.
 *
 * <p>
 * This type provides an extension mechanism that is easier to
 * use than a composite, wherein subclasses of subclasses can override
 * the addData() method to provide additional data for testing.
 *
 * @author Gary T. Leavens
 */
public abstract class LongExtensibleStrategy
    extends LongAbstractStrategy
{
    /** The data to return in the iterations */
    private /*@ nullable @*/ long[] data = null;  //@ in objectState;

    // doc comment inherited
    public synchronized LongIterator longIterator() {
        if (data == null) {
            data = getData();
            //@ assert data != null;
        }
        return new LongArrayIterator(data);
    }

    /** Create and return the data for the iterations.
     *  This is should only be called once for this object.
     */
    /*@ protected normal_behavior
      @   assignable objectState;
      @   ensures \result != null;
      @*/
    protected long[] getData() {
        long[] defd = defaultData();
        long[] ret = defd;
        long[] added = addData();
        if (added.length != 0) {
            ret = new long[defd.length + added.length];
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
    protected abstract long[] defaultData();

    /** Subclasses can override this to make simple extensions to the
     * data used. */
    /*@ protected normal_behavior
      @   assignable objectState;
      @   ensures \result != null;
      @*/
    protected long[] addData() {
        return new long[] {};
    }
}

