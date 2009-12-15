// @(#)$Id: IntBigStrategy.java,v 1.4 2005/07/07 21:03:04 leavens Exp $

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

/** Slightly more extensive test data of type int.
 * <p>
 * Subclasses of this strategy can provide additional test data by
 * overriding the method addData().
 *
 * @see IntStrategy
 * @author Gary T. Leavens
 */
public class IntBigStrategy extends IntExtensibleStrategyDecorator {

    /** Initialize this strategy. */
    //@ public normal_behavior
    //@   assignable defaultData, addedData;
    public IntBigStrategy() {
        super(new IntStrategy() {
                protected int[] addData() {
                   return new int[] { 3, -5,
                           Integer.MIN_VALUE, Integer.MAX_VALUE, };

                }
            });
    }
}

