// @(#)$Id: shortStrategyType.java-generic,v 1.8 2005/12/24 21:20:31 chalin Exp $

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

/** The interface of strategies that provide test data of type short.
 * @author Gary T. Leavens
 */
public interface ShortStrategyType extends StrategyType {

    /** Compute a fresh ShortIterator, which can be used to
     * provide test data of type short.  The
     * ShortIterator returned should be freshly created.
     * Usually it should not be at its end. However, in rare cases it
     * might make sense to have an empty iterator be computed (e.g.,
     * by filtering).  */
    //@ assignable objectState;
    //@ ensures \fresh(\result);
    //@ ensures_redundantly \result != null;
    public ShortIterator shortIterator();
}
