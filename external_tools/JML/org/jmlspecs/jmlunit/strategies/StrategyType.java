// @(#)$Id: StrategyType.java,v 1.8 2007/12/19 01:59:43 chalin Exp $

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

/** Strategies for providing test data.  These simply consist of a
 * method iterator(), which can be called to return a new
 * {@link IndefiniteIterator} object.
 * @author Gary T. Leavens
 */
public interface StrategyType {

    /** Compute a fresh indefinite iterator, which can be used to
     * provide test data of some reference type.  The indefinite
     * iterator returned should be freshly created.  Usually it should
     * not be at its end.  However, in rare cases it might make sense
     * to have an empty iterator be computed (e.g., by filtering).  */
    //@ assignable objectState;
    //@ ensures \fresh(\result);
    //@ ensures_redundantly \result != null;
    public /*@non_null*/ IndefiniteIterator iterator();
}
