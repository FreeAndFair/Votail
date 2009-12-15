// @(#)$Id: booleanIterator.java-generic,v 1.10 2005/12/24 21:20:31 chalin Exp $

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

/** An extended indefinite iterator interface that can iterate over
 * values of type boolean without casting.
 * @see IndefiniteIterator
 * @author Gary T. Leavens
 */
public interface BooleanIterator extends IndefiniteIterator {

    /*@ also
      @  public normal_behavior
      @    requires !atEnd();
      @    ensures \result instanceof Boolean;
      @*/
    /*@ pure nullable @*/ Object get();

    /** Return the current boolean in this iterator. */
    /*@ public behavior
      @     assignable \nothing;
      @     ensures_redundantly atEnd() == \old(atEnd());
      @     signals_only NoSuchElementException;
      @     signals (NoSuchElementException) \old(atEnd());
      @*/
    /*@ pure @*/ boolean getBoolean();

    /** Return a copy of this iterator in the same state as this object. */
    /*@ also
      @  public normal_behavior
      @    assignable \nothing;
      @    ensures \fresh(\result) && \result instanceof BooleanIterator;
      @    ensures \result != this;
      @    ensures_redundantly \result != null;
      @    ensures ((BooleanIterator)\result).atEnd() == atEnd();
      @    ensures !atEnd() ==>
      @            new Boolean(((BooleanIterator)\result).getBoolean())
      @            .equals(new Boolean(getBoolean()));
      @*/
    /*@ pure @*/ Object clone();
}
