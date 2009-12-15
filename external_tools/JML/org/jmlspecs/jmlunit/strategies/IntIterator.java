// @(#)$Id: intIterator.java-generic,v 1.10 2005/12/24 21:20:31 chalin Exp $

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
 * values of type int without casting.
 * @see IndefiniteIterator
 * @author Gary T. Leavens
 */
public interface IntIterator extends IndefiniteIterator {

    /*@ also
      @  public normal_behavior
      @    requires !atEnd();
      @    ensures \result instanceof Integer;
      @*/
    /*@ pure nullable @*/ Object get();

    /** Return the current int in this iterator. */
    /*@ public behavior
      @     assignable \nothing;
      @     ensures_redundantly atEnd() == \old(atEnd());
      @     signals_only NoSuchElementException;
      @     signals (NoSuchElementException) \old(atEnd());
      @*/
    /*@ pure @*/ int getInt();

    /** Return a copy of this iterator in the same state as this object. */
    /*@ also
      @  public normal_behavior
      @    assignable \nothing;
      @    ensures \fresh(\result) && \result instanceof IntIterator;
      @    ensures \result != this;
      @    ensures_redundantly \result != null;
      @    ensures ((IntIterator)\result).atEnd() == atEnd();
      @    ensures !atEnd() ==>
      @            new Integer(((IntIterator)\result).getInt())
      @            .equals(new Integer(getInt()));
      @*/
    /*@ pure @*/ Object clone();
}
