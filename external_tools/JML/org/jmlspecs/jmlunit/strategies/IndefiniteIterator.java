// @(#)$Id: IndefiniteIterator.java,v 1.9 2005/12/23 17:02:07 chalin Exp $

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

/** Indefinite iterators.  These can also be thought of as cursors
 * that point into a sequence.
 * @version $Revision: 1.9 $
 * @author Gary T. Leavens
 * @see java.util.Iterator
 */
public interface IndefiniteIterator extends Cloneable {

    /** Is this iterator at its end?  That is, if we called get(),
     * would it throw an exception? */
    /*@ pure @*/ boolean atEnd();

    /** Return the current element in this iteration.  This method may
     * be called multiple times, and does not advance the state of the
     * iterator when it is called.  The idea is to permit several
     * similar copies to be returned (e.g., clones) each time it is
     * called.
     * @throws NoSuchElementException, when atEnd() is true.
     */
    /*@  public behavior
      @     assignable \nothing;
      @     ensures_redundantly atEnd() == \old(atEnd());
      @     signals (Exception e) e instanceof NoSuchElementException
      @                       && atEnd();
      @*/
    /*@ pure nullable @*/ Object get();

    /** Advance the state of this iteration to the next position.
     * Note that this never throws an exception. */
    /*@  public normal_behavior
      @     assignable objectState;
      @*/
    void advance();

    /** Return a copy of this iterator in the same state as this object. */
    /*@ also
      @  public normal_behavior
      @    assignable \nothing;
      @    ensures \fresh(\result) && \result instanceof IndefiniteIterator;
      @    ensures \result != this;
      @    ensures_redundantly \result != null;
      @    ensures ((IndefiniteIterator)\result).atEnd() == atEnd();
      @*/
    /*@ pure @*/ Object clone();
}
