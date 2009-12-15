// @(#)$Id: CompositeIterator.java,v 1.12 2005/12/24 21:20:31 chalin Exp $

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

/** Composition of several indefinite iterators.
 * @author Gary T. Leavens
 * @see IndefiniteIterator
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class CompositeIterator implements IndefiniteIterator {

    /** What iterator we are working with now. */
    private /*@ spec_public @*/ int currentIterator = 0; //@ in objectState;
    
    /** The iterators that are being sequenced */
    private final /*@ spec_public non_null @*/ IndefiniteIterator[] iters;
    //@ in objectState;
    //+@ maps iters[*].objectState \into objectState;

    //@ public invariant 0 <= currentIterator && currentIterator <= iters.length;
    //@ public invariant \nonnullelements(iters);
    /*@ public constraint (\forall int i;  0 <= i && i < iters.length;
      @                                    iters[i] == \old(iters[i]));
      @*/

    /** Initialize this composite to iterate over the given iterator. */
    /*@ assignable iters, currentIterator, owner;
      @ ensures (* this.iters is a deep clone of
      @            new IndefiniteIterator[] {iter} *);
      @ ensures owner == null;
      @*/
    public CompositeIterator(/*@ non_null @*/ IndefiniteIterator iter) {
        this(new IndefiniteIterator[] {iter});
    }

    /** Initialize this composite to iterate over the given iterators,
     * in order. */
    /*@ assignable iters, currentIterator, owner;
      @ ensures (* this.iters is a deep clone of
      @            new IndefiniteIterator[] {iter1, iter2} *);
      @ ensures owner == null;
      @*/
    public CompositeIterator(/*@ non_null @*/ IndefiniteIterator iter1, 
                              /*@ non_null @*/ IndefiniteIterator iter2) {
        this(new IndefiniteIterator[] {iter1, iter2});
    }

    /** Initialize this composite to iterate over clones of the given
     * iterators, in order. */
    /*@ requires \nonnullelements(iters);
      @ assignable this.iters, currentIterator, owner;
      @ ensures (* this.iters is a deep clone of iters *);
      @ ensures this.iters != iters;
      @ ensures this.iters.length == iters.length;
      @ ensures (\forall int i; 0 <= i && i < iters.length;
      @                this.iters[i] != iters[i]
      @                && this.iters[i].atEnd() == iters[i].atEnd());
      @ ensures owner == null;
      @*/
    public CompositeIterator(/*@ non_null @*/ IndefiniteIterator[] iters) {
        this.iters = new IndefiniteIterator[iters.length];
        for (int i = 0; i < iters.length; i++) {
            this.iters[i] = (IndefiniteIterator) iters[i].clone();
            //@ set this.iters[i].owner = this;
        }
        setCurrentIterator();
        //@ set owner = null;
    }

    /** Initialize this composite to iterate over clones of the given
     * iterators, in order, starting at the given current iterator. */
    /*@ requires 0 <= currentIterator && currentIterator <= iters.length;
      @ requires (\forall int i; 0 <= i && i < currentIterator;
      @                          iters[i].atEnd());
      @ requires \nonnullelements(iters);
      @ assignable this.iters, this.currentIterator, owner;
      @ ensures (* this.iters is a deep clone of iters *);
      @ ensures this.iters != iters;
      @ ensures this.iters.length == iters.length;
      @ ensures (\forall int i; 0 <= i && i < iters.length;
      @                this.iters[i] != iters[i]
      @                && this.iters[i].atEnd() == iters[i].atEnd());
      @ ensures this.currentIterator == currentIterator;
      @ ensures owner == null;
      @*/
    protected CompositeIterator(int currentIterator,
                                /*@ non_null @*/ IndefiniteIterator[] iters)
                                
    {
        this.iters = new IndefiniteIterator[iters.length];
        for (int i = 0; i < iters.length; i++) {
            this.iters[i] = (IndefiniteIterator) iters[i].clone();
            //@ set this.iters[i].owner = this;
        }
        this.currentIterator = currentIterator;
        //@ set owner = null;
    }

    public boolean atEnd() {
        return !(currentIterator < iters.length);
    }

    /** Return the next element in this iteration.
     * @throws NoSuchElementException;
     */
    /*@ also
      @   public behavior
      @     assignable \nothing;
      @     signals (Exception e) e instanceof NoSuchElementException;
      @*/
    public /*@ pure @*/ Object get() {
        if (currentIterator < iters.length) {
            return iters[currentIterator].get();
        } else {
            //@ assume !(currentIterator < iters.length);
            //@ hence_by (* definition of atEnd() *);
            //@ assume atEnd();
            throw new NoSuchElementException();
        }
    }

    public void advance() {
        if (currentIterator < iters.length) {
            iters[currentIterator].advance();
        }
        setCurrentIterator();
    }

    /*@ public invariant (\forall int i; 0 <= i && i < currentIterator;
      @                                  iters[i].atEnd());
      @*/

    /** Set the current iterator to the next one that has elements, if any. */
    //@ assignable currentIterator;
    private void setCurrentIterator() {
        while (currentIterator < iters.length
               && iters[currentIterator].atEnd()) {
            currentIterator++;
        }
    }

    public /*@ non_null @*/ Object clone() {
        return new CompositeIterator(currentIterator, iters);
    }

    public /*@ non_null @*/ String toString() {
        String ret
            = "CompositeIterator(" + currentIterator
            + ", new IndefiniteIterator[] {";
        for (int i = 0; i < iters.length; i++) {
            ret += iters[i] + ", ";
        }
        return ret + "})";
    }
}
