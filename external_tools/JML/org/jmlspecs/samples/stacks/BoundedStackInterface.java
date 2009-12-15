// @(#)$Id: BoundedStackInterface.java,v 1.14 2006/08/16 17:40:44 leavens Exp $

// Copyright (C) 1998, 1999 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.


package org.jmlspecs.samples.stacks;
//@ model import org.jmlspecs.models.*;
public interface BoundedStackInterface extends BoundedThing {
    //@ public initially theStack != null && theStack.isEmpty();
  /*@ public model instance JMLObjectSequence theStack;
    @                                             in size;
    @*/
  //@ public instance represents size <- theStack.int_length();
  /*@ public instance invariant theStack != null;
    @ public instance invariant_redundantly
    @                           theStack.int_length() <= MAX_SIZE;
    @ public instance invariant 
    @         (\forall int i; 0 <= i && i < theStack.int_length();
    @                         theStack.itemAt(i) != null);
    @*/

  /*@   public normal_behavior
    @     requires !theStack.isEmpty();
    @     assignable size, theStack;
    @     ensures theStack.equals(\old(theStack.trailer()));
    @ also
    @   public exceptional_behavior
    @     requires theStack.isEmpty();
    @     assignable \nothing;
    @     signals_only BoundedStackException;
    @*/
  public void pop( ) throws BoundedStackException;

  /*@   public normal_behavior
    @     requires theStack.int_length() < MAX_SIZE && x != null;
    @     assignable size, theStack;
    @     ensures theStack.equals(\old(theStack.insertFront(x)));
    @     ensures_redundantly theStack != null && top() == x
    @              && theStack.int_length() 
    @                     == \old(theStack.int_length()+1);
    @ also
    @   public exceptional_behavior
    @     requires theStack.int_length() >= MAX_SIZE || x == null;
    @     assignable \nothing;
    @     signals_only BoundedStackException, NullPointerException;
    @     signals (BoundedStackException)
    @                  theStack.int_length() == MAX_SIZE;
    @     signals (NullPointerException) x == null;
    @*/
  public void push(Object x )
         throws BoundedStackException, NullPointerException;

  /*@   public normal_behavior
    @     requires !theStack.isEmpty();
    @     ensures \result == theStack.first() && \result != null;
    @ also
    @   public exceptional_behavior
    @     requires theStack.isEmpty();
    @     signals_only BoundedStackException;
    @     signals (BoundedStackException e)
    @             \fresh(e) && e != null && e.getMessage() != null
    @           && e.getMessage().equals("empty stack");
    @*/
  public /*@ pure @*/ Object top( ) throws BoundedStackException;
}
