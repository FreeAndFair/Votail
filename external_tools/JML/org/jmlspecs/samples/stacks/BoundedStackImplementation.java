// @(#)$Id: BoundedStackImplementation.java,v 1.15 2005/07/08 18:13:39 leavens Exp $

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

import java.util.Arrays;
//@ model import org.jmlspecs.models.*;

public class BoundedStackImplementation implements BoundedStackInterface {

  // implementation data structures
  protected java.lang.Object[] theItems;
  //@                              maps theItems[*] \into theStack;
  protected int nextFree;
  //@               in theStack;
  //@ protected invariant 0 <= nextFree && nextFree <= theItems.length;
  //@ protected invariant theItems != null;
  /*@ protected represents theStack <- theStackRep();
    @ protected represents_redundantly theStack \such_that
    @      theStack != null
    @   && theStack.int_length() == nextFree
    @   && (\forall int i; 0 <= i && i < nextFree;
    @                      theStack.itemAt(i) == theItems[i]);
    @ protected invariant
    @     (\forall int i; 0 <= i && i < nextFree;
    @                     theItems[i] != null);
    @*/

  /*@ protected pure model JMLObjectSequence theStackRep() {
    @ JMLObjectSequence ret = new JMLObjectSequence();
    @   int i;
    @   for (i = 0; i < nextFree; i++) {
    @     ret = ret.insertFront(theItems[i]);
    @   }
    @   return ret;
    @ }
    @*/

  private static int MAX_STACK_ITEMS = 10;

  //@ private represents MAX_SIZE <- MAX_STACK_ITEMS;

  //@ private invariant theItems.length == MAX_STACK_ITEMS;

  /*@ protected normal_behavior
    @   assignable size, theStack;
    @   assignable_redundantly theItems, nextFree;
    @   ensures nextFree == 0;
    @*/
  public BoundedStackImplementation( )
  {
    theItems = new Object[MAX_STACK_ITEMS];
    nextFree = 0;
  }

  /*@ also
    @   protected behavior
    @     assignable \nothing;
    @     ensures 
    @       Arrays.equals(theItems,
    @                     ((BoundedStackImplementation)\result).theItems)
    @         && nextFree == ((BoundedStackImplementation)\result).nextFree
    @         && this != \result;
    @     ensures_redundantly \result != null;
    @*/
  public java.lang.Object clone () throws CloneNotSupportedException
  {
      BoundedStackImplementation res = new BoundedStackImplementation();
      res.theItems = (Object[])(theItems.clone());
      res.nextFree = nextFree;
      return res;
  }

  /*@ also
    @   protected normal_behavior
    @     ensures \result == theItems.length;
    @ implies_that
    @     private normal_behavior
    @     ensures \result == MAX_STACK_ITEMS;
    @*/
  public int getSizeLimit()
  {
    return MAX_STACK_ITEMS;
  }

  /*@ also
    @   protected normal_behavior
    @       ensures \result == (nextFree == 0);
    @*/
  public boolean isEmpty( )
  {
    return (nextFree == 0);
  }

  /*@ also
    @   protected normal_behavior
    @     ensures \result == (nextFree == theItems.length);
    @*/
  public boolean isFull()
  {
    return (nextFree == MAX_STACK_ITEMS);
  }

  /*@ also
    @    protected normal_behavior
    @     requires nextFree != 0;
    @     assignable theStack;
    @     assignable_redundantly nextFree;
    @     ensures nextFree == \old(nextFree - 1)
    @           && \not_modified(theItems);
    @     ensures_redundantly Arrays.equals(theItems,\old(theItems));
    @ also 
    @    protected exceptional_behavior
    @     requires nextFree == 0;
    @     assignable \nothing;
    @     signals_only BoundedStackException;
    @*/
  public void pop( ) throws BoundedStackException
  {
    if (nextFree == 0) {
      throw new BoundedStackException("Tried to pop an empty stack.");
    } else {
      nextFree--;
      return;
    }   
  }

  /*@ also
    @    protected normal_behavior
    @     requires nextFree < theItems.length && x != null;
    @     assignable theStack;
    @     assignable_redundantly nextFree, theItems[nextFree];
    @     ensures theItems[(int)(nextFree-1)] == x
    @           && (\forall int i; 0 <= i && i < \old(nextFree-1);
    @                              theItems[i] == \old(theItems[i]))
    @           && nextFree == \old(nextFree + 1);
    @ also
    @   protected exceptional_behavior
    @     requires nextFree >= theItems.length || x == null;
    @     assignable \nothing;
    @     signals (BoundedStackException) nextFree >= theItems.length;
    @     signals (NullPointerException) x == null;
    @*/
  public void push(Object x ) throws BoundedStackException
  {
        if (nextFree == MAX_STACK_ITEMS) {
          throw new BoundedStackException("Tried to push onto a full stack");
        } else if (x == null) {
          throw new NullPointerException("Argument x to push is null");
        } else {
          theItems[nextFree++] = x;
          return;
        }       
    }

  /*@ also
    @   protected normal_behavior
    @     requires nextFree != 0;
    @     assignable \nothing;
    @     ensures \result == theItems[(int)(nextFree - 1)];
    @ also 
    @   protected exceptional_behavior
    @     requires nextFree == 0;
    @     assignable \nothing;
    @     signals (BoundedStackException e)
    @             \fresh(e) && e != null && e.getMessage() != null
    @           && e.getMessage().equals("empty stack");
    @*/
  public Object top( ) throws BoundedStackException
  {
    if (nextFree == 0) {
      throw new BoundedStackException("empty stack");
    } else {
      return theItems[nextFree - 1];
    }
  }

  /*@ also
    @   public normal_behavior
    @     assignable \nothing;
    @     ensures \result != null
    @          && (* a string encoding of this is returned *);
    @*/
  public String toString()
  {
    StringBuffer ret = new StringBuffer(this.getClass().toString() + " [");
    boolean first = true;
    for (int k = nextFree - 1; k >= 0; k--) {
        if (first) {
            first = false;
        } else {
            ret.append(", ");
        }
        if (theItems[k] != null) {
            ret.append(theItems[k]);
        } else {
            ret.append("null");
        }
    } 
    ret.append("]");
    return ret.toString();
  }

  /*@ protected normal_behavior
    @   assignable System.out;
    @   ensures (* prints a version of stack to System.out *);
    @*/
  protected void printStack ( )
  {
    System.out.println("The stack items are (top first):");
    System.out.println(toString());
  }
}
