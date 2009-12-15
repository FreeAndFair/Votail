// @(#)$Id: UnboundedStackAsArrayList.java,v 1.7 2005/07/08 18:13:39 leavens Exp $

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

import java.util.ArrayList;
import java.util.Iterator;

//@ model import org.jmlspecs.models.*;


public class UnboundedStackAsArrayList extends UnboundedStack {

  protected ArrayList elems;
  //@                     in theStack;
  //@                     maps elems.theList \into theStack;

  //@ protected invariant elems != null;
  /*@ protected represents theStack <- abstractValue();
   @  protected represents_redundantly theStack \such_that
   @     (\forall int i;
   @         0 <= i && i < elems.size();
   @         elems.get(i) == theStack.itemAt(i) );
   @*/

  /*@ protected pure model JMLObjectSequence abstractValue() {
    @   JMLObjectSequence ret = new JMLObjectSequence();
    @   Iterator iter = elems.iterator();
    @   while (iter.hasNext()) {
    @     ret = ret.insertBack(iter.next());
    @   }
    @   return ret;
    @ }
    @*/

  /*@ public normal_behavior
    @   assignable theStack;
    @   ensures theStack.isEmpty();
    @*/
  public UnboundedStackAsArrayList()
  {
    elems = new ArrayList();
  }

  /*@ also
    @   protected normal_behavior
    @     requires !theStack.isEmpty();
    @     assignable theStack;
    @     ensures \not_modified(elems);
    @*/
  public void pop( )
  {
    elems.remove(0);
  }

  /*@ also
    @   protected normal_behavior
    @     assignable theStack;
    @     ensures \not_modified(elems);
    @*/
  public void push(Object x)
  {
    elems.add(0,x);
  }

  public Object top( )
  {
    return elems.get(0);
  }

  public String toString() {
      StringBuffer ret = new StringBuffer("UnboundedStack[");
      Iterator iter = elems.iterator();
      boolean first = true;
      while (iter.hasNext()) {
          Object o = iter.next();
          if (o != null) {
              ret.append(o.toString());
          } else {
              ret.append("null");
          }
          if (first) {
              first = false;
          } else {
              ret.append(", ");
          }
      }
      ret.append("]");
      return ret.toString();
  }
}
