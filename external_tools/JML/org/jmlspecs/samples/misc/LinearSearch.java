// @(#)$Id: LinearSearch.java,v 1.4 2005/02/17 17:05:32 leavens Exp $

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

package org.jmlspecs.samples.misc;

/** A linear search component, intended to demonstrate verification in
 * JML specifications.  This class has two abstract methods that
 * describe the search, which need to be filled in to instantiate
 * it.  The formulation of the search and the verification
 * is based on Edward Cohen's book
 * <cite>Programming in the 1990s</cite> (Springer-Verlag, 1990).
 * @author Gary T. Leavens
 */
public abstract class LinearSearch
{
    /** The function that describes what is being sought. */
    //@ requires j >= 0;
    public abstract /*@ pure @*/ boolean f(int j);

    /** The last integer in the search space, this describes the
     * domain of f, which goes from 0 to the result.
     */
    //@ ensures 0 <= \result;
    //@ ensures (\exists int j; 0 <= j && j <= \result; f(j));
    public abstract /*@ pure @*/ int limit();

    /** Find a solution to the searching problem. */
    /*@ public normal_behavior
      @   requires (\exists int i; 0 <= i && i <= limit(); f(i));
      @   assignable \nothing;
      @   ensures \result == (\min int i; 0 <= i && f(i); i);
      @*/
    public int find() {
        int x = 0;
        //@ maintaining 0 <= x && (\forall int i; 0 <= i && i < x; !f(i));
        //@ decreasing limit() - x;
        while (!f(x)) {
            /*@ assert 0 <= x && !f(x)
              @    && (\forall int i; 0 <= i && i < x; !f(i));
              @*/
            //@ hence_by (* arithmetic *);
            /*@ assert 0 <= (x+1)-1 && !f((x+1)-1)
              @    && (\forall int i; 0 <= i && i < (x+1)-1; !f(i));
              @*/
            x = x + 1;
            /*@ assert 0 <= x-1 && !f((int)(x-1))
              @    && (\forall int i; 0 <= i && i < x-1; !f(i));
              @*/
            //@ hence_by (* arithmetic, constant term rule *);
            /*@ assert 0 <= x && (\forall int i; i == x-1; !f(i))
              @    && (\forall int i; 0 <= i && i < x-1; !f(i));
              @*/
            //@ hence_by (* joining the range *);
            /*@ assert 0 <= x && 
              @        (\forall int i; (0 <= i && i < x-1) || i == x-1; !f(i));
              @*/
            //@ hence_by (* arithmetic *);
            //@ assert 0 <= x && (\forall int i; 0 <= i && i < x; !f(i));
        }
        /*@ assert 0 <= x && f(x)
          @     && (\forall int i; 0 <= i && i < x; !f(i));
          @*/
        //@ hence_by (* definition of \min *);
        //@ assert x == (\min int i; 0 <= i && f(i); i);
        return x;
    }
}
