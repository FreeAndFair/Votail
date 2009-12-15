// @(#)$Id: Proof.java,v 1.3 2004/11/22 04:55:48 leavens Exp $

// Copyright (C) 2000 Iowa State University

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

/** A class that demonstrates Floyd-Hoare-style proofs using JML
 * notation.  This was originally used as an exercise for a class at
 * the University of Iowa.
 * @author Gary T. Leavens */
public class Proof {

    /** A variable to keep track of the minimum. */
    protected /*@ spec_public @*/ int min = Integer.MAX_VALUE;

    /** Exercise 1: find the minimum element in an array. */
    /*@ public normal_behavior
      @   requires a != null && a.length >= 1;
      @   assignable min;
      @   ensures (\forall int i; 0 <= i && i < a.length; min <= a[i])
      @      && (\exists int i; 0 <= i && i < a.length; min == a[i]);
      @*/
    public void find_min (int a[])
    {
        //@ assert a != null && a.length >= 1;
        //@ hence_by (* predicate calculus, arithmetic *);
        /*@ assert (\forall int i; 0 <= i && i < 1; a[0] <= a[i])
          @   && (\exists int i; 0 <= i && i < 1; a[0] == a[i])
          @   && a.length >= 1;
          @*/
        min = a[0];
        /*@ assert (\forall int i; 0 <= i && i < 1; min <= a[i])
          @   && (\exists int i; 0 <= i && i < 1; min == a[i])
          @   && a.length >= 1;
          @*/
        int j = 1;
        /*@ assert (\forall int i; 0 <= i && i < j; min <= a[i])
          @   && (\exists int i; 0 <= i && i < j; min == a[i])
          @   && a.length >= j;
          @*/
        //@ hence_by (* algebra *);
        /*@ assert (\forall int i; 0 <= i && i < j; min <= a[i])
          @   && (\exists int i; 0 <= i && i < j; min == a[i])
          @   && j < a.length + 1;
          @*/
        /*@ maintaining (\forall int i; 0 <= i && i < j; min <= a[i])
          @   && (\exists int i; 0 <= i && i < j; min == a[i])
          @   && j < a.length + 1;
          @ decreasing a.length - j;
          @*/
        while (j < a.length) {
            //@ ghost final int m = a.length - j;
            /*@ assert (\forall int i; 0 <= i && i < j; min <= a[i])
              @   && (\exists int i; 0 <= i && i < j; min == a[i])
              @   && j < a.length + 1
              @   && j < a.length 
              @   && (a.length - j) <= m;
              @*/
            /*@ hence_by ((j < a.length && (a.length - j) <= m) 
              @   ==> (0 < a.length - j && (a.length - j) <= m)
              @   ==> (0 <= m && (a.length - j) <= m))
              @   && (j < a.length + 1 && j < a.length ==> j < a.length);
              @*/
            /*@ assert (\forall int i; 0 <= i && i < j; min <= a[i])
              @   && (\exists int i; 0 <= i && i < j; min == a[i])
              @   && j < a.length
              @   && 0 <= m && (a.length - j) <= m;
              @*/
            if (a[j] < min) {
                /*@ assert (\forall int i; 0 <= i && i < j; min <= a[i])
                  @   && (\exists int i; 0 <= i && i < j; min == a[i])
                  @   && j < a.length
                  @   && 0 <= m && (a.length - j) <= m
                  @   && a[j] < min;
                  @*/
                //@ hence_by (* algebra *);
                /*@ assert (\forall int i; 0 <= i && i < (j+1) ==> a[j] <= a[i])
                  @   && (\exists int i; 0 <= i && i < (j+1) && a[j] == a[i])
                  @   && j+1 < a.length + 1
                  @   && 0 <= m && (a.length - (j+1)) < m;
                  @*/
                min = a[j];
                /*@ assert (\forall int i; 0 <= i && i < (j+1) ==> min <= a[i])
                  @   && (\exists int i; 0 <= i && i < (j+1) && min == a[i])
                  @   && j+1 < a.length + 1
                  @   && 0 <= m && (a.length - (j+1)) < m;
                  @*/
            }
            /*@ assert (\forall int i; 0 <= i && i < (j+1) ==> min <= a[i])
              @   && (\exists int i; 0 <= i && i < (j+1) && min == a[i])
              @   && j+1 < a.length + 1
              @   && 0 <= m && (a.length - (j+1)) < m;
              @*/
            j = j + 1;
            /*@ assert (\forall int i; 0 <= i && i < j; min <= a[i])
              @   && (\exists int i; 0 <= i && i < j; min == a[i])
              @   && j < a.length + 1
              @   && 0 <= m && (a.length - j) < m;
              @*/
        }
        /*@ assert (\forall int i; 0 <= i && i < j; min <= a[i])
          @   && (\exists int i; 0 <= i && i < j; min == a[i])
          @   && j < a.length + 1
          @   && j >= a.length;
          @*/
        //@ hence_by (* algebra *);
        /*@ assert (\forall int i; 0 <= i && i < j; min <= a[i])
          @   && (\exists int i; 0 <= i && i < j; min == a[i])
          @   && j == a.length;
          @*/
        //@ hence_by (* algebra *);
        /*@ assert (\forall int i; 0 <= i && i < a.length; min <= a[i])
          @   && (\exists int i; 0 <= i && i < a.length; min == a[i]);
          @*/
    }

    /** The index where the element occurs for exercise 2. */
    private /*@ spec_public @*/ int res = 0;

    /** Return the value of res */
    public int getRes() { return res; }

    /** Exercise 2: find the index of an integer in an array. */
    /*@ public normal_behavior
      @   requires a != null
      @      && (\exists int i; 0 <= i && i < a.length; a[i] == x);
      @   assignable res;
      @   ensures 0 <= res && res < a.length && a[res] == x;
      @*/
    public void find(int a[], int x)
    {
        /*@ assert a != null
          @   && (\exists int i; 0 <= i && i < a.length; a[i] == x);
          @*/
        //@ hence_by (* predicate calculus *);
        /*@ assert ((\exists int i; 0 <= i && i < 0;
          @                          a[i] == x && res == i)
          @          || (\exists int i; 0 <= i && i < a.length;
          @                             a[i] == x))
          @   && 0 < a.length + 1;
          @*/
        int j = 0;
        /*@ assert ((\exists int i; 0 <= i && i < j;
          @                          a[i] == x && res == i)
          @               || (\exists int i; j <= i && i < a.length;
          @                                  a[i] == x))
          @   && j < a.length + 1;
          @*/
        /*@ maintaining ((\exists int i; 0 <= i && i < j;
          @                               a[i] == x && res == i)
          @               || (\exists int i; j <= i && i < a.length;
          @                                  a[i] == x))
          @   && j < a.length + 1;
          @ decreasing a.length - j;
          @*/
        while (j < a.length) {
            //@ ghost final int m = a.length - j;
            /*@ hence_by j < a.length ==> j <= a.length+1
              @       && a.length - j == m;
              @*/
            /*@ assert ((\exists int i; 0 <= i && i < j;
              @                          a[i] == x && res == i)
              @          || (\exists int i; j <= i && i < a.length;
              @                             a[i] == x))
              @   && j <= a.length + 1
              @   && j < a.length
              @   && a.length - j <= m;
              @*/
            /*@ hence_by (j < a.length && (a.length - j) <= m) 
              @      ==> (0 < a.length - j && (a.length - j) <= m);
              @*/
            /*@ assert ((\exists int i; 0 <= i && i < j;
              @                          a[i] == x && res == i)
              @          || (\exists int i; j <= i && i < a.length;
              @                             a[i] == x))
              @   && j <= a.length + 1
              @   && j < a.length
              @   && 0 < a.length - j
              @   && a.length - j <= m;
              @*/
            /*@ hence_by ((0 < a.length - j && (a.length - j) <= m)
              @           ==> (0 <= m))
              @   && (j < a.length + 1 && j < a.length ==> j < a.length);
              @*/
            /*@ assert ((\exists int i; 0 <= i && i < j;
              @                          a[i] == x && res == i)
              @          || (\exists int i; j <= i && i < a.length;
              @                             a[i] == x))
              @   && j < a.length
              @   && 0 <= m && a.length - j <= m;
              @*/

            if (a[j] == x) {
                /*@ assert ((\exists int i; 0 <= i && i < j;
                  @                          a[i] == x && res == i)
                  @          || (\exists int i; j <= i && i < a.length;
                  @                             a[i] == x))
                  @   && j < a.length
                  @   && 0 <= m && a.length - j <= m
                  @   && a[j] == x;
                  @*/
                //@ hence_by (* predicate calculus *);
                /*@ assert ((\exists int i; 0 <= i && i < j;
                  @                          a[i] == x && res == i)
                  @          || (\exists int i; j <= i && i < j+1;
                  @                             a[i] == x && j == i)
                  @          || (\exists int i; j+1 <= i && i < a.length;
                  @                             a[i] == x))
                  @   && j < a.length
                  @   && 0 <= m && a.length - j <= m
                  @   && a[j] == x;
                  @*/
      
                res = j;
                /*@ assert ((\exists int i; 0 <= i && i < j;
                  @                          a[i] == x && res == i)
                  @          || (\exists int i; j <= i && i < j+1;
                  @                             a[i] == x && res == i)
                  @          || (\exists int i; j+1 <= i && i < a.length; 
                  @                             a[i] == x))
                  @   && j < a.length
                  @   && 0 <= m && a.length - j <= m
                  @   && a[res] == x;
                  @*/
                //@ hence_by (* predicate calculus *);
                /*@ assert ((\exists int i; 0 <= i && i < j+1;
                  @                          a[i] == x && res == i)
                  @          || (\exists int i; j+1 <= i && i < a.length;
                  @                             a[i] == x))
                  @   && j < a.length
                  @   && 0 <= m && a.length - j <= m;
                  @*/

            }
            else {
                /*@ assert ((\exists int i; 0 <= i && i < j;
                  @                          a[i] == x && res == i)
                  @          || (\exists int i; j <= i && i < a.length;
                  @                             a[i] == x))
                  @   && j < a.length
                  @   && 0 <= m && a.length - j <= m
                  @   && a[j] != x;
                  @*/
                //@ hence_by (* predicate calculus *);
                /*@ assert ((\exists int i; 0 <= i && i < j+1;
                  @                          a[i] == x && res == i)
                  @          || (\exists int i; j+1 <= i && i < a.length;
                  @                             a[i] == x))
                  @   && j < a.length
                  @   && 0 <= m && a.length - j <= m;
                  @*/
            }
            /*@ assert ((\exists int i; 0 <= i && i < j+1; 
              @                          a[i] == x && res == i)
              @          || (\exists int i; j+1 <= i && i < a.length;
              @                             a[i] == x))
              @   && j < a.length
              @   && 0 <= m && a.length - j <= m;
              @*/
            //@ hence_by (* algebra *);
            /*@ assert ((\exists int i; 0 <= i && i < j+1;
              @                          a[i] == x && res == i)
              @          || (\exists int i; j+1 <= i && i < a.length;
              @                             a[i] == x))
              @   && (j+1) < a.length + 1
              @   && 0 <= m && a.length - (j+1) < m;
              @*/

            j = j + 1;
            /*@ assert ((\exists int i; 0 <= i && i < j;
              @                          a[i] == x && res == i)
              @          || (\exists int i; j <= i && i < a.length;
              @                             a[i] == x))
              @   && j < a.length + 1
              @   && 0 <= m && a.length - j < m;
              @*/
        }
        /*@ assert ((\exists int i; 0 <= i && i < j;
          @                          a[i] == x && res == i)
          @          || (\exists int i; j <= i && i < a.length;
          @                             a[i] == x))
          @   && j < a.length + 1
          @   && j >= a.length;
          @*/

        //@ hence_by (* algebra *);
        /*@ assert ((\exists int i; 0 <= i && i < j;
          @                          a[i] == x && res == i)
          @          || (\exists int i; j <= i && i < a.length;
          @                             a[i] == x))
          @   && j == a.length;
          @*/
        //@ hence_by (* algebra *);
        /*@ assert ((\exists int i; 0 <= i && i < a.length;
          @                          a[i] == x && res == i)
          @          || (\exists int i; a.length <= i && i < a.length;
          @                             a[i] == x));
          @*/
        //@ hence_by (* predicate calculus *);
        /*@ assert (\exists int i; 0 <= i && i < a.length;
          @                         a[i] == x && res == i);
          @*/
        //@ hence_by (* predicate calculus *);
        //@ assert 0 <= res && res < a.length && a[res] == x;
    }

}
