// @(#)$Id: SumArrayLoop.java,v 1.6 2007/07/01 14:17:58 chalin Exp $

// Copyright (C) 2005 Iowa State University

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


package org.jmlspecs.samples.jmlrefman;

/** An example of some simple loops with loop invariants
 *  and variant functions specified.
 */
public abstract class SumArrayLoop {

    /** Return the sum of the argument array. */
    /*@   old \bigint sum = 
      @		(\sum int j; 0 <= j && j < a.length; (\bigint)a[j]);
      @   requires Long.MIN_VALUE <= sum && sum <= Long.MAX_VALUE;
      @   assignable \nothing;
      @   ensures \result == sum;
      @*/
    public static long sumArray(int [] a) {
        long sum = 0;
        int i = a.length;

        /*@ maintaining -1 <= i && i <= a.length;
          @ maintaining sum
          @            == (\sum int j; 
          @                   i <= j && 0 <= j && j < a.length; 
          @                   (\bigint)a[j]);
          @ decreasing i; @*/
        while (--i >= 0) {
            sum += a[i];
        }

        //@ assert i < 0 && -1 <= i && i <= a.length;
        //@ hence_by (i < 0 && -1 <= i) ==> i == -1;
        //@ assert i == -1 && i <= a.length;
        //@ assert sum == (\sum int j; 0 <= j && j < a.length; (\bigint)a[j]);
        return sum;
    }

}
