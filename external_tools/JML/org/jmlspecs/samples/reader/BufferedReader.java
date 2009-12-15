// @(#)$Id: BufferedReader.java,v 1.4 2004/01/06 11:30:21 davidcok Exp $

// Copyright (C) 2003 Iowa State University

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


package org.jmlspecs.samples.reader;

/** Buffered readers.
 * @author Arnd Poetzsch-Heffter
 *         from an example by K. Rustan M. Leino and Greg Nelson, in
 *         Data abstraction and information hiding,
 *         ACM Transactions on Programming Languages and Systems,
 *         Volume 24, number 5, pp. 491-553, September 2002.
 */
public abstract class BufferedReader implements Reader {

  protected /*@ spec_public @*/ int lo, hi;
  //@                               in valid, state, svalid;
  protected /*@ spec_public @*/ int cur;
  //@                               in valid, state;
  protected /*@ spec_public @*/ char[] buff;
  //@                               in valid, state, svalid;
  //@                               maps buff[*] \into state;
  
  //@ public model boolean svalid;           in valid;

  /*@ public represents valid <-
    @  this != null  &&
    @  0 <= lo  &&  lo <= cur  &&  cur <= hi  &&
    @  buff != null  &&  hi-lo <= buff.length &&
    @  svalid ;
    @*/


  public int read() {
    if( cur == hi ) refill();
    if( cur == hi )
      return -1;
    else {
      int result = buff[cur-lo];
      cur++;
      return result;
    }
  }


  /*@ public normal_behavior
    @   requires    valid;
    @   assignable  state;
    @   ensures     cur == \old(cur) ;
    @*/
  public abstract void refill();

  
}


