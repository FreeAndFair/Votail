// @(#)$Id: ReaderTest.java,v 1.1 2003/02/18 17:07:17 leavens Exp $

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

/** Tests for the readers example.
 * @author Arnd Poetzsch-Heffter
 *         from an example by K. Rustan M. Leino and Greg Nelson, in
 *         Data abstraction and information hiding,
 *         ACM Transactions on Programming Languages and Systems,
 *         Volume 24, number 5, pp. 491-553, September 2002.
 */
public class  ReaderTest {
  
  /** Run the tests. */
  public static void main( String[] args ) {

    int EXPECTED = 1000000;
    Reader rd = new BlankReader(EXPECTED);

    int count = 0;
    int chr;
    do {
      chr = rd.read();
      count++;
    } while( chr != -1 );
    rd.close();
    if (count == EXPECTED+1) {
        System.out.println("Test passed");
    } else {
        System.out.println("Failure: count was " + count);
    }
  }  
}









