/*
 * @(#)$Id: TestGraph.java,v 1.1 2008/03/05 00:13:50 wahlst Exp $
 *
 * Copyright (C) 2006 Iowa State University
 *
 * This file is part of JML
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 */

package org.jmlspecs.jmlexec.samples;

public class TestGraph {
  public static void main(String argv[]) {
    Integer i1, i2, i3, i4;
    i1 = new Integer(1);
    i2 = new Integer(2);
    i3 = new Integer(3);
    i4 = new Integer(4);

    Graph g = new Graph();
    g.addVertex(i1);
    g.addVertex(i2);
    g.addVertex(i3);
    g.addVertex(i4);

    g.addEdge(i1, i2);
    g.addEdge(i1, i3);
    g.addEdge(i2, i3);
    g.addEdge(i1, i4);

    System.out.println(g);
    Object [] res = g.clique(3);
    for (int i = 0; i < res.length; i++) {
      System.out.print(res[i] + " ");
    }
    System.out.println();
//    Object [] res2 = g.clique(4);
 
  }
}
