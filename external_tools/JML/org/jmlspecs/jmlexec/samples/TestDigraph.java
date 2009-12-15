/*
 * @(#)$Id: TestDigraph.java,v 1.1 2008/03/05 00:13:50 wahlst Exp $
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

public class TestDigraph {

  public static void main(String args []) {
    Node n = new Node(1);
    Node n2 = new Node(2);
    Digraph d = new Digraph();
    d.addNode(n);
    Node n3 = new Node(3);
    Node n4 = new Node(4);
    d.addNode(n2);
    d.addNode(n3);
    d.addNode(n4);
    System.out.println("added nodes");
    d.addArc(new ArcType(n, n2));
    System.out.println("added arcs");
    System.out.println(d.isAPath(n3, n));
    System.out.println(d.isAPath(n, n2));
    System.out.println(d.unconnected(n2));
    System.out.println(d.unconnected(n4));
  }
}
