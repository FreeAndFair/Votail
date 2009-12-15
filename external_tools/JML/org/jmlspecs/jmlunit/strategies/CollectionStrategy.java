// @(#)$Id: CollectionStrategy.java,v 1.4 2005/07/07 21:03:04 leavens Exp $

// Copyright (C) 2005 Iowa State University
//
// This file is part of the runtime library of the Java Modeling Language.
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation; either version 2.1,
// of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with JML; see the file LesserGPL.txt.  If not, write to the Free
// Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
// 02110-1301  USA.

package org.jmlspecs.jmlunit.strategies;

import java.util.*;

/** A small extensible strategy for producing test data of type
 * Collection.  This provides <kbd>null</kbd>, a small HashSet and an
 * empty Vector.
 *
 * <p>To extend this strategy with additional data,
 * override the {@link #make(int)} method.
 *
 * @author Gary T. Leavens
 */
public class CollectionStrategy
    extends NewObjectAbstractExtensibleStrategyDecorator
{
    /** Initialize this strategy */
    public CollectionStrategy() {
        super(
              new NewObjectAbstractStrategy()
              {
                  protected Object make(int n) {
                      switch (n) {
                      case 0:
                          HashSet s1 = new HashSet();
                          s1.add("");
                          s1.add(new Float(3.14159f));
                          return s1;
                      case 1:
                          return new ArrayList();
                      default:
                          break;
                      }
                      throw new NoSuchElementException();
                  }
              }
              );
    }
}
