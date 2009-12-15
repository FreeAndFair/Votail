// @(#)$Id: ObjectStrategy.java,v 1.7 2007/12/19 01:59:43 chalin Exp $

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

/** A minimal, extensible strategy for producing test data of type
 * {@link java.lang.Object}.  This just provides just
 * <kbd>null</kbd> and <kbd>new Object()</kbd>.
 *
 * <p>To extend this strategy with additional data,
 * override the {@link #make(int)} method.
 *
 * @author Gary T. Leavens
 */
public class ObjectStrategy
    extends NewObjectAbstractExtensibleStrategyDecorator
{
    /** Initialize this strategy */
    public ObjectStrategy() {
        super(
              new StrategyType()
              {
                  public /*@non_null*/ IndefiniteIterator iterator() {
                      return new ImmutableObjectArrayIterator
                          // note that new Object() can't be modified.
                          (new Object[] { null, new Object(), });
                  }
              }
              );
    }
}
