// @(#)$Id: byteAbstractFilteringIteratorDecorator.java-generic,v 1.11 2005/12/24 21:20:31 chalin Exp $

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

import java.util.NoSuchElementException;

/** An filtering decorator for an indefinite iterator over type byte.
 * @author Gary T. Leavens
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public abstract class ByteAbstractFilteringIteratorDecorator
    extends ByteAbstractIterator
{
    private /*@ spec_public non_null @*/ ByteIterator rawElems;
    //@ in objectState; maps rawElems.objectState \into objectState;

    //@ public ghost boolean dented = false;

    //@ public invariant !dented ==> (atEnd() <==> rawElems.atEnd());
    /*@ public invariant !dented ==>
      @                   (!atEnd() ==> get().equals(rawElems.get()));
      @ public invariant_redundantly !dented ==>
      @                 (!atEnd() ==>
      @                 new Byte(getByte())
      @                 .equals(new Byte(rawElems.getByte())));
      @*/

    /** Initialize this iterator decorator */
    /*@ public normal_behavior
      @   requires iter != null;
      @   assignable rawElems, objectState, owner;
      @   ensures (* rawElems is a clone of iter *);
      @   ensures owner == null;
      @*/
    public ByteAbstractFilteringIteratorDecorator
        (ByteIterator iter)
    {
        rawElems = (ByteIterator) iter.clone();
        //@ set rawElems.owner = this;
        //@ set owner = null;
        setCursor();
    }

    /** Partially intialize this iterator decorator, with a call to
     * initialize needed after this call. */
    /*@ public normal_behavior
      @   requires iter != null;
      @   assignable rawElems, dented, owner;
      @   ensures (* rawElems is a clone of iter *) && dented;
      @   ensures owner == null;
      @*/
    public ByteAbstractFilteringIteratorDecorator
        (ByteIterator iter, byte ignored)
    {
        //@ set dented = true;
        rawElems = (ByteIterator) iter.clone();
        //@ set rawElems.owner = this;
        //@ set owner = null;
    }

    /** Complete initialization of this object. */
    //@ assignable objectState, dented;
    //@ ensures !dented;
    //@ ensures !atEnd() ==> approve(getByte());
    public void initialize() {
        setCursor();
        //@ set dented = false;
    }

    /** Set the cursor to the next element that is approved, if any. */
    //@ assignable objectState;
    //@ ensures !rawElems.atEnd() ==> approve(rawElems.getByte());
    private void setCursor() {
        while (!rawElems.atEnd() && !approve(rawElems.getByte())) {
            rawElems.advance();
        }
    }

    /** Return true if the element is to be returned by the
     * getByte() method. */
    //@ public normal_behavior
    //@   assignable \nothing;
    public abstract /*@ pure @*/ boolean approve(byte elem);

    // doc comment inherited
    /*@ also public normal_behavior
      @   assignable \nothing;
      @   ensures \result == rawElems.atEnd();
      @*/
    public /*@ pure @*/ boolean atEnd() {
        return rawElems.atEnd();
    }

    /** Return the current approved element. */
    public /*@ pure @*/ byte getByte()
        throws NoSuchElementException
    {
        return rawElems.getByte();
    }

    // doc comment inherited
    //@ also public normal_behavior
    //@   assignable objectState;
    //@   ensures !atEnd() ==> approve(getByte());
    public void advance() {
        rawElems.advance();
        setCursor();
    }

    public /*@ non_null @*/ Object clone() {
        ByteAbstractFilteringIteratorDecorator ret
            = (ByteAbstractFilteringIteratorDecorator) super.clone();
        ret.rawElems = (ByteIterator) rawElems.clone();
        return ret;
    }

    public /*@ non_null @*/ String toString() {
        return "ByteAbstractFilteringIteratorDecorator("
            + rawElems + ")";
    }
}
