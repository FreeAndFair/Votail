// @(#)$Id: PriorityQueue.java,v 1.9 2007/11/13 11:48:41 chalin Exp $

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


package org.jmlspecs.samples.jmlkluwer;

//@ refine "PriorityQueue.java-refined";

import java.util.ArrayList;
import java.util.Iterator;
//@ model import org.jmlspecs.models.JMLValueSet;

public class PriorityQueue implements PriorityQueueUser {

    private /*@ non_null \rep @*/ ArrayList levels
        = new /*@ \rep @*/ ArrayList();
        //@ in entries; maps levels.theCollection \into entries;

    /*@ private invariant
      @    (\forall int i; 0 <= i && i < levels.size();
      @         levels.get(i) instanceof ArrayList
      @         && !((ArrayList)levels.get(i)).isEmpty()
      @         && (\forall int j;
      @               0 <= j && j < ((ArrayList)levels.get(i)).size();
      @               ((ArrayList)levels.get(i)).get(j) instanceof QueueEntry
      @               && ((QueueEntry)((ArrayList)levels.get(i)).get(j))
      @                    .getLevel()
      @                     ==
      @                    ((QueueEntry)((ArrayList)levels.get(i)).get(0))
      @                    .getLevel())
      @         && (\forall int k; 0 <= k && k < i;
      @                getLevelOf(levels.get(k)) < getLevelOf(levels.get(i))));
      @*/

    /*@ private represents entries <- abstractValue();
      @*/

    /*@ private pure model JMLValueSet abstractValue() {
      @    JMLValueSet v = new JMLValueSet();
      @    Iterator levelsIter = levels.iterator();
      @    while (levelsIter.hasNext()) {
      @        ArrayList levelList = (ArrayList)levelsIter.next();
      @        Iterator iter = levelList.iterator();
      @        while (iter.hasNext()) {
      @           v = v.insert((QueueEntry)iter.next());
      @        }
      @    }
      @    return v;
      @ }
      @*/

    private long nextTS = 0L; //@ in entries;

    //@ public invariant_redundantly -1L <= largestTimeStamp();
    //@ private invariant nextTS == largestTimeStamp() + 1;
    //@ private invariant_redundantly 0L <= nextTS;

    public PriorityQueue() {}

    public void addEntry(Object argObj, int argPriorityLevel)
        throws PQException
    {
        if (nextTS == Long.MAX_VALUE) {
            throw new IllegalStateException();
        }
        if (argObj == null || argPriorityLevel < 0 || contains(argObj)) {
            throw new PQException();
        }

        ArrayList thisLevel = getLevelList(argPriorityLevel);
        thisLevel.add(new /*@ \rep @*/ QueueEntry(argObj, argPriorityLevel,
                                                  nextTS));
        //@ assert nextTS < Long.MAX_VALUE;
        nextTS += 1;
    }

    /*@  private normal_behavior
      @   requires (\exists int i; 0 <= i && i < levels.size();
      @                   levels.get(i) != null
      @                && ((QueueEntry)((ArrayList)levels.get(i)).get(0))
      @                                .priorityLevel == argPriorityLevel);
      @   assignable \nothing;
      @   ensures levels.theCollection.has(\result);
      @ also
      @  private normal_behavior
      @   requires !(\exists int i; 0 <= i && i < levels.size();
      @                   levels.get(i) != null
      @                && ((QueueEntry)((ArrayList)levels.get(i)).get(0))
      @                                .priorityLevel == argPriorityLevel);
      @   assignable levels.theCollection;
      @   ensures \fresh(\result) && levels.theList.has(\result);
      @   ensures (\forall int i; 0 <= i && i < levels.size();
      @                 levels.get(i) == \result
      @              || (\old(levels.theList).has(levels.get(i))
      @                  && (\old(levels.theList).get(i)
      @                       .equals(levels.get(i))
      @                      || \old(levels.theList).get(i-1)
      @                           .equals(levels.get(i)))));
      @*/
    private /*@ helper \rep @*/ ArrayList getLevelList(int argPriorityLevel) {
        int i = 0;
        /*@ maintaining i <= levels.size();
          @ maintaining (\forall int j; 0 <= j && j < i;
          @                   getLevelOf(levels.get(j)) < argPriorityLevel);
          @*/
        while (i < levels.size()) {
            ArrayList levelList = (ArrayList) levels.get(i);
            if (getLevelOf(levelList) == argPriorityLevel) {
                return levelList;
            } else if (getLevelOf(levelList) > argPriorityLevel) {
                break;
            }
            i++;
        }
        ArrayList newLevel = new /*@ \rep @*/ ArrayList();
        levels.add(i, newLevel);
        return newLevel;
    }

    //@ requires levelList != null && !levelList.isEmpty();
    //@ assignable \nothing;
    private /*@ helper pure @*/ int getLevelOf(ArrayList levelList) {
        return ((QueueEntry)levelList.get(0)).getLevel();
    }

    //@ requires levelList instanceof ArrayList;
    //@ requires !((ArrayList)levelList).isEmpty();
    //@ assignable \nothing;
    private /*@ helper pure @*/ int getLevelOf(Object levelList) {
        return getLevelOf((ArrayList) levelList);
    }
    
    public /*@ pure @*/ boolean contains(Object argObj) {
        Iterator levelsIter = levels.iterator();
        while (levelsIter.hasNext()) {
            ArrayList levelList = (ArrayList)levelsIter.next();
            Iterator elemIter = levelList.iterator();
            while (elemIter.hasNext()) {
                QueueEntry qe = (QueueEntry)elemIter.next();
                if (qe.getObj() == argObj) {
                    return true;
                }
            }
        }
        return false;
    }

    public /*@ pure @*/ Object next() throws PQException {
        if (isEmpty()) {
            throw new PQException();
        }
        ArrayList highest = (ArrayList)levels.get(levels.size() - 1);
        return ((QueueEntry)highest.get(0)).getObj();
    }

    public void remove(Object argObj) {
        Iterator levelsIter = levels.iterator();
        while (levelsIter.hasNext()) {
            ArrayList levelList = (ArrayList)levelsIter.next();
            Iterator elemIter = levelList.iterator();
            while (elemIter.hasNext()) {
                QueueEntry qe = (QueueEntry)elemIter.next();
                if (qe.getObj() == argObj) {
                    elemIter.remove();
                    break;
                }
            }
            if (levelList.isEmpty()) {
                levelsIter.remove();
            }
        }
        if (levels.isEmpty()) {
            nextTS = 0;
        }
    }

    public /*@ pure @*/ boolean isEmpty() {
        return levels.size() == 0;
    }

    public String toString() {
        StringBuffer ret = new StringBuffer();
        ret.append("PriorityQueue {");
        Iterator levelsIter = levels.iterator();
        while (levelsIter.hasNext()) {
            ArrayList levelList = (ArrayList)levelsIter.next();
            Iterator elemIter = levelList.iterator();
            ret.append("   level ");
            ret.append(getLevelOf(levelList));
            ret.append(": ");
            while (elemIter.hasNext()) {
                QueueEntry qe = (QueueEntry)elemIter.next();
                ret.append(qe.toString());
                ret.append(", ");
            }
            ret.append("\n");
        }
        ret.append("}");
        return ret.toString();
    }
}
