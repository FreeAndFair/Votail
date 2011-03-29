/**
 *  Copyright 2005 Michael McMahon
 *
 *  This file is part of STVCounter
 *
 *  STVCounter is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  STVCounter is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with Foobar.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.hexmedia.prstv;

import java.util.*;

/*
public class BallotList {

    LinkedList<Ballot> ballots;
    int cached_value = -1;

    public BallotList() {
	ballots = new LinkedList<Ballot>();
    }

    public boolean add (Ballot b) {
	boolean b = ballots.add (b);
	cached_value = -1;
	return b;
    }

    //
    // return the total value of the ballots in the list
    //
    public int value () {
	if (cached_value != -1) {
	    return cached_value;
	}
	int value = 0;
	for (Ballot b : ballots) {
	    value += b.getValue();
	}
	cached_value = value;
	return value;
    }
}	
*/

public class BallotList extends LinkedList<Ballot> {

    int cached_value = -1;

    public BallotList() {
    }

    public boolean add (Ballot b) {
	boolean r = super.add (b);
	cached_value = -1;
	return r;
    }

    public boolean addAll (BallotList b) {
	boolean r = super.addAll (b);
	cached_value = -1;
	return r;
    }

    /* force object to recompute value */

    public void invalidateCache() {
	cached_value = -1;
    }

    //
    //return the total value of the ballots in the list
    //
    public int value () {
	if (cached_value != -1) {
	    return cached_value;
	}
	int value = 0;
	for (Ballot b : this) {
	    value += b.getValue();
	}
	cached_value = value;
	return value;
    }
}	
