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

/**
 * represents a candidate. Includes the persons name. 
 * the status during the election. Current list of votes
 * and if elected a list of surplus votes to be redistributed
 */
public class Candidate implements Comparable<Candidate> {
    private String name;
    private static volatile int quota;
    /* this candidates votes is votes+lastSet */
    private BallotList votes;
    private BallotList lastSet; /* the last set received */
    private Surplus surplus; /* this candidates surplus if elected */
    private Status status;
    private int count;	/* count elected/eliminated in */
    ArrayList<Integer> votesAtCount;
    private int index;

    /* set to true for all-vote fractional. ie. all votes
     * in a candidates pile are used for surplus transfers
     * If false, only the last set is used
     */
    public static boolean useAllVotesForSurplus = false;

    Candidate (String name, int index) {
	this.name = name;
	status = Status.INRACE;
	votes = new BallotList();
	lastSet = new BallotList();
	votesAtCount = new ArrayList<Integer>();
	this.index = index;
    }

    /* needed for sorting 
     */
    public int compareTo (Candidate o) {
	if (status != Status.INRACE) {
	    return -1;
	}
	int s1 = nvotes();
	int s2 = o.nvotes();
	if (s1 > s2) {
	    return 1;
	} else if (s1 < s2) {
	    return -1;
	} else {
	    return 0;
	}
    }

    static void setQuota (int q) {
	quota = q;
    }

    void addVotes (BallotList v) {
	if (lastSet != null) {
	    /* merge lastset with main set of votes */
	    votes.addAll (lastSet);
	}
	lastSet = v;
    }

    public String name () {
	return name;
    }

    public String toString () {
	return "name: "+ name + " votes: " +nvotes();
    }

    public int count () {
	return count;
    }

    public int index () {
	return index;
    }

    /* calculate the Candidates status and return it */

    Status status () {
	if (status == Status.INRACE) {
	    int size = nvotes();
	    if (size>=quota) {
		status = Status.ELECTED;
		BallotList bl = useAllVotesForSurplus? votes(): lastSet;
	    	surplus = new Surplus (bl, size, quota);
	    }
	}
	return status;
    }

    void setCount (int count) {
	this.count = count;
    }

    /* record the current number of votes as the final amount
     * for the indicated count */

    void rememberVotesAtCount (int count) {
	assert votesAtCount.size() == count -1;
	votesAtCount.add (count-1, nvotes());
    }

    /* return number of votes recorded at the indicated count */

    int votesAtCount (int count) {
	return votesAtCount.get (count-1);
    }
	
    /* eliminate this candidate */

    void eliminate () {
	if (status != Status.INRACE) {
	    return;
	}
	status = Status.ELIMINATED;
    }
 
    BallotList votes() {
	if (lastSet != null) {
	    votes.addAll (lastSet);
	    lastSet = new BallotList();
	}
	return votes;
    }

    int nvotes() {
	return votes.value()+lastSet.value();
    }

    Surplus surplus() {
	return surplus;
    }
}
