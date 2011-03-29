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
 * This class divvies out the votes using the next available 
 * preference on each ballot. The votes are not actually given
 * to the candidates until distribute() is called.
 *
 * Lifecycle:
 *
 * RANDOM  create --> distribute
 *
 * FRACTIONAL create --> reduceValue --> distribute
 *
 * 	create takes the lastset (or complete set) of ballots belonging
 * 	to a candidate and finds the next available preference for each ballot
 *	A new map containing all ballots in the original set, but divided out
 *	among all other candidates is created. 
 *
 *	The Surplus class then calculates the correct number from each element
 *	of the map to carry forward.
 */

public class CandidateBallotMap extends HashMap<Candidate,BallotList> {

    int n;

    public void addBallot (Candidate c, Ballot b) {
	BallotList list = get(c);
	if (list == null) {
	    list = new BallotList();
	    put (c, list);
	}
	list.add (b);
    }

    /* get the ballots destined for candidate c */

    public BallotList getList (Candidate c) {
	return get(c);
    }

    /* create a map from a list of ballots. The map is indexed
     * by candidate and contains a list of ballots for that
     * candidate
     */
    public static CandidateBallotMap create (BallotList ballots) {
	int i = 0;
    	CandidateBallotMap map = new CandidateBallotMap ();
	for (Ballot b : ballots) {
	    if (b.getValue() == 0) {
		continue;
	    }
	    Candidate c = b.getNextPreference ();
	    if (c != null) {
	    	map.addBallot (c, b);
		i+=b.getValue();
	    }
	}
	map.n = i;
	return map;
    }

    public int totalVotes() {
	return n;
    }

    /* distribute the votes in this map among the candidates
     * and then clear the map
     */
    public void distribute () {
	int i=0;
	Set<Candidate> keys = keySet();
	for (Candidate c : keys) {
	    BallotList b = get(c);
	    c.addVotes (get(c));
	    i+=b.value();
	}
	clear();
	Display.log ("Distributed " + Election.fmt(i) + " votes");
    }

    /*
     * remaining is the number of ballots to leave in the map
     * for the candidate. The group of votes at the end of the map
     * are left.
     */
    public void reduceRandom (Candidate c, int remaining) {
	BallotList m = get(c);
	int size = m.size();
	assert remaining <= size;
	m.subList (0, size-remaining).clear();
	m.invalidateCache();
    }

    /* in a fractional count, reduce the value of each ballot
     * by the designated amount. If any ballots have a lower
     * value than the requested amount then then a tally of the
     * missing value is kept, and the operation is repeated for
     * the remaining ballots (which have higher value) until
     * the entire (initial) amount has been deducted.
     */
    public void reduceFractional (int amount, int nballots) {
	int zapme = 0;
	Display.log ("Surplus vote reduction");
    	Display.tableStart (true);
    	Display.tableRow (new Object[]{"Iteration", "Ballot value reduction", "Residue"});
	while (amount > 0) {
	    zapme ++;
	    assert zapme < 10;
	    int residual = 0;
	    for (Candidate c : keySet()) {
	        BallotList blist = get(c);
	        for (Ballot b : blist) {
		    residual += b.reduceValue (amount);
	        }
	    }
	    Display.tableRow (new Object[]{Integer.toString(zapme), 
					   Election.fmt(amount), 
					   Election.fmt(residual)});
	    amount = residual /nballots;
	}
	Display.tableEnd();
	Display.log("<p>");
    }

    public String toString() {
	StringBuffer b = new StringBuffer();
	b.append ("[");
	int total = 0;
	Set<Candidate> keys = keySet();
	for (Candidate c : keys) {
	    BallotList bl = get(c);
	    total += bl.value();
	    b.append (c.name()+":"+bl.value()+",");
	}
  	b.append ("("+total+")]");
 	return new String (b);
    }
}
