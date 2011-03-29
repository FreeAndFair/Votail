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
 * A ballot with an ordered list of candidate preferences.
 * An iterator is used to return the candidates as required
 * during the count
 *
 * Ballots are used in one of two ways: (random or fractional)
 * If random the ballots value is always equal to 1.
 * If fractional, its value starts at a value of 1000
 * and this value is reduced proportionally whenever
 * the ballot ends up in a surplus. The ballot can continue
 * to be used until such time as its value becomes zero.
 */

public class Ballot {
    private List<CandidatePreference> preferences;
    private Iterator<CandidatePreference> i;
    private int mixedNumber;
    private int nextpref = 1; // next preference to be counted

    /* used for fractional counting */
    private int value;
    private boolean fractional;
    static int frac_multiplier = 1000;

    /* set to true if we've checked the whole ballot */
    private boolean fullyRead = false; 

    /* true if there are some hidden preferences in this ballot */
    private boolean hasHidden;
    private int numHidden;

    /* the last preference examined on this ballot */
    private CandidatePreference last=null; 

    public static int nonTransferableBallots = 0;

    public Ballot (
	int n, List<CandidatePreference> prefs, 
	boolean hasHidden, int nHidden, boolean fractional
    ) 
    {
	preferences = prefs;
	mixedNumber = n;
	i = prefs.iterator();
	this.hasHidden = hasHidden;
	this.numHidden = nHidden;
	if (fractional) {
    	    value = frac_multiplier;
	    this.fractional = true;
	} else {
    	    value = 1;
    	    this.fractional = false;
	}
    }

    public int getValue () {
	return value;
    }

    public boolean fractional () {
	return fractional;
    }

    /* reduce the votes value by the specified amount
     * return any residual amount which could not be deducted
     */
    public int reduceValue (int amount) {
	if (amount <= value) {
	    value -= amount;
	    return 0;
	} else {
	    amount -= value; 
	    value = 0;
	    return amount;
	}
    }

    Candidate getNextPreference () {
	CandidatePreference pref;
	while (i.hasNext()) {
	    pref = i.next();
	    last = pref;
	    if (pref.n != nextpref) {
		Display.error ("ballot error on # " + 
			mixedNumber + " ("+nextpref+":"+pref.n+")",null);
	    }
	    nextpref ++;
	    if (pref.c.status() == Status.INRACE) {
		return pref.c;
	    }
	}
	fullyRead = true;
	if (hasHidden) {
	    Display.error ("needed ballot data hidden on ballot # " + mixedNumber, null);
	}
	nonTransferableBallots ++;
	return null;
    }

    String getModifiedPrefsList (int n) {
	int[] strs = new int [n]; // indexed by candidate, contains pref#
	for (CandidatePreference pref : preferences) {
	    strs [pref.c.index()] = pref.n;
	}
	int lastpref = last.n;
		
	String buf = "";
	for (int i=0; i<n; i++) {
	    String val=null;
	    if (strs[i] == 0 && fullyRead) {
		/* we had to examine the whole ballot. This candidate did not get a preference
		 * therefore we have to output the blank entry. ie. we
		 * have to prove that the vote had no more preferences
		 * which could be counted
		 */
		val = "";
	    } else if ((strs[i] == 0) || (strs[i] > lastpref)) {
		/* this preference is lower than the last expressed
		 * or else we didnt look at all preferences and
 		 * this candidate did not get a preference
		 * so it can be hidden */
		val = "*";
	    } else {
	        val = Integer.toString(strs[i]);
	    }
	    buf = buf + ";\""+val+"\"";
	}
	return buf;
    }
	    
    int nprefs () {
	return preferences.size();
    }

    int nmodprefs () {
	return last.n;
    }

    int numHidden () {
	return numHidden;
    }

    int mixedNumber () {
	return mixedNumber;
    }

    public String toString() {
	StringBuffer b = new StringBuffer();
	b.append ("[Ballot:"+mixedNumber+":");
	for (CandidatePreference p : preferences) {
	    b.append (p.c.name()+":");
	}
        b.append ("]");
	return new String (b);
    }
}
