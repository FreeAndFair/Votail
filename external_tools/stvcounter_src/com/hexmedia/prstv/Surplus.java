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

public class Surplus implements Comparable<Surplus> {
    BallotList source; /* source votes for the surplus */
    int ndistrib;	/* the number of votes to redistributed */
    Float t;

    /* used for fractional only */
    static boolean fractional;
    int nreceived;
    int nrequired; /* the number of votes required at last count */

    CandidateBallotMap cbm;

    Surplus (BallotList v, int nreceived, int nrequired) {
	source = v;
	this.nreceived = nreceived;
	this.nrequired = nrequired;
	ndistrib = nreceived - nrequired;
	assert ndistrib >= 0;
	assert ndistrib < v.value();
    }
    
    static void setFractional (boolean f) {
	fractional = f;
    }

    static boolean isFractional () {
	return fractional;
    }

    /* needed for sorting (biggest first)
     */
    public int compareTo (Surplus o) {
	if (ndistrib > o.ndistrib) {
	    return -1;
	} else if (ndistrib < o.ndistrib) {
	    return 1;
	} else {
	    return 0;
	}
    }

    int size () {
	return ndistrib;
    }

    public String toString () {
	return "[Surplus: ndistrib="+ndistrib+"]";
    }

    /* when the surplus is calculated the numbers
     * are put into RandomSurplus instances, and then
     * when distribute() is called, the numbers
     * are taken from here. Not used for fractional surpluses
     */
    private static class RandomSurplus implements Comparable<RandomSurplus> {
	private Float exact;

	public int units;
	public Float remainder;
	public Candidate candidate;

	RandomSurplus (Candidate c, int votes, Float transferFactor) {
	    exact = votes * transferFactor;
	    units = exact.intValue();
	    remainder = exact - units;
	    candidate = c;
	}
	    
        public int compareTo (RandomSurplus o) {
	    if (remainder > o.remainder) {
		return -1;
	    } else if (remainder < o.remainder) {
		return 1;
	    } else {
	        return 0;
	    }
        }
    }

    public void calculate () {
	if (fractional) {
	    calculateFractional();
	} else {
	    calculateRandom();
	}
    }

    static String fmt (int x) {
	return Election.fmt (x);
    }

    public void calculateFractional () {

	assert fractional;
	Display.head2 ("Surplus calculation");
	Display.log ("The following surplus will be distributed at the next count");
	Display.log ("Surplus size: " + fmt(ndistrib));
    	cbm = CandidateBallotMap.create (source);
	int ntransferable = cbm.totalVotes();
	if (ndistrib > ntransferable) {
	    ndistrib = ntransferable;
	}
	int nballots = source.size();
	int srcval = source.value();
	int reduction = (srcval - ndistrib)/nballots;
	int remainder = (srcval - ndistrib)% nballots;
	if (remainder > 0) {
	    reduction ++;
	}
	assert reduction > 0;
	cbm.reduceFractional (reduction, nballots);
	
	Display.tableStart (false);
    	Display.tableRow (new Object[]{"Number of ballots in last set: ", Integer.toString(nballots)}, "right");
    	Display.tableRow (new Object[]{"Total value of last set: ", fmt(srcval)},"right");
    	Display.tableRow (new Object[]{"Reduction per ballot: ", fmt(reduction)},"right");
    	Display.tableRow (new Object[]{"Total reduction in value: ", fmt(reduction*nballots)},"right");
    	Display.tableRow (new Object[]{"Total value to be transferred: ", fmt(srcval-reduction*nballots)},"right");
	Display.tableRow (new Object[]{"Number of transferable votes in surplus: ",
					fmt(ntransferable)},"right");
	Display.tableEnd();

	Display.head2 ("Surplus distribution");
	Display.tableStart (false);
	Display.tableRow (new String[]{"Name: ","Current votes: ","Will receive: "});
	Set<Candidate> keys = cbm.keySet();
	for (Candidate candidate : keys) {
	    BallotList l = cbm.get (candidate);
	    int size = l.value();
	    Display.tableRow (new Object[] {
		candidate.name(), fmt(candidate.nvotes()), fmt(size)
	    }, "right");
	}
	Display.tableEnd();
    }


    public void calculateRandom () {

	assert !fractional;
	Display.head2 ("Surplus calculation");
	Display.log ("The following surplus will be distributed at the next count");
	Display.tableStart (false);
	Display.tableRow (new Object[] {"Surplus size: ",ndistrib});
    	cbm = CandidateBallotMap.create (source);
	int ntransferable = cbm.totalVotes();
	if (ndistrib > ntransferable) {
	    ndistrib = ntransferable;
	}
	t = new Float ((float)ndistrib / ntransferable);
    	Display.tableRow (new Object[]{"Transfer factor: ",t});
	Display.tableRow (new Object[]{"Number of transferable votes in surplus: ",
					ntransferable});
	Display.tableEnd();

	Set<Candidate> keys = cbm.keySet();
	LinkedList<RandomSurplus> csurpluses = new LinkedList<RandomSurplus>();

	int votes_allocated = 0;
	Display.head2 ("Initial surplus distribution");
	Display.tableStart (false);
	Display.tableRow (new String[]{"Name: ","Current votes: ","Will receive: ","Remainder: "});
	for (Candidate candidate : keys) {
	    BallotList l = cbm.get (candidate);
	    int size = l.value();
	    RandomSurplus csurp = new RandomSurplus (candidate, size, t);
	    votes_allocated += csurp.units;
	    Display.tableRow (new Object[] {
		candidate.name(), candidate.nvotes(), csurp.units, csurp.remainder
	    });
	    csurpluses.add (csurp);
	}
	Display.tableEnd();

	if (votes_allocated < ndistrib) {
	    Display.head2 ("Surplus remainder distribution");
	    /* look at remainders */
	    Collections.sort(csurpluses);
	    Display.tableStart (false);
	    Display.tableRow (new String[]{"Name", "Additional vote"});
	    int i = 0;
	    while (votes_allocated < ndistrib && csurpluses.size() > i) {
		RandomSurplus c = csurpluses.get(i++);
		c.units ++;
	    	votes_allocated ++;
	    	Display.tableRow (new String[] {c.candidate.name(), ": +1"});
	    }
	    Display.tableEnd ();
	}

	for (RandomSurplus c : csurpluses) {
	    Candidate candidate = c.candidate;
	    cbm.reduceRandom (candidate, c.units);
	}
    }

    public CandidateBallotMap surplus () {
	return cbm;
    }
}
