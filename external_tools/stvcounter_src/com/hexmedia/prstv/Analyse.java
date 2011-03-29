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

public class Analyse {

    ReadDataFromCSVFile srcFile, modFile;
    BallotList srcList, modList;
    HashMap<Integer,Ballot> srcMap, modMap;

    LinkedList<Integer> c4, c5, c6, c7, c8, c9, c10, c11, c12;
    int srcHidden=0, modHidden=0;
    int ncandidates, nballots;

    /* takes a map from the original list and retrieves
     * the same ballots from the modified list. It then
     * calculates the mean number of preferences in this new list
     */
    void checkModifiedMap (LinkedList<Integer> l, int n) {
	double count = 0;
	int max = 0;
	for (int x : l) {
	    Ballot b = modMap.get(x);
	    int nprefs = b.nprefs();
	    if (nprefs > max) {
		max = nprefs;
	    }
	    count += nprefs;
	}
	double avg = count / l.size();
	System.out.println ("Mean # of prefs for set with "+
	    n + " originally is: " + avg);
    }

    public void analyse (String f1, String f2) throws Exception {
	System.out.println ("Reading source file: " + f1);
	srcFile = new ReadDataFromCSVFile (f1, false);
	ncandidates = srcFile.candidates().size();
	System.out.println ("Reading modified file: " + f2);
	modFile = new ReadDataFromCSVFile (f2, false);
	if (modFile.candidates().size() != ncandidates) {
	    System.out.println ("*** wrong number of candidates: ");
	    System.exit (1);
	}
	srcList = srcFile.ballots();
	nballots = srcList.size();
	modList = modFile.ballots();
	if (nballots != modList.size()) {
	    System.out.println ("*** wrong number of ballots: ");
	    System.exit (1);
	}
	System.out.println ("Number of candidates: "+ncandidates);
	System.out.println ("Number of ballots: "+nballots);
	int maxprefs = ncandidates * nballots;
	System.out.println ("Theoretical max number of preferences: "+maxprefs);
	srcMap = new HashMap<Integer,Ballot>();
	modMap = new HashMap<Integer,Ballot>();
	c9 = new LinkedList<Integer>();
	c10 = new LinkedList<Integer>();
	c11 = new LinkedList<Integer>();
	c12 = new LinkedList<Integer>();
	c4 = new LinkedList<Integer>();
	c5 = new LinkedList<Integer>();
	c6 = new LinkedList<Integer>();
	c7 = new LinkedList<Integer>();
	c8 = new LinkedList<Integer>();

	double nprefs = 0;

	for (Ballot b : modList) {
	    int number = b.mixedNumber();
	    modMap.put (number, b);
	    int prefs = b.nprefs();
	    nprefs += b.nprefs();
	    modHidden += b.numHidden();
	    if (prefs >= 4) {
		c4.add (number);
	    }
	    if (prefs >= 5) {
		c5.add (number);
	    }
	    if (prefs >= 6) {
		c6.add (number);
	    }
	    if (prefs >= 7) {
		c7.add (number);
	    }
	    if (prefs >= 8) {
		c8.add (number);
	    }
	    if (prefs >= 9) {
		c9.add (number);
	    }
	    if (prefs >= 10) {
		c10.add (number);
	    }
	    if (prefs >= 11) {
		c11.add (number);
	    }
	    if (prefs >= 12) {
		c12.add (number);
	    }
	}
	System.out.println ("# modified ballots with 4 or more preferences: " + c4.size());
	System.out.println ("# modified ballots with 5 or more preferences: " + c5.size());
	System.out.println ("# modified ballots with 6 or more preferences: " + c6.size());
	System.out.println ("# modified ballots with 7 or more preferences: " + c7.size());
	System.out.println ("# modified ballots with 8 or more preferences: " + c8.size());
	System.out.println ("# modified ballots with 9 or more preferences: " + c9.size());
	System.out.println ("# modified ballots with 10 or more preferences: " + c10.size());
	System.out.println ("# modified ballots with 11 or more preferences: " + c11.size());
	System.out.println ("# modified ballots with 12 or more preferences: " + c12.size());
	System.out.println ("# modified preferences hidden: " + modHidden);
	System.out.println ("fraction of modified preferences hidden: " + (float)modHidden/(float)maxprefs);

	double modMean = nprefs/modList.value();
	System.out.println ("Mean number of preferences in modified file: " + modMean);
	double total = 0f;

	for (Ballot b : modList) {
	    double deviation = (b.nprefs() - modMean) * (b.nprefs() - modMean);
	    total += deviation;
	}
	double sd = Math.sqrt (total/modList.value());
	System.out.println ("Standard deviation of preferences in modified file: " + sd);

	nprefs = 0;

	c9 = new LinkedList<Integer>();
	c10 = new LinkedList<Integer>();
	c11 = new LinkedList<Integer>();
	c12 = new LinkedList<Integer>();
	c4 = new LinkedList<Integer>();
	c5 = new LinkedList<Integer>();
	c6 = new LinkedList<Integer>();
	c7 = new LinkedList<Integer>();
	c8 = new LinkedList<Integer>();
	
	for (Ballot b : srcList) {
	    int number = b.mixedNumber();
	    nprefs += b.nprefs();
	    srcMap.put (number, b);
	    int prefs = b.nprefs();
	    srcHidden += b.numHidden();
	    if (prefs >= 4) {
		c4.add (number);
	    }
	    if (prefs >= 5) {
		c5.add (number);
	    }
	    if (prefs >= 6) {
		c6.add (number);
	    }
	    if (prefs >= 7) {
		c7.add (number);
	    }
	    if (prefs >= 8) {
		c8.add (number);
	    }
	    if (prefs >= 9) {
		c9.add (number);
	    }
	    if (prefs >= 10) {
		c10.add (number);
	    }
	    if (prefs >= 11) {
		c11.add (number);
	    }
	    if (prefs >= 12) {
		c12.add (number);
	    }
	}
	double srcMean = nprefs/srcList.value();
	System.out.println ("Mean number of preferences in source file: " + srcMean);
	total = 0f;
	for (Ballot b : srcList) {
	    double deviation = (b.nprefs() - srcMean) * (b.nprefs() - srcMean);
	    total += deviation;
	}
	sd = Math.sqrt (total/srcList.value());
	System.out.println ("Standard deviation of preferences in source file: " + sd);
	System.out.println ("# original ballots with 4 or more preferences: " + c4.size());
	System.out.println ("# original ballots with 5 or more preferences: " + c5.size());
	System.out.println ("# original ballots with 6 or more preferences: " + c6.size());
	System.out.println ("# original ballots with 7 or more preferences: " + c7.size());
	System.out.println ("# original ballots with 8 or more preferences: " + c8.size());
	System.out.println ("# original ballots with 9 or more preferences: " + c9.size());
	System.out.println ("# original ballots with 10 or more preferences: " + c10.size());
	System.out.println ("# original ballots with 11 or more preferences: " + c11.size());
	System.out.println ("# original ballots with 12 or more preferences: " + c12.size());
	System.out.println ("# original preferences hidden: " + srcHidden);
	System.out.println ("fraction of original preferences hidden: " + (float)srcHidden/(float)maxprefs);

	checkModifiedMap (c4, 4);
	checkModifiedMap (c5, 5);
	checkModifiedMap (c6, 6);
	checkModifiedMap (c7, 7);
	checkModifiedMap (c8, 8);
	checkModifiedMap (c9, 9);
	checkModifiedMap (c10, 10);
	checkModifiedMap (c11, 11);
	checkModifiedMap (c12, 12);
	    
    }
	
    public static void main (String[] args) throws Exception {
	if (args.length != 2) {
	    System.out.println ("usage: java Analyse file1 file2");
	    return;
	}
	Analyse an = new Analyse ();
	an.analyse (args[0], args[1]);
    }
}
