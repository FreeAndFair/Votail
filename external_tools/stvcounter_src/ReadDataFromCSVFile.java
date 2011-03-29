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

import java.io.*;
import java.util.*;

public class ReadDataFromCSVFile {

    BufferedReader reader;
    List<Candidate> candidates = new LinkedList<Candidate>();
    BallotList ballots = new BallotList();

    ReadDataFromCSVFile (String filename, boolean fractional) throws Exception {
	FileReader f = new FileReader (filename);
	reader = new BufferedReader (f);
	readFile(fractional);
    }
	
    public List<Candidate> candidates () {
	return candidates;
    }

    public BallotList ballots () {
	return ballots;
    }

    private void readFile (boolean fractional) throws Exception {
	String line = reader.readLine();
	StringTokenizer tok = new StringTokenizer (line, ";");
	int nelems = tok.countTokens(); /* remember this */
	tok.nextToken(); /* ignore first string */
	Candidate[] cand_arr = new Candidate [nelems-1];
	for (int i=0; i<nelems-1; i++) {
	    /* drop the enclosing "" chars */
	    String s = tok.nextToken();
	    String name = s.substring (1,s.length()-1);
	    Candidate c = new Candidate (name, i);
	    candidates.add (c);
	    cand_arr[i] = c;
	}


	int lineNumber = 1;
	while ((line = reader.readLine()) != null) {
	    Candidate x[] = new Candidate [nelems-1];
	    tok = new StringTokenizer (line, ";");
	    if (tok.countTokens() != nelems) {
		throw new Exception ("Wrong number of tokens at line " + lineNumber, null);
	    }
	    LinkedList<CandidatePreference> prefs = new LinkedList<CandidatePreference>();
	    String s = tok.nextToken();
	    s = s.substring (1,s.length()-1);
	    int number = Integer.parseInt (s);
	    boolean hasHidden = false;
	    int numHidden = 0;

	    for (int i=0; i<nelems-1; i++) {
		Candidate c = cand_arr[i];
		assert c!= null;
	        /* drop the enclosing "" chars */
	        String choice = tok.nextToken();
		if (choice.length() > 2) {
		    choice = choice.substring (1,choice.length()-1);
		    if (choice.equals("*")) {
			hasHidden = true;
			numHidden ++;
		    } else {
		    	int position = Integer.parseInt (choice)-1;
			if (x[position] != null) {
			    int pref = position + 1;
			    throw new Exception ("Preference "+pref+" cast more than once: line: "+lineNumber);
			}
		    	x[position] = c;
		    }
		} else {
		    assert choice.length() == 2;
		}
	    }
	    for (int i=0; i<nelems-1; i++) {
		if (x[i]!=null) {
		    prefs.add (new CandidatePreference (x[i], i+1));
		}
	    }
	    Ballot b = new Ballot (number, prefs, hasHidden, numHidden, fractional);
	    ballots.add (b);
	    lineNumber ++;
	}
    }
}
