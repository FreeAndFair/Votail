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
import java.io.*;
import java.net.URL;
import javax.swing.SwingUtilities;

public class Election {

    BallotList votes;
    int quota;
    int depositThreshold;
    int nseats;
    int seatsToBeFilled;
    String file;

    /* inrace + elected + eliminated = constant (total of all candidates) */
    List<Candidate> inrace;
    List<Candidate> elected;
    List<Candidate> eliminated;

    List<Candidate> candidates; /* doesn't change */
    List<Surplus> surpluses;
    
    Election (int nseats, String file) {
	this.votes = votes;
	this.nseats = nseats;
	this.file = file;
	elected = new LinkedList<Candidate>();
	eliminated = new LinkedList<Candidate>();
	surpluses = new LinkedList<Surplus>();
    }

    void initialize() {
	Display.nextPage();
	Display.log ("Reading candidate and ballot data from <b>" + 
			file + " </b>");
	Display.display();
	ReadDataFromCSVFile r=null;
    	boolean fractional=false;
	String r1=null, r2=null;
	try {
	    Display.waitCursor();
	    fractional = !Display.getRules ().equals (Display.RANDOM);
	    if (!fractional) {
		r1 = "random";
	    } else {
		r1 = "fractional";
	    }
	    if (fractional && Display.getRules().equals(Display.FRACTIONAL_ALL)) {
	    	Candidate.useAllVotesForSurplus = true;
		r2 = "all votes";
	    } else {
		r2 = "last set only";
	    }
	    Surplus.setFractional (fractional);
	    r = new ReadDataFromCSVFile (file, fractional);
	    Display.restoreCursor();
	} catch (Exception e) {
	e.printStackTrace();
	    Display.error (e.toString(), e);
	}
	votes = r.ballots();
	candidates =  r.candidates();
	this.inrace = new ArrayList<Candidate>(candidates);
	Display.log ("Read " + fmt(votes.value()) + " votes");
	String qtype;
	if (droopQuota) {
    	    quota = votes.value() / (nseats+1) + 1; // DROOP
	    qtype = "Droop";
	} else {
    	    quota = votes.value() / (nseats) ; // HARE
	    qtype = "Hare";
	}
	Display.head2 ("Election parameters");
	Display.tableStart (true);
	Display.tableRow (new Object[]{"Total poll:  ", fmt(votes.value())},"right");
	Display.tableRow (new Object[]{"Number of seats:  ", nseats},"right");
	Display.tableRow (new Object[]{"Quota:  ", fmt(quota)},"right");
	Display.tableRow (new Object[]{"Quota Type:  ", qtype}, "right");
	Candidate.setQuota (quota);
	seatsToBeFilled = nseats;
	depositThreshold = quota/4 +1;
	Display.tableRow (new Object[] {"Surplus distribution: " , r1}, "right");
	Display.tableRow (new Object[] {"Distribution set: " , r2}, "right");
	Display.tableEnd();
	Display.log("<p>Click <b>Next Count</b> to run the first count" +
	    " or <b>Run all counts</b> to run all counts together");
	Display.enableNextButton();
	Display.display();
    }

    public static String fmt (int x) {
	if (Surplus.isFractional()) {
	    return String.format ("%d.%03d", x/1000, x%1000);
	} else {
	    return Integer.toString (x);
	}
    }

    void printResults () {
	Display.head1("Election results");
	Display.head2("Candidates elected");
	Display.tableStart (true);
	Display.tableHead(new String[]{"Name:", "Votes:", "Elected in count:"});
	for (Candidate c : elected) {
	    Display.tableRow (new Object[]{c.name(), fmt(c.nvotes()), c.count()}, "right");
	}
	Display.tableEnd ();
	Display.head2("Candidates eliminated");
	Display.tableStart (true);
	Display.tableHead(new String[]{"Name:", "Votes:", "Eliminated in count:"});
	for (Candidate c : eliminated) {
	    Display.tableRow (new Object[]{c.name(), fmt(c.nvotes()), c.count()}, "right");
	}
	Display.tableEnd ();
	Display.head2 ("End of election");
	Display.log ("<p>Output logged to <i>results.html</i>");
	Display.log ("<p>Modified version of input file written to <i>modified.csv</i>");
    }

    void printCandidates (List<Candidate> candidates) {
	Display.tableStart (true);
	Display.tableHead(new String[]{"Name:", "Votes:"});
	for (Candidate c : candidates) {
	    Display.tableRow (new Object[]{c.name(), fmt(c.nvotes())}, "right");
	}
	Display.tableEnd ();
	Display.log("");
    }

    int count=0;

    public int count () {
	return count;
    }

    CandidateBallotMap nextMap=null; /* the next set of votes to be counted */

    /* this is called from Display */
    /* returns true if election finished after this count */

    public boolean runCount () {

    	count ++;

	if (count == 1) {
	    nextMap = CandidateBallotMap.create (votes);
	}

    	Display.head1 ("Result of count " + count );
	Display.tableStart (false);
	Display.tableRow (new Object[]{"Seats remaining: ", seatsToBeFilled}, "right");
	Display.tableRow (new Object[]{"Quota:  ", fmt(quota)}, "right");
	Display.tableRow (new Object[] {"Deposit Threshold: " , fmt(depositThreshold)}, "right");
	Display.tableEnd();
	Display.log("");
    	nextMap.distribute();
    	Display.head2 ("Standing after votes in this count distributed");
	Collections.sort (inrace);
	Collections.reverse (inrace);
    	printCandidates(inrace);

	if (seatsToBeFilled > 0) {

	    /* see if any elected */

	    int electedInThisCount = 0;
	    Iterator<Candidate> i = inrace.iterator();
	    Display.head2 ("Candidates elected in this count");
	    if (i.hasNext()) {
	        Display.tableStart (false);
	        Display.tableHead (new String[]{"Name: ", "Votes: ", "Surplus: "});
	        while (i.hasNext()) {
	            Candidate c = i.next();
	            if (c.status() == Status.ELECTED) {
		        Display.tableRow (new Object[]{c.name(), fmt(c.nvotes()), fmt(c.surplus().size())});
			if (c.surplus().size() > 0) {
		            surpluses.add (c.surplus());
			}
		        c.setCount (count);
		        i.remove ();
		        elected.add (c);
		        seatsToBeFilled --;
		        electedInThisCount++;
	            }
	        }
	        Display.tableEnd();
	    }
	
	    Display.log (electedInThisCount+" candidates were elected in this count.");

	    int totalSurplus = 0;

	    if (surpluses.size() > 0) {
    	        Collections.sort (surpluses);
	        for (Surplus surplus: surpluses) {
	    	    totalSurplus += surplus.size();
	        }
	    }

	    Collections.sort (inrace); /* sort to find lowest candidate */
    
	    Display.log ("");
	    /* check for some possible shortcuts */

    	    /* one more candidate than seats ? */

	    if (seatsToBeFilled+1 == inrace.size() && inrace.size() > 1) {
	        Candidate lowest = inrace.get(0);
	        Candidate next = inrace.get(1);
	        int difference = next.nvotes() - lowest.nvotes();
	        if (totalSurplus < difference) {
	            /* lowest candidate cannot possibly make it */
	            Display.log ("Following candidates elected without reaching quota"
	            	+ " because " + lowest.name() + " cannot be elected.");
	            lowest.eliminate();
		    lowest.setCount (count);
	            inrace.remove (lowest);
		    eliminated.add (lowest);
	            printCandidates (inrace);
		    for (Candidate c: inrace) {
		        elected.add (c);
		        c.setCount (count);
		    }
		    recordCounts (count);
		    writeCSVFile();
		    return true;
	        }
	    }
    
    	    /* same number of candidates as seats ? */
    
	    if (seatsToBeFilled == inrace.size()) {
	        /* just declare remaining candidates elected */
	        Display.log ("Following candidates elected without reaching quota.");
	        printCandidates (inrace);
		for (Candidate c: inrace) {
		    elected.add (c);
		    c.setCount (count);
		}
	    	recordCounts (count);
	    	writeCSVFile();
	        return true;
	    }

	    /* end of short cuts */

	    /* check if we are allowed to return a surplus */
	    boolean useSurplus = false;

	    Display.head2 ("Analysis of Surpluses");
	    Display.log ("Number of surpluses available: " + surpluses.size());
	    Display.log ("Total votes in surpluses: " + fmt(totalSurplus));

	    if (seatsToBeFilled > 0 && surpluses.size() > 0) {
		Candidate highest = inrace.get(inrace.size()-1);
		Display.startBulletList();

		/* Elect a continuing candidate ? */

		if (totalSurplus + highest.nvotes() >= quota) {
	            useSurplus = true;
		    Display.listItem (highest.name() + " is highest, and could reach the quota.");
		} else {
		    Display.listItem (highest.name() + " is highest, but cannot be elected with "+
				 "\r\n    the available surpluses yet.");
	        
		    /* Save lowest candidate from exclusion */

		    Candidate lowest = inrace.get(0);
		    Candidate nextLowest = inrace.get(1);

		    if (lowest.nvotes() + totalSurplus >= nextLowest.nvotes()) {
			Display.listItem (lowest.name()+" is lowest, and could possibly be saved "+
					"\r\n    from elimination, with the available surpluses.");
	                useSurplus = true;
		    } else {
			Display.listItem (lowest.name()+" is lowest, but cannot be saved "+
					"\r\n    from elimination, with the available surpluses.");

			/* save lowest candidates deposit ? */
			
			if ((lowest.nvotes() < depositThreshold) && 
			    (lowest.nvotes() + totalSurplus) >= depositThreshold) {
			    Display.listItem (lowest.name()+" is lowest, and the available " +
				"surpluses might save his deposit.");
	                    useSurplus = true;
			} 
		    }	
		}
		Display.endBulletList();
		if (useSurplus) {
		    Surplus s = surpluses.remove(0);
		    s.calculate();
		    nextMap = s.surplus();
		} else {
		    Display.log ("Surplus(es) are available but cannot be used at this time.");
		}
	    } 

	    if (seatsToBeFilled > 0 && !useSurplus) {
	        Display.head2 ("One or more candidates must be eliminated");

	        /* one or more candidates have to be eliminated */
	    
		Display.tableStart (false);
		Display.tableHead (new String[]{"Name: ", "Votes: "});
	        LinkedList<BallotList> eliminations = new LinkedList<BallotList>();
	        int numElimVotes = 0;
		Candidate lowest = inrace.get(0);
		int l_votes = lowest.nvotes();
		Candidate next = inrace.get(1);
		int n_votes = next.nvotes();
		int nElim = 0; /* must always eliminated at least one */
	        while (nElim == 0 || numElimVotes + l_votes < n_votes || n_votes == 0) {
		     /* lowest cannot catch up */
		    if ((numElimVotes > 0) && 
			(l_votes+numElimVotes >= depositThreshold ) &&
			(nElim > 0)) {
			/* could reach deposit threshold */
			break;
		    }
	            lowest.eliminate();
		    nElim ++;
		    lowest.setCount (count);
	            BallotList b = lowest.votes();
	            Display.tableRow (new Object[]{lowest.name(), fmt(b.value())});
	            eliminated.add (lowest);
	            inrace.remove (lowest);
	            eliminations.add (b);
	            numElimVotes += b.value();
	            if (inrace.size()< 2) {
		        break;
	            }
		    lowest = next;
		    l_votes = n_votes;
		    next = inrace.get(1);
		    n_votes = next.nvotes();
	        }
		Display.tableEnd();
		Display.head2 ("Number of Eliminated votes: "+fmt(numElimVotes));
	        nextMap = new CandidateBallotMap();
	        for (BallotList ballots: eliminations) {
	            for (Ballot ballot : ballots) {
		        Candidate c = ballot.getNextPreference();
		        if (c != null) {
		            nextMap.addBallot (c, ballot);
		        }
	            }
	        }
	    }
        }
	recordCounts (count);
	if (seatsToBeFilled == 0) {
	    writeCSVFile();
	    return true;
	}
	return false;
    }
	
    /* information not used yet */

    void recordCounts (int count) {
	for (Candidate c : inrace) {
	    c.rememberVotesAtCount (count);
	}
    }

    /* write the modified CSV file showing only 
     * the preferences that were used in the count
     */
    void writeCSVFile () {
	double x1 = 0f,x2 = 0f, x3=0f;
	int n4=0, n5=0, n6=0, n7=0, n8=0, n9=0, n10=0;
	try {
	    FileOutputStream f = new FileOutputStream ("modified.csv");
	    PrintWriter w = new PrintWriter (f);
	    w.print ("\"Mixed Vote No.\"");
	    int nc = 0;
	    for (Candidate c : candidates) {
	        w.print (";\""+c.name()+"\"");
	        nc ++;
	    }
	    w.println ("");
	    int count = 1;
	    int ncand = candidates.size();
	    int hcount = 0;
	    for (Ballot b : votes) {
	        w.println ("\""+count+"\""+b.getModifiedPrefsList(ncand));
		int nprefs = b.nprefs();
		x1 += nprefs;
		if (nprefs >=4) n4++;
		if (nprefs >=5) n5++;
		if (nprefs >=6) n6++;
		if (nprefs >=7) n7++;
		if (nprefs >=8) n8++;
		if (nprefs >=9) n9++;
		if (nprefs >=10) n10++;
		x3 += b.numHidden();
		if (b.numHidden() > 0) {
		    hcount ++;
		}
		count ++;
	    }
	    w.close();
	    Display.log ("Finished writing modified.csv");
	    Display.head2 ("Preference analysis");
	    Display.tableStart (false);
	    Display.tableRow (new Object[]{"Total number of ballots:" ,votes.size()}, "right");
	    Display.tableRow (new Object[]{"Total number of preferences possible:", 
				votes.size()*ncand}, "right");
	    Display.tableRow (new Object[]{"Total number of preferences expressed:", (int)x1}, 
							"right");
	    x1 = x1/votes.size();
	    Display.tableRow (new Object[]{"Mean number of preferences expressed:", x1}, 
						"right");
	    Display.tableRow (new Object[]{"Number of ballots with hidden preferences:",hcount}, 
						"right");
	    Display.tableRow (new Object[]{"Total number of hidden preferences:",(int)x3}, 
						"right");
	    Display.tableRow (new Object[]{"Number of ballots with 4 or more preferences:",n4},
						"right");
	    Display.tableRow (new Object[]{"Number of ballots with 5 or more preferences:",n5},
						"right");
	    Display.tableRow (new Object[]{"Number of ballots with 6 or more preferences:",n6},
						"right");
	    Display.tableRow (new Object[]{"Number of ballots with 7 or more preferences:",n7},
						"right");
	    Display.tableRow (new Object[]{"Number of ballots with 8 or more preferences:",n8},
						"right");
	    Display.tableRow (new Object[]{"Number of ballots with 9 or more preferences:",n9},
						"right");
	    Display.tableRow (new Object[]{"Number of ballots with 10 or more preferences:",n10},
						"right");
	    x3 = x3/(ncand * votes.size()) * 100;
	    int x3i = (int) x3;
	    Display.tableRow (new Object[]{"Proportion of preferences which were hidden:" ,
					new String(x3i + "%")}, "right");
	    Display.tableEnd();
	} catch (IOException e) {
	    Display.error ("Error writing modified.csv", e);
	}
    }
	
    static boolean droopQuota = true; // by default - otherwise Hare

    public static void main (final String[] args) throws Exception {
	Display.create();
	Display.warn (new String[] {"<html>Please note! This is a work-in-progress.","Most, but not all, "+
		"count rules have been implemented.","No warranty of fitness for any purpose is given",
		"with this software. You use it entirely at your own risk.",
		"There are probably many bugs. If you find any, please report them to :-",
		"michael@hexmedia.com. Have fun!"});
	String filename=null, seats=null;
	if (args.length == 0) {
	    InitParams ip = new InitParams (null);
	    seats = ip.seats();
	    filename = ip.filename();
	} else if (args.length == 2) {
	    seats = args[1];
	    filename = args[0];
	} else if (args.length == 3) {
	    seats = args[2];
	    filename = args[1];
	    droopQuota = Boolean.parseBoolean(args[0]);
	} else {
	    usage();
	}
	try {
	    final int nseats = Integer.parseInt (seats);
	    Display.tableStart (false);
	    Display.tableRow (new Object[]{"Will read vote data from: ", filename});
	    Display.tableRow (new Object[]{"Number of seats in race: " , seats});
	    Display.tableEnd();
	    Display.head2 ("Instructions");
	    Display.tableStart (false);
	    Display.tableRow (new Object[] {"<img src="+res("1.gif")+">",
					    "Select the appropriate <b>surplus distribution</b> rule"});
	    Display.tableRow (new Object[] {"<img src="+res("2.gif")+">",
					    "Click <b>Initialize</b> to read in the count data"});
	    Display.tableRow (new Object[] {"<img src="+res("3.gif")+">",
					    "Click <b>Next count</b> to run each count one by one or <b>Run all counts</b> "+
					    "to run all counts at once"});
	    Display.tableEnd();
	    Display.log ("<p>All data displayed in this window will also be written to <i>results.html</i>");
	    Display.log ("<p>A modified version of the input file will be written to <i>modified.csv</>");
	    Election election = new Election (nseats, filename);
	    Display.setElection (election);
	    Display.display();
	} catch (NumberFormatException e) {
	    Display.error ("Bad data entered in number of seats field", e);
	}

    }

    static String res (String arg) throws Exception {
	ClassLoader loader = Thread.currentThread().getContextClassLoader();
	URL u = loader.getResource (arg);
	return u.toString();
    }

    static void usage () {
	System.out.println ("");
	System.out.println ("Incorrect parameters to program:");
	System.out.println ("");
	System.out.println ("usage: java -jar election.jar [true|false] votes.csv N");
	System.out.println ("");
	System.out.println ("where votes.csv is a csv text file containing the ballots");
	System.out.println ("and N is the number of seats in the election");
	System.out.println ("optional true/false arg refers to usage of droop quota: true=Droop (default) false=Hare");
	System.exit (0);
    }
}
