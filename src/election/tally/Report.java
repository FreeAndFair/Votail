package election.tally;


/*
 * Copyright (c) 2005-2009 Dermot Cochran
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

/**
 * Latest election results for each constituency.
 *
 * @author Dermot Cochran
 */

/* <BON>
 * class_chart ELECTION_RESULT
 * indexing
 *   author: "Dermot Cochran";
 *   copyright: "2005-2009, Dermot Cochran";
 *   license: "MIT";
 *   modified: "2009-01-21-dc";
 * explanation
 *   "Information and statistics about the current results of the election."
 * query
 *   "How many candidates were elected?",
 *   "How many rounds of counting were performed?",
 *   "Which candidates were elected?",
 *   "In which round of counting was each candidate elected?",
 *   "Is this count now completed?",
 *   "Was the count successful?",
 *   "How many votes did each candidate receive in each round?"
 * constraint
 *   "The number of candidates elected is not less than zero",
 *   "The number of candidates elected is not more than the number of seats",
 *   "The total number of rounds of counting is not less than zero",
 *   "The list of elected candidates contains a valid internal identifier for each candidate",
 *   "The same internal identifier does not appear twice in the list of elected candidates",
 *   "The number of candidates elected at the end of each round is not less than the number of\
 *   \ candidates elected at the end of the previous round"
 *   "Not enough information is revealed to identify any voter"
 *   "Enough information is revealed in order to allow software independent verification of the\
 *   \ count results"
 *   "The results are immutable, once recorded and cannot be tampered with or otherwise modified\
 *   \ after the count is complete"
 * end
 * </BON>
 */

public class Report {
	
	/**
	 * Maximum number of seats in any constituency
	 */
	final static int MAX_SEATS = 5;
	
//@ public invariant 0 <= numberElected;
//@ public invariant numberElected <= MAX_SEATS;
	private /*@ spec_public @*/ int numberElected;

/*@ public invariant (\forall int i;
  @   0 < i && i < numberElected;
  @   0 < electedCandidateIDs[i] &&
  @   electedCandidateIDs[i] != Ballot.NONTRANSFERABLE);
  @ public invariant (\forall int i, j;
  @   0 <= i && i < numberElected &&
  @   0 <= j && j < numberElected && 
  @   i != j;
  @   electedCandidateIDs[i] != electedCandidateIDs[j]); 
  @*/
	private /*@ non_null spec_public @*/ int[] electedCandidateIDs;
	
/**
	 * @return the numberElected
	 */
	public /*@ pure @*/ int getNumberElected() {
		return numberElected;
	}

	/**
	 * Is this the internal identifier of an elected candidate?
	 * 
	 * @param id The internal identifier
	 * 
	 * @return <code>true</code> if this is the ID of an elected candidate
	 */
	public /*@ pure @*/ boolean isElectedCandidateID (int id) {
		for (int i=0; i < electedCandidateIDs.length; i++) {
			if (id == electedCandidateIDs[i]) {
				return true;
			}
		}
		return false;
	}

	/** Total number of rounds of counting */
	//@ public invariant 0 <= totalNumberOfCounts;
	private /*@ spec_public @*/ int totalNumberOfCounts;

	/** Internal identifiers for each candidate */
	private /*@ spec_public @*/ int[] candidateIDs;

	/** Number of votes for each candidate in each round of counting */
	private /*@ spec_public @*/ long[][] candidateVotes;

	//@ public invariant 0 <= numberOfCandidates;
	private /*@ spec_public @*/ int numberOfCandidates;
	
	/**
	 * Store the election results for this constituency.
	 * 
	 * @param list The list of internal identifiers for the winner candidates
	 * @param counts The number of rounds of counting 
	 * @param candidates The list of candidates
	 */
	/*@ requires list.length <= MAX_SEATS;
	  @ requires 0 <= counts;
	  @ requires candidates != null;
	  @ requires \nonnullelements (candidates);
	  @ assignable candidateIDs;
	  @ assignable candidateVotes;
	  @ assignable numberElected;
	  @ assignable electedCandidateIDs;
	  @ assignable totalNumberOfCounts;
	  @*/
	public Report(/*@ non_null @*/ final int[] list, final int counts, final Candidate[] candidates){
		numberElected = list.length;
		electedCandidateIDs = new int [list.length];
		for (int i=0; i < list.length; i++) {
			electedCandidateIDs[i] = list[i];
		}
		totalNumberOfCounts = counts;
		numberOfCandidates = candidates.length;
		candidateIDs = new int [candidates.length];
		candidateVotes = new long [candidates.length][counts];
		for (int c=0; c<candidates.length; c++) {
			candidateIDs[c] = candidates[c].getCandidateID();
			for (int n=0; n < counts; n++) {
				candidateVotes[c][n] = candidates[c].getVoteAtCount(n);
			}
		}
		}

	/**
	 * How many rounds of counting?
	 * 
	 * @return The number of rounds of counting
	 */
	public /*@ pure @*/ int getTotalNumberOfCounts() {
		return totalNumberOfCounts;
	}

	/**
	 * Get the total vote for each candidate at each round of counting.
	 * 
	 * @param id The ID number of the candidate
	 * @param round The round of counting
	 * 
	 * @return The total vote for this candidate at that round of counting.
	 */
	//@ requires 0 <= round && round < totalNumberOfCounts;
	//@ requires candidateIDs != null;
	//@ requires candidateVotes != null;
	//@ requires numberOfCandidates <= candidateIDs.length;
	//@ requires numberOfCandidates <= candidateVotes.length;
	//@ requires (\forall int c; 0 <= c && c < numberOfCandidates; round < candidateVotes[c].length);
	//@ requires (\exists int i; 0 <= i && i < numberOfCandidates; candidateIDs[i] == id);
	public /*@ pure @*/ long getResult(final int id, final int round) {
	
		long result = 0;
		for (int c = 0; c < numberOfCandidates; c++) {
			if (candidateIDs[c] == id) {
				result = candidateVotes[c][round];
				break;
			}	
		}
		return result;
	}
}
