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
 * Data transfer structure for candidate ID details and number of seats.
 * 
 * @author <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 * Dermot Cochran</a>
 */

public class Election {

/** Number of candidates for election in this constituency */
//@ public invariant 0 <= numberOfCandidates;
	public transient int numberOfCandidates;
	
/** Number of seats to be filled in this election */
//@ public invariant 0 <= numberOfSeatsInThisElection;
//@ public invariant numberOfSeatsInThisElection <= totalNumberOfSeats;
	public transient int numberOfSeatsInThisElection;
	
/** Number of seats in this constituency */
//@ public invariant 0 <= totalNumberOfSeats;
	public transient int totalNumberOfSeats;
	
/** List of all candidates in this election */
/*@ public invariant (\forall int i;
  @   0 <= i && i < numberOfCandidates;
  @   0 < candidateList[i].getCandidateID() &&
  @   candidateList[i].getCandidateID() != Ballot.NONTRANSFERABLE); 
  @*/
/** @constraint No duplicate candidates are allowed. */
/*@ public invariant (\forall int i, j;
  @   0 <= i && i < numberOfCandidates &&
  @   0 <= j && j < numberOfCandidates &&
  @   i != j;
  @   !candidateList[i].equals(candidateList[j])); 
  @*/	
	private transient /*@ spec_public non_null @*/ Candidate[] candidateList;
	
	/**
	 * 
	 */
	public Election(){	
		totalNumberOfSeats = 0;
		numberOfCandidates = 0;
		numberOfSeatsInThisElection = 0;
		candidateList = new Candidate[numberOfCandidates];
	} //@ nowarn;

	/**
	 * Set the list of candidates.
	 * <p>
	 * <strong>Constraints:</strong>
	 * <ul>
	 * <li> This method may only be called once i.e. the initial list of candidates cannot be altered.</li>
	 * <li> No candidate may appear more than once on the list.</li>
	 * </ul>
	 * <p>
	 * 
	 * @param listOfCandidates The list of candidates for this election.
	 */
	/*@ public normal_behavior 
	  @   requires numberOfCandidates == 0;
	  @   requires (\forall int i;
	  @     0 <= i && i < listOfCandidates.length;
	  @     listOfCandidates[i] != null &&
	  @     0 < listOfCandidates[i].getCandidateID() &&
	  @     listOfCandidates[i].getCandidateID() != Ballot.NONTRANSFERABLE); 
 	  @   requires (\forall int i, j;
	  @     0 <= i && i < listOfCandidates.length &&
	  @     0 <= j && j < listOfCandidates.length &&
	  @     i != j;
	  @     (false == listOfCandidates[i].equals(listOfCandidates[j]))); 
	  @  assignable candidateList, numberOfCandidates;
	  @  ensures (\forall int i;
	  @     0 <= i && i < listOfCandidates.length;
 	  @     candidateList[i].equals(listOfCandidates[i]));
 	  @  ensures listOfCandidates.length == numberOfCandidates;
	  @*/	
	public void setCandidateList(final /*@ non_null @*/ Candidate[] listOfCandidates) {
		numberOfCandidates = listOfCandidates.length;
		candidateList = new Candidate[numberOfCandidates];
		for (int i = 0; i < numberOfCandidates; i++) {
		  this.candidateList[i] = listOfCandidates[i];
		}
	}

	/**
	 * Get the <code>Candidate</code> object.
	 * 
	 * @return The candidate at that position on the initial list
	 */
	//@ requires candidateList != null;
	//@ requires \nonnullelements (candidateList);
	//@ requires 0 <= index && index < candidateList.length;
	public /*@ pure non_null @*/ Candidate getCandidate(final int index) {
		return candidateList[index];
	}
	}
