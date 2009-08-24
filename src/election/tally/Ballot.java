/**
 * Votail - PR-STV ballot counting for Irish elections
 * 
 * Copyright (c) 2005-2007 Dermot Cochran, Joseph R. Kiniry and Patrick E. Tierney
 * Copyright (c) 2008-2009 Dermot Cochran, Lero Graduate School of Software Engineering
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

package election.tally;

//@ refine "Ballot.java-refined";

/* <BON>
 * class_chart BALLOT
 * indexing
 *   author: "Dermot Cochran"
 * explanation
 *   "An electronic representation of a valid ballot paper"
 * query
 *   "To which continuing candidate is this ballot allocated?",
 *   "In which round of counting was this ballot last transfered?",
 *   "Who is the first preference candidate on this ballot?",
 *   "Is this ballot deeper in the pile than another ballot?",
 *   "What is the internal identifier (sequence number) for this ballot?"
 * command
 *   "Load this ballot from the database"
 * constraint
 *   "Every valid ballot has a valid first preference"
 * </BON>
 */

/**
 * The ordered set of preferences from a ballot paper in an Irish election,
 * which uses the Proportional Representation Single Transfer Vote.
 * (PRSTV) system.
 * 
 * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_2.pdf">
   Department of Environment and Local Government, 
   Count Requirements and Commentary on Count Rules,
   section 3-14</a>
 * 
 * @author <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">Dermot Cochran</a>
 * @copyright 2005-2009
 */


public class Ballot {
  /**
   * Maximum possible number of ballots based on maximum population size for
   * a five seat constituency i.e. at most 30,000 people per elected representative.
   * 
   * @see "Constitution of Ireland, Article 16, Section 2"
   */
  public static final int MAX_BALLOTS = 150000;

/**
 * Candidate ID value to use for non-transferable ballot papers
 * 
 * @design A special candidate ID value is used to indicate
 * non-transferable votes i.e., when the list of preferences has
 * been exhausted and none of the continuing candidates are in the preference list, 
 * the ballot is deemed to be non-transferable.
 * 
 * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_2.pdf">
 * Department Of Environment and Local Government,
 * Count requirements and Commentary an Count Rules,
 * section 7, pages 23-27</a>
 */
public static final int NONTRANSFERABLE = 0;

private static final int MAX_PREFERENCES = Candidate.MAX_CANDIDATES;

/** Ballot ID number */
  //@ public invariant (ballotID == 0) || (0 < ballotID);
  protected /*@ spec_public @*/ int ballotID;
	 
  /** Preference list of candidate IDs */	
  protected /*@ spec_public */ int[] preferenceList 
       = new int [MAX_PREFERENCES];

  /** Total number of valid preferences on this ballot paper */
  protected /*@ spec_public @*/ int numberOfPreferences;
  
  /** Position within preference list */
  //@ public initially positionInList == 0;
  //@ public invariant 0 <= positionInList;
  //@ public invariant positionInList <= numberOfPreferences;
  //@ public constraint \old(positionInList) <= positionInList;
  protected /*@ spec_public @*/ int positionInList;
   
  /** Candidate ID to which the vote is assigned at the end of each count */
  protected /*@ spec_public @*/ int[] candidateIDAtCount = 
    new int [Candidate.MAX_CANDIDATES];

  /** Last count number in which this ballot was transferred */
  //@ public invariant 0 <= countNumberAtLastTransfer;
  //@ public invariant countNumberAtLastTransfer <= CountConfiguration.MAXCOUNT;
  //@ public initially countNumberAtLastTransfer == 0;  
  protected /*@ spec_public @*/ int countNumberAtLastTransfer;
    
  /** Random number used for proportional distribution of surplus votes */
  //@ public constraint randomNumber == \old (randomNumber);
  //@ public ghost int _randomNumber;

  protected /*@ spec_public @*/ int randomNumber;

  /**
   * Next available value for ballot ID number.
   */
  /*@ private invariant 0 < nextBallotID;
    @ private constraint \old(nextBallotID) <= nextBallotID;
    @*/
  protected /*@ spec_public @*/ static int nextBallotID = 1;


  /**
   * Generate an empty ballot paper for use by a voter.
   */
/*@ also public normal_behavior
  @	  assignable _randomNumber, numberOfPreferences, countNumberAtLastTransfer,
  @     ballotID, positionInList, randomNumber, nextBallotID, preferenceList;
  @   ensures numberOfPreferences == 0;
  @   ensures countNumberAtLastTransfer == 0;
  @   ensures positionInList == 0;
  @*/
  public Ballot () {
 	  numberOfPreferences = 0;
	  countNumberAtLastTransfer = 0;
	  positionInList = 0;
	  ballotID = nextBallotID++;
      randomNumber = this.hashCode();
	  //@ set _randomNumber = randomNumber;
  }
    
  /**
   * Copy the <em>contents</em> of a ballot.
   * @param ballot Ballot to be copied.
   */
  public Ballot(final Ballot ballot) {
	  numberOfPreferences = ballot.numberOfPreferences;
	  for (int p = 0; p < numberOfPreferences; p++) {
		preferenceList[p] = ballot.getPreference(p);
	  }
	  countNumberAtLastTransfer = 0;
	  positionInList = 0;
	  ballotID = nextBallotID++;
      randomNumber = this.hashCode();
	  //@ set _randomNumber = randomNumber;
	
}

/**
   * Load the ballot details.
   * 
   * @param list List of candidate IDs in order from first preference
   * 
   * @design There should be at least one preference in the list. Empty or spoilt
   *         votes should neither be loaded nor counted. There should be no
   *         duplicate preferences in the list and none of the candidate ID values
   *         should match the special value for non transferable votes.
   *         <p>
   *         There should be no duplicates in the preference list; but there is no
   *         need to make this a precondition because duplicates will be ignored
   *         and skipped over.
   *         
   * @constraint The ballot may only be loaded once; it cannot be overwritten.
   */    
  /*@ also public normal_behavior
    @   requires (\forall int i; 0 <= i && i < list.length;
    @     (list[i]) != NONTRANSFERABLE);
    @   requires (\forall int i; 0 <= i && i < list.length;
    @     0 < list[i]);
    @   requires positionInList == 0;
    @	assignable numberOfPreferences, ballotID, preferenceList, nextBallotID, positionInList, candidateIDAtCount[*];
    @   ensures numberOfPreferences == list.length;
    @   ensures (\forall int i; 0 <= i && i < list.length;
    @     (preferenceList[i] == list[i]));
    @*/
   public void load(final /*@ non_null @*/ int[] list) {

    for(int i = 0; i < list.length; i++) {
 		    preferenceList[i] = list[i];
 	}
    
    numberOfPreferences = list.length;
    candidateIDAtCount [countNumberAtLastTransfer] = list[0];
  }

  /**
   * Get candidate ID to which the ballot is assigned 
   * 
   * @return The candidate ID to which the ballot is assigned
   */    
  /*@ also public normal_behavior
    @   requires 0 <= positionInList;
    @   requires positionInList <= numberOfPreferences;
    @   ensures (positionInList == numberOfPreferences) ==>
    @     (\result == NONTRANSFERABLE);
    @   ensures (positionInList < numberOfPreferences) ==>
    @     (\result == preferenceList[positionInList]);
    @*/   
  public /*@ pure @*/ int getCandidateID() {
      return getPreference(positionInList);
  }
    
  /**
   * Get next preference candidate ID
   * 
   * @param offset The number of preferences to look ahead
   * 
   * @return The next preference candidate ID
   */    
  /*@ also public normal_behavior
    @ requires 0 <= positionInList;
    @ requires 1 <= offset;
    @ requires positionInList <= numberOfPreferences;
    @ requires preferenceList != null;
    @ ensures (positionInList + offset >= numberOfPreferences) ==>
    @   (\result == NONTRANSFERABLE);
    @ ensures (positionInList + offset < numberOfPreferences) ==>
    @   (\result == preferenceList[positionInList + offset]);
    @*/

  public /*@ pure @*/ int getNextPreference(final int offset){
        if(positionInList + offset < numberOfPreferences){
          return preferenceList[positionInList + offset];
        }
		return NONTRANSFERABLE;
  }
 
  /**
   * Transfer this ballot to the next preference candidate.
   * 
   * @design This method may be called multiple times during the same count
   * until the ballot is non-transferable or a continuing candidate ID is
   * found in the remainder of the preference list.
   * 
   * @param countNumber The count number at which the ballot was transfered.
   */    
  /*@ also public normal_behavior
    @   requires 0 <= positionInList;
    @   requires positionInList <= numberOfPreferences;
    @   requires positionInList < preferenceList.length;
    @   requires countNumberAtLastTransfer <= countNumber;
    @   requires countNumber < candidateIDAtCount.length;
    @   assignable countNumberAtLastTransfer, positionInList, candidateIDAtCount[*];
    @   ensures (countNumberAtLastTransfer == countNumber) || 
    @           (positionInList == numberOfPreferences);
    @   ensures \old(positionInList) <= positionInList;
    @   ensures (positionInList == \old(positionInList) + 1) ||
    @           (positionInList == numberOfPreferences);
    @*/
  public void transfer(final int countNumber) {

		if (positionInList < numberOfPreferences) {
			// Update ballot history
			for (int r = countNumberAtLastTransfer; r <= countNumber; r++) {
				candidateIDAtCount [r] = preferenceList[positionInList];
			}
	 		countNumberAtLastTransfer = countNumber;
 			positionInList++;
		}
	}
    
  /**
   * Get ballot ID number
   * 
   * @return ID number for this ballot
   */    
  /*@ also public normal_behavior
    @ ensures \result == ballotID;
    @*/
  public /*@ pure @*/ int getBallotID(){
    return ballotID;
  }
     
  /**
   * This method checks if this ballot paper is assigned to this candidate.
   * 
   * @design It is valid to use <code>NONTRANSFERABLE</code> as the ID value 
   * to be checked. This ballot paper can only be assigned to one candidate at 
   * a time; there are no fractional transfer of votes in Dail elections.
   * 
   * @param candidateIDToCheck The unique identifier for this candidate
   * 
   * @return <code>true</code> if this ballot paper is assigned to this 
   * candidate ID
   */    
  /*@ also public normal_behavior
    @   ensures (\result == true) <==> (getCandidateID() == candidateIDToCheck);
    @*/
  public /*@ pure @*/ boolean isAssignedTo(final int candidateIDToCheck){
    return (getCandidateID() == candidateIDToCheck);
  }
    
  /**
   * Gets the remaining number of preferences.
   * 
   * @return The number of preferences remaining
   */    
  /*@ also 
    @   public normal_behavior 
    @     requires positionInList <= numberOfPreferences;
    @     ensures \result == numberOfPreferences - positionInList;
    @*/
  public /*@ pure @*/ int remainingPreferences(){
    return (numberOfPreferences - positionInList);
  }

//@ requires 0 <= i;
//@ ensures (i < numberOfPreferences) ==> preferenceList[i] == \result;
//@ ensures (numberOfPreferences <= i) ==> \result == Ballot.NONTRANSFERABLE;
public /*@ pure @*/ int getPreference(int i) {
    if (i < numberOfPreferences) {
       return preferenceList[i];
    }
    return Ballot.NONTRANSFERABLE;	
}

public boolean isFirstPreference(int candidateID) {
	return candidateID == preferenceList[0];
}
 
}