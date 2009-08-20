package election.tally;

import election.tally.exception.NullCandidateException;

/**
 * Ballot counting algorithm for elections to Oireachtas Eireann - the National 
 * Parliament of Ireland.
 * 
 * @author Dermot Cochran
 * @copyright 2005-2009 Dermot Cochran
 * 
 * @license
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
 * 
 * @sponsors
 * This work was supported, in part, by Science Foundation Ireland
 * grant 03/CE2/I303_1 to Lero - the Irish Software Engineering
 * Research Centre (www.lero.ie) and, in part, by the European Project Mobius 
 * IST 15909 within the IST 6th Framework. This software reflects only the 
 * authors' views and the European Community is not liable for any use that 
 * may be made of the information contained therein.
 * 
 * 
 * @see <a href="http://www.irishstatuebook.ie/1992_23.html">Part XIX of the 
   Electoral Act, 1992</a>
 * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_2.pdf">Department of
   Environment and Local Government: Count Requirements and Commentary on Count
   Rules, sections 3-16</a>
 * @see <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 * Formal Verification of Voting</a> 
 * @see <a href="http://www.jmlspecs.org/">JML Homepage</a>  
 */
//@ refine "AbstractBallotCounting.java-refined";
public abstract class AbstractBallotCounting extends ElectionStatus {

    // TODO naming convention for fields that represent model fields

    /** List of decisions made */
    protected transient /*@ spec_public @*/ Decision[] decisions 
        = new Decision[Decision.MAX_DECISIONS];
   //@ protected represents decisionsMade <- decisions;
   //@ represents numberOfDecisions <- decisionsTaken;

	/** List of candidates for election */
	protected transient /*@ spec_public @*/ Candidate[] candidates 
	  = new Candidate[Candidate.MAX_CANDIDATES];
   //@ protected represents candidateList <- candidates;

	/** List of contents of each ballot paper that will be counted. */
	protected transient Ballot[] ballots = new Ballot[Ballot.MAX_BALLOTS];
   //@ protected represents ballotsToCount <- ballots;
	
	/** Total number of candidates for election */
	protected transient /*@ spec_public @*/ int totalNumberOfCandidates;
   //@ public represents totalCandidates <- totalNumberOfCandidates;

	/** Number of candidates elected so far */
	protected transient /*@ spec_public @*/ int numberOfCandidatesElected;
   //@ public represents numberElected <- numberOfCandidatesElected;

	/** Number of candidates excluded from election so far */
	protected transient /*@ spec_public @*/ int numberOfCandidatesEliminated;
   //@ public represents numberEliminated <- numberOfCandidatesEliminated;

	/** Number of seats in this election */
	protected transient /*@ spec_public @*/ int numberOfSeats;
   //@ public represents seats <- numberOfSeats;

	/** Number of seats in this constituency */
	protected transient int totalNumberOfSeats;
  //@ protected represents totalSeats <- totalNumberOfSeats;

   /** Total number of valid ballot papers */
   protected /*@ spec_public @*/ transient int totalNumberOfVotes;
   
   /** Number of votes so far which did not have a transfer to
	 * a continuing candidate */
	protected /*@ spec_public @*/ int totalofNonTransferableVotes;
   //@ protected represents nonTransferableVotes <- totalofNonTransferableVotes;

   /** Number of votes needed to save deposit unless elected */
	protected transient /*@ spec_public @*/ int savingThreshold;
   //@ protected represents depositSavingThreshold <- savingThreshold;

	protected transient /*@ spec_public @*/ int countNumberValue;
   //@ protected represents countNumber <- countNumberValue;

	/** Number of candidates with surplus votes */
	protected /*@ spec_public @*/ int totalNumberOfSurpluses;
   //@ protected represents numberOfSurpluses <- totalNumberOfSurpluses;

	/** Total number of undistributed surplus votes */
	protected /*@ spec_public @*/ int totalSumOfSurpluses;
   //@ protected represents sumOfSurpluses <- totalSumOfSurpluses;
	
	protected transient /*@ spec_public @*/ int totalRemainingSeats;
   /*@ protected represents remainingSeats <- 
     @           numberOfSeats - numberOfCandidatesElected;
     @*/

	/** Lowest continuing vote */
	protected int lowestVote;
   //@ protected represents lowestContinuingVote <- lowestVote;

	/** The second lowest non-zero number of votes held by a continuing
	                          candidate */
	protected int nextHighest;
   //@ protected represents nextHighestVote <- nextHighest;

	/** The highest number of votes held by a continuing candidate */
	protected int highestContinuing;
   //@ protected represents highestContinuingVote <- highestContinuing;

	/** The highest number of votes held by a continuing candidate */
	protected int highestAvailableSurplus;
   //@ protected represents highestSurplus <- highestAvailableSurplus;

	/** Sum of continuing votes other than the highest */
   //@ public model int sumOfOtherContinuingVotes;
   //@ public invariant 0 <= sumOfOtherContinuingVotes;
   //@ public invariant sumOfOtherContinuingVotes <= totalVotes;
   
	/** The highest number of votes held by a continuing candidate */
	protected int totalSumOfOtherContinuingVotes;
   /*@ protected represents sumOfOtherContinuingVotes <- 
	 @    totalSumOfOtherContinuingVotes;
	 @*/

	/** Number of candidates with equal highest continuing votes */
	protected int totalNumberOfEqualHighestContinuing;
   /*@ protected represents numberOfEqualHighestContinuing <- 
     @   totalNumberOfEqualHighestContinuing;
     @*/

	/**  Number of candidates with equal lowest non-zero votes */
	protected int totalNumberOfEqualLowestContinuing;
   /*@ protected represents numberOfEqualLowestContinuing <- 
     @                      totalNumberOfEqualLowestContinuing;
     @*/

	/**
	 * Number of decisions taken.
	 */
	//@ public invariant (decisions != null) ==> (decisionsTaken <= decisions.length);
	protected transient /*@ spec_public @*/ int decisionsTaken;

	/**
 * Default Constructor.
 */
/*@ also
  @   public normal_behavior
  @     assignable state, countNumber, numberElected, numberEliminated,
  @       countNumberValue, numberOfCandidatesElected, seats, numberOfSeats,
  @       totalVotes,numberOfCandidatesEliminated, decisions, decisionsTaken,
  @       totalNumberOfVotes;
  @     ensures state == ElectionStatus.EMPTY;
  @     ensures countNumber == 0;
  @     ensures numberElected == 0;
  @*/
public AbstractBallotCounting(){
	status = ElectionStatus.EMPTY;
	countNumberValue = 0;
	numberOfCandidatesElected = 0;
	numberOfCandidatesEliminated = 0;
    createDecisionTable();
    totalNumberOfVotes = 0;
    numberOfSeats = 0;
}

/*@ assignable decisionsTaken;
  @ ensures numberOfDecisions == 0;
  @*/
private void createDecisionTable() { 
    decisionsTaken = 0;
}

/**
 * Determine if the candidate has enough votes to be elected.
 * 
 * @param candidate The candidate in question
 * @return True if the candidate has at least a quota of votes
 * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_1.pdf">
 * CEV guidelines, page 79, paragraph 120(2)</a>
 * 
 * <BON>query "Has the candidate at least a quota of votes?"</BON>
 */
/*@ also
  @   public normal_behavior
  @     requires 0 <= countNumber;
  @     requires ballotsToCount != null;
  @     requires (\forall int index; 0 <= index && index < totalVotes;
  @          ballotsToCount[index] != null); 
  @     ensures \result <==> (candidate.getTotalVote() >= getQuota());
  @*/
public /*@ pure @*/ boolean hasQuota(final /*@ non_null @*/ Candidate candidate){
	return (countBallotsFor(candidate.getCandidateID()) >= getQuota());
}

/**
 * Determine if the candidate was elected in any previous round
 * 
 * <BON>query "Has the candidate been elected?"</BON>
 * 
 * @param candidate The candidate
 * 
 * @return True if the candidate has already been elected
 */
/*@ also
  @   protected normal_behavior
  @     requires candidate != null;
  @     ensures (\result == true) <==>
  @       (candidate.getStatus() == Candidate.ELECTED || hasQuota(candidate));
  @*/
public /*@ pure @*/ boolean isElected(final Candidate candidate){
	return ((candidate.getStatus() == CandidateStatus.ELECTED) || hasQuota(candidate));
}

/**
 * Determine how many surplus votes a candidate has.
 * 
 * <BON>query "How many surplus votes does this candidate have?"</BON>
 * 
 * @design The surplus is the maximum number of votes available for transfer
 * @param candidate The candidate record
 * @return The undistributed surplus for that candidate, or zero if the 
 * candidate has less than a quota of votes
 * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_1.pdf">CEV guidelines, page 79, paragraph 120(2)</a>
 */
/*@ also
  @   protected normal_behavior
  @     requires 0 <= countNumber;
  @     requires COUNTING == state;
  @     ensures (hasQuota(candidate) == true) ==> \result ==
  @       (candidate.getTotalVote() - getQuota());
  @     ensures (hasQuota(candidate) == false) ==> \result == 0;
  @     ensures \result >= 0;
  @*/
public /*@ pure @*/ int getSurplus(final /*@ non_null @*/ Candidate candidate){
	int surplus = 0;
 	final int totalVote = countBallotsFor(candidate.getCandidateID());
	final int quota = getQuota();
	if (totalVote > quota) {			
 		surplus = totalVote - quota;
	}
	return surplus;
}

/**
 * How many elected candidates have surplus votes available for redistribution?
 * 
 * @return the totalNumberOfSurpluses
 */
public /*@ pure @*/ int getTotalNumberOfSurpluses() {
	return totalNumberOfSurpluses;
}

/**
 * Update the number of candidates with surplus votes for redistribution.
 * 
 * @param totalNumberOfSurpluses the totalNumberOfSurpluses to set
 */
//@ requires 0 <= quantity;
//@ requires quantity <= numberElected;
//@ assignable totalNumberOfSurpluses;
//@ ensures quantity == totalNumberOfSurpluses;
protected void setTotalNumberOfSurpluses(final int quantity) {
	this.totalNumberOfSurpluses = quantity;
}

/**
 * How many surplus votes are available for distribution?
 * 
 * @return the totalSumOfSurpluses
 */
public /*@ pure @*/ int getTotalSumOfSurpluses() {
	return totalSumOfSurpluses;
}

/**
 * Update the total number of surplus votes available for redistribution.
 * 
 * @param totalSumOfSurpluses the totalSumOfSurpluses to set
 */
//@ requires 0 <= sum;
//@ requires sum <= totalVotes;
//@ assignable totalSumOfSurpluses;
//@ ensures sum == totalSumOfSurpluses;
protected void setTotalSumOfSurpluses(final int sum) {
	this.totalSumOfSurpluses = sum;
}

/**
 * Determine if the candidate has enough votes to save his or her deposit.
 * 
 * <BON>query "Has this candidate saved his or her deposit?"</BON>
 * 
 * @design The deposit saving threshold is one plus one quarter of the full quota
 * @design This needs to be checked just before the candidate is eliminated to include
 *   all transfers received before the candidate was either elected or eliminated
 * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_2.pdf">CEV commentary on count rules, section 3 page 13, section 4 page 17 and section 14</a>
 * @param index The candidate for which to check
 * @return true if candidate has enough votes to save deposit
 * @throws NullCandidateException  if candidate object cannot be found
 */
/*@ also
  @  public normal_behavior
  @     requires (state == COUNTING) || (state == FINISHED);
  @     requires \nonnullelements (candidateList);
  @     requires 0 <= index;
  @     requires index < totalNumberOfCandidates;
  @     requires index < candidateList.length;
  @     ensures \result <==> 
  @       (candidateList[index].getOriginalVote() >= depositSavingThreshold) ||
  @       (isElected (candidateList[index]) == true);
  @*/
public /*@ pure @*/ boolean isDepositSaved(final int index) throws NullCandidateException{
	if (candidates == null) {
		throw new NullCandidateException();
	}
	final Candidate candidate = candidates[index];
	final int originalVote = candidate.getOriginalVote();
	final boolean elected = isElected (candidate);
	return ((originalVote >= savingThreshold) || elected);
}

/**
 * Redistribute ballots from the highest available surplus.
 * 
 * <BON>
 *   command
 *     "Calculate transfer factor",
 *     "Calculate non-fractional transfers",
 *     "Calculate fractional differences for each candidate",
 *     "Calculate adjusted number of transfers",
 *     "Move the ballots"
 * </BON>
 * 
 * @param candidateWithSurplus The elected candidate whose surplus is to be transferred
 * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_2.pdf">CEV Commentary on Count Rules, section 12, page 47</a>
 */
/*@ also
  @   protected normal_behavior
  @   requires getSurplus (candidateList[candidateWithSurplus]) > 0;
  @   requires state == COUNTING;
  @   requires getNumberContinuing() > remainingSeats;
  @   requires (getNumberContinuing() > remainingSeats + 1) ||
  @     (sumOfSurpluses + lowestContinuingVote > nextHighestVote) ||
  @     (numberOfEqualLowestContinuing > 1);
  @   requires remainingSeats > 0;
  @   requires (remainingSeats > 1) ||
  @     ((highestContinuingVote < sumOfOtherContinuingVotes + sumOfSurpluses) &&
  @     (numberOfEqualHighestContinuing == 1));
  @   requires getSurplus (candidateList[candidateWithSurplus]) == highestSurplus;
  @   requires (sumOfSurpluses + highestContinuingVote >= getQuota()) ||
  @     (sumOfSurpluses + lowestContinuingVote > nextHighestVote) ||
  @     (numberOfEqualLowestContinuing > 1) ||
  @     ((sumOfSurpluses + lowestContinuingVote >= depositSavingThreshold) &&
  @     (lowestContinuingVote < depositSavingThreshold));
  @   assignable candidates;
  @   ensures getSurplus (candidateList[candidateWithSurplus]) == 0;
  @   ensures countNumber == \old (countNumber) + 1;
  @   ensures (state == COUNTING) || (state == FINISHED);
  @   ensures totalVotes == getNumberOfBallots();
  @*/
	public abstract void distributeSurplus(int candidateWithSurplus);

/**
 * Elimination of a candidate and transfer of votes.
 * 
 * <BON>
 *   command
 *     "Calculate transfers",
 *     "Move ballots"
 * </BON>
 * 
 * @param candidatesToEliminate One or more candidates to be excluded from the 
 *   election in this count
 */

/**
 * Load candidate details and number of seats.
 * 
 * @param electionParameters The candidate details and number of seats
 */
/*@ also
  @   protected normal_behavior
  @     requires state == EMPTY;
  @     requires (\forall int c; 0 <= c && c < electionParameters.numberOfCandidates;
  @              electionParameters.candidateList[c] != null);
  @     requires electionParameters.candidateList != null &&
  @       electionParameters.numberOfCandidates <= electionParameters.candidateList.length;
  @     assignable status; 
  @     assignable totalNumberOfCandidates;
  @     assignable numberOfSeats, totalRemainingSeats;
  @     assignable totalNumberOfSeats;
  @     assignable candidates, decisions, decisionsTaken;
  @     ensures state == PRELOAD;
  @     ensures totalCandidates == electionParameters.numberOfCandidates;
  @     ensures seats == electionParameters.numberOfSeatsInThisElection;
  @     ensures totalSeats == electionParameters.totalNumberOfSeats;
  @*/
public void setup(final /*@ non_null @*/ Election electionParameters){
	this.totalNumberOfCandidates = electionParameters.numberOfCandidates; //@ nowarn;
	this.numberOfSeats = electionParameters.numberOfSeatsInThisElection; //@ nowarn;
	this.totalNumberOfSeats = electionParameters.totalNumberOfSeats; //@ nowarn;
	this.status = PRELOAD;
	for (int i = 0; i < totalNumberOfCandidates; i++) {
		this.candidates[i] = electionParameters.getCandidate(i); //@ nowarn;
	}
	this.totalRemainingSeats = this.numberOfSeats; //@ nowarn;
 }

/**
 * Open the ballot box for counting.
 * @param ballotBox The ballots to be counted
 */
/*@ also
  @   protected normal_behavior
  @     requires state == PRELOAD;
  @     assignable state, totalVotes, ballotsToCount, ballots;
  @     assignable totalNumberOfVotes;
  @     ensures state == PRECOUNT;
  @     ensures totalVotes == ballotBox.numberOfBallots;
  @*/
public void load(final /*@ non_null @*/ BallotBox ballotBox) {
 	totalNumberOfVotes = ballotBox.size(); //@ nowarn;
 	int index = 0;
 	while (index < totalNumberOfVotes && ballotBox.isNextBallot()) {
 		ballots[index++] = ballotBox.getNextBallot(); //@ nowarn;
 	}
 	status = PRECOUNT;
 	
 	// Number of first preferences for each candidate
 	calculateFirstPreferences(); //@ nowarn;
}

/**
 * Droop quota; number of votes needed to guarantee election.
 * 
 * @return Number of votes required to ensure election
 */
public /*@ pure @*/ int getQuota() {
  return 1 + (totalNumberOfVotes / (1 + numberOfSeats));
}

/**
 * Calculate the first preference counts for each candidate.
 */
/*@ requires candidates != null;
  @ requires (\forall int index; 0 <= index && index < totalNumberOfCandidates;
  @          candidates[index] != null);
  @ requires ballotsToCount != null;
  @ requires (\forall int index; 0 <= index && index < totalVotes;
  @          ballotsToCount[index] != null); 
  @ assignable candidates[*];
  @*/
public void calculateFirstPreferences() {
	for (int c = 0; c < totalNumberOfCandidates; c++) {
		final int candidateID = candidates[c].getCandidateID();
		final int numberOfBallotsInPile = countFirstPreferences(candidateID);
		candidates[c].addVote(numberOfBallotsInPile, 0);
	}
}

/**
 * Count the number of ballots in the pile for this candidate.
 * 
 * @param candidateID The internal identifier of this candidate
 * @return The number of ballots in this candidate's pile
 */
/*@ also
  @    requires ballotsToCount != null;
  @    requires (\forall int index; 0 <= index && index < totalVotes;
  @          ballotsToCount[index] != null); 
  @*/
public /*@ pure @*/ int countBallotsFor(int candidateID) {
	int numberOfBallots = 0;
	for (int b=0; b < totalNumberOfVotes; b++) {
		if (ballots[b].isAssignedTo(candidateID)) {
			numberOfBallots++;
		}
	}
	return numberOfBallots;
}

/**
 * Count the number of first preferences for this candidate.
 * 
 * @param candidateID The internal identifier of this candidate
 * @return The number of ballots in this candidate's pile
 */
/*@ also
  @    requires ballotsToCount != null;
  @    requires (\forall int index; 0 <= index && index < totalVotes;
  @          ballotsToCount[index] != null); 
  @*/
public /*@ pure @*/ int countFirstPreferences(int candidateID) {
	int numberOfBallots = 0;
	for (int b=0; b < totalNumberOfVotes; b++) {
		if (ballots[b].isFirstPreference(candidateID)) {
			numberOfBallots++;
		}
	}
	return numberOfBallots;
}

/**
 * Gets the potential number of transfers from one candidate to another.
 * 
 * @design This method is needed to get the proportions to use when 
 * transferring surplus votes
 * 
 * @param fromCandidate Candidate from which to check the transfers
 * @param toCandidateID Candidate ID to check for receipt of transferred votes
 * @return Number of votes potentially transferable from this candidate to that candidate
 */
/*@ also
  @     requires ballotsToCount != null;
  @     requires (\forall int b; 0 <= b && b < totalVotes; 
  @         ballotsToCount[b] != null);
  @     ensures \result== (\num_of int j; 0 <= j && j < totalVotes;
  @       (ballotsToCount[j].isAssignedTo(fromCandidate.getCandidateID())) &&
  @       (getNextContinuingPreference(ballotsToCount[j]) == toCandidateID));
  @*/
	protected /*@ pure spec_public @*/ int getPotentialTransfers(
	  final Candidate fromCandidate, final int toCandidateID) {
		int numberOfBallots = 0;
 		for (int j = 0; j < totalNumberOfVotes; j++) {
			if (ballots[j].isAssignedTo(fromCandidate.getCandidateID()) &&
			    (getNextContinuingPreference(ballots[j]) == toCandidateID)) {
					numberOfBallots++;
				}
			
		}
	return numberOfBallots;
	}

/**
 * Gets the status of the algorithm in progress.
 * 
 * @return The state variable value {@link #EMPTY}, {@link #SETTING_UP},
 * {@link #PRELOAD}, {@link #LOADING}, {@link #PRECOUNT},
 * {@link #COUNTING}, {@link #FINISHED}
 */
/*@ also
  @   protected normal_behavior
  @   ensures \result == state;
  @*/
public /*@ pure @*/ byte getStatus(){
	return status;
}

/**
 * Gets the next preference continuing candidate.
 * 
 * @param ballot Ballot paper from which to get the next preference
 * 
 * @return Internal ID of next continuing candidate or <code>NONTRANSFERABLE</code>
 */
/*@ also 
  @   protected normal_behavior
  @     requires state == COUNTING;
  @     ensures (\result == Ballot.NONTRANSFERABLE) <=!=>
  @       (\exists int k; 1 <= k && k < ballot.remainingPreferences();
  @       (\result == ballot.getNextPreference(k)) &&
  @       (\forall int i; 1 <= i && i < k;
  @         isContinuingCandidateID(ballot.getNextPreference(i)) == false));
  @*/
	protected /*@ pure spec_public @*/ int getNextContinuingPreference(final /*@ non_null @*/ Ballot ballot) {
		int result = Ballot.NONTRANSFERABLE;

  		for (int i = 1; i < ballot.remainingPreferences(); i++) {
			    final int nextPreference = ballot.getNextPreference(i);
			    if (isContinuingCandidateID(nextPreference)) {
			        result = nextPreference;
				      break;
			    }
		  }
		
		return result;
	} //@ nowarn;

/**
 * Determine if a candidate ID belongs to a continuing candidate.
 * 
 * @param candidateID The ID of candidate for which to check the status
 * 
 * @return <code>true</code> if this candidate ID matches that of a 
 * continuing candidate
 */
/*@ also
  @     requires 0 <= candidateID;
  @     requires candidateList != null;
  @     requires (\forall int c; 0 <= c && c < totalNumberOfCandidates;
  @              candidateList[c] != null);
  @     ensures \result == (\exists int i;
  @       0 <= i && i < candidateList.length;
  @       candidateList[i] != null &&
  @       candidateID == candidateList[i].getCandidateID() &&
  @       candidateList[i].getStatus() == CandidateStatus.CONTINUING);
  @*/
	public /*@ pure @*/ boolean isContinuingCandidateID(final int candidateID) {
		for (int i = 0; i < totalNumberOfCandidates; i++) { 
			final byte candidateStatus = candidates[i].getStatus();
			if (candidateID == candidates[i].getCandidateID()) {
                return candidateStatus == CandidateStatus.CONTINUING;
			}
		}
		return false; // not a candidate
	}

/**
 * Determine actual number of votes to transfer to this candidate
 * 
 * @design The number of votes in a surplus transferred is in proportion to
 * the number of transfers available throughout the candidate ballot stack
 * 
 * @param fromCandidate Candidate from which to count the transfers
 * @param toCandidate Continuing candidate eligible to receive votes
 * @return Number of votes available for transfer 
 */
/*@ also
  @   protected normal_behavior
  @
  @   requires isElected (fromCandidate) || 
  @            (fromCandidate.getStatus() == CandidateStatus.ELIMINATED);
  @   requires toCandidate.getStatus() == CandidateStatus.CONTINUING;
  @   requires ballotsToCount != null;
  @     requires (\forall int b; 0 <= b && b < totalVotes; 
  @         ballotsToCount[b] != null);
  @   ensures (isElected (fromCandidate) &&
  @     (getSurplus(fromCandidate) < getTotalTransferableVotes(fromCandidate)))
  @     ==>
  @       (\result == 
  @       (getSurplus (fromCandidate) *
  @         getPotentialTransfers (fromCandidate,
  @         toCandidate.getCandidateID()) /
  @         getTotalTransferableVotes (fromCandidate)));
  @   ensures ((fromCandidate.getStatus() == Candidate.ELIMINATED) ||
  @     (getTotalTransferableVotes(fromCandidate) <= getSurplus(fromCandidate)))
  @     ==>
  @       (\result == 
  @       (\num_of int j; 0 <= j && j < totalVotes;
  @         ballotsToCount[j].isAssignedTo(fromCandidate.getCandidateID()) &&
  @         getNextContinuingPreference(ballotsToCount[j]) ==
  @         toCandidate.getCandidateID()));
  @*/
	protected /*@ pure spec_public @*/ int getActualTransfers(
	          final /*@ non_null @*/ Candidate fromCandidate, 
	          final /*@ non_null @*/ Candidate toCandidate) {
		int numberOfVotes = 
		  getPotentialTransfers (fromCandidate, toCandidate.getCandidateID());
 		final int surplus = getSurplus(fromCandidate);
    final int totalTransferableVotes = 
      getTotalTransferableVotes(fromCandidate);
    if (isElected(fromCandidate) && surplus < totalTransferableVotes) {
 			 numberOfVotes *= surplus;
       numberOfVotes /= totalTransferableVotes;
		}

    return numberOfVotes;
	}


/**
 * Determine the rounded value of a fractional transfer.
 * 
 * @design This depends on the shortfall and the relative size of the other
 * fractional transfers.
 * 
 * @param fromCandidate
 * Elected candidate from which to distribute surplus
 * 
 * @param toCandidate 
 * Continuing candidate potentially eligble to recieve transfers
 * 
 * @return <code>1</code> if the fractional vote is to be rounded up
 * <code>0</code> if the fractional vote is to be rounded down
 */
/*@ also 
  @   protected normal_behavior
  @   requires state == COUNTING;
  @   requires isElected (fromCandidate);
  @   requires toCandidate.getStatus() == CandidateStatus.CONTINUING;
  @   requires getSurplus(fromCandidate) < 
  @            getTotalTransferableVotes(fromCandidate);
  @   ensures  (getCandidateOrderByHighestRemainder 
  @            (fromCandidate,toCandidate) <=
  @            getTransferShortfall (fromCandidate))
  @   ==> \result == 1;
  @   ensures (getCandidateOrderByHighestRemainder 
  @           (fromCandidate,toCandidate) >
  @           getTransferShortfall (fromCandidate))
  @   ==> \result == 0;
  @*/
protected /*@ pure spec_public @*/ int getRoundedFractionalValue(
          final /*@ non_null @*/ Candidate fromCandidate, 
          final /*@ non_null @*/ Candidate toCandidate){
 		return (getCandidateOrderByHighestRemainder 
 				(fromCandidate,toCandidate) <= 
 		  getTransferShortfall (fromCandidate)) ? 1 : 0;
 }

/**
 * Determine shortfall between sum of transfers rounded down and the size 
 * of surplus
 * 
 * @param fromCandidate
 * Elected candidate from which to distribute surplus 
 * 
 * @return The shortfall between the sum of the transfers and the size
 * of surplus
 */
/*@ also requires candidates != null;
  @      requires (\forall int c; 0 <= c && c < totalNumberOfCandidates;
  @               candidates[c] != null);
  @      requires (state == COUNTING);
  @      requires (fromCandidate.getStatus() == CandidateStatus.ELECTED) ||
  @               (fromCandidate.getStatus() == CandidateStatus.ELIMINATED);
  @*/
protected /*@ pure spec_public @*/ int getTransferShortfall(
          /*@ non_null @*/ Candidate fromCandidate){
	int shortfall = 0;
 	for (int i=0; i < totalNumberOfCandidates; i++) {
		if (candidates[i].getStatus() == CandidateStatus.CONTINUING) { //@ nowarn;
			shortfall += getActualTransfers (fromCandidate, candidates[i]); //@ nowarn;
		}
	}
	return shortfall - getSurplus(fromCandidate);
} //@ nowarn;

/**
 * Simulate random selection between two candidates.
 * 
 * @design This needs to be random but consistent, so that same 
 * result is always given for the same pair of candidates.
 * 
 * @param firstCandidate The first of the candidates to be selected from
 * 
 * @param secondCandidate The second of the candidates to be selected from
 * 
 * @return The candidate ID of the chosen candidate
 */
/*@ also 
  @   protected normal_behavior
  @     requires firstCandidate.randomNumber != secondCandidate.randomNumber;
  @     ensures (\result == firstCandidate.candidateID) <==>
  @       (firstCandidate.randomNumber < secondCandidate.randomNumber);
  @     ensures (\result == secondCandidate.candidateID) <==>
  @       (secondCandidate.randomNumber < firstCandidate.randomNumber);
  @*/
public /*@ pure @*/ int randomSelection(
		/*@ non_null @*/ Candidate firstCandidate, 
		/*@ non_null @*/ Candidate secondCandidate) {
	
 		if (firstCandidate.randomNumber < secondCandidate.randomNumber) {
			return firstCandidate.candidateID;
		}
		return secondCandidate.candidateID; 
}



/**
 * Determine the individuals remainder after integer division by the
 * transfer factor for surpluses.
 * 
 * @design This can all be done with integer arithmetic; no need to
 * use floating point numbers, which could introduce rounding errors.
 * 
 * @param fromCandidate Elected candidate from which to count to transfers
 * @param tocandidate Continuing candidate eligible to receive votes
 * 
 * @return The size of the quotient remainder 
 */
/*@ also
  @   protected normal_behavior
  @     requires candidates != null;
  @     requires (\forall int c; 0 <= c && c < totalNumberOfCandidates;
  @              candidates[c] != null);
  @     requires state == COUNTING;
  @     requires isElected (fromCandidate);
  @     requires toCandidate.getStatus() == election.tally.Candidate.CONTINUING;
  @     requires getSurplus(fromCandidate) < 
  @       getTotalTransferableVotes(fromCandidate);
  @     requires 0 <= getTransferShortfall (fromCandidate);
  @     requires 0 < getSurplus(fromCandidate);
  @     ensures \result ==
  @       getPotentialTransfers(fromCandidate, toCandidate.getCandidateID()) -
  @       getActualTransfers(fromCandidate, toCandidate);
  @        
  @*/
protected /*@ pure spec_public @*/ int getTransferRemainder(
          /*@ non_null @*/ Candidate fromCandidate, 
          /*@ non_null @*/ Candidate toCandidate){
   return getPotentialTransfers(fromCandidate, toCandidate.getCandidateID())
    - getActualTransfers(fromCandidate, toCandidate);
}

/**
 * Determine if one continuing candidate is higher than another, for the
 * purpose of resolving remainders of transfer quotients.
 * 
 * @design This is determined by finding the earliest round of counting in
 * which these candidates had unequal votes. If both candidates are equal at
 * all counts then random numbers are used to draw lots.
 * 
 * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_2.pdf">Department of
 * Environment and Local Government, Count Requirements and Commentary on
 * Count Rules, section 7, page 25</a> 
 *
 * @param firstCandidate
 * The first of the candidates to be compared
 * 
 * @param secondCandidate
 * The second of the candidates to be compared
 *  
 * @return <code>true</code> if the first candidate is deemed to have recieved more
 * votes than the second 
 */
/*@ also
  @   protected normal_behavior
  @     requires firstCandidate.getStatus() == Candidate.CONTINUING;
  @     requires secondCandidate.getStatus() == Candidate.CONTINUING;
  @     ensures \result <==> 
  @       (\exists int i; 0 <= i && i < countNumber;
  @         (firstCandidate.getVoteAtCount(i) > secondCandidate.getVoteAtCount(i)) &&
  @         (\forall int j; i < j && j < countNumber;
  @           firstCandidate.getVoteAtCount(j) == secondCandidate.getVoteAtCount(j))) 
  @      ||
  @      ((randomSelection (firstCandidate, secondCandidate) ==
  @        firstCandidate.getCandidateID()) &&
  @        (\forall int k; 0 < k && k < countNumber;
  @          firstCandidate.getVoteAtCount(k) == secondCandidate.getVoteAtCount(k)));
  @*/
	protected /*@ pure spec_public @*/ boolean isHigherThan(Candidate firstCandidate, Candidate secondCandidate) {
		
		int count = countNumberValue;
		while (0 <= count) {
			
			final int firstNumberOfVotes = firstCandidate.getVoteAtCount(count); //@ nowarn;
			final int secondNumberOfVotes = secondCandidate.getVoteAtCount(count); //@ nowarn;
			if (firstNumberOfVotes > secondNumberOfVotes) {
				return true;
			}
			else if (secondNumberOfVotes > firstNumberOfVotes) {
				return false;
			}
			count--;
		}
		
		return secondCandidate.isAfter(firstCandidate);
	} //@ nowarn;

/**
 * Determine the number of continuing candidates with a higher remainder in
 * their transfer quotient, or deemed to have a higher remainder.
 * 
 * @design There must be a strict ordering of candidates for the purpose of 
 * allocating the transfer shortfall. If two or more candidates have equal
 * remainders then use the number of transfers they are about to recieve and if
 * the number of transfers are equal then look at the number of votes all ready 
 * recieved.
 * 
 * @param fromCandidate 
 * Elected candidate from which to distribute surplus
 * 
 * @param toCandidate 
 * Continuing candidate potentially eligible to recieve transfers
 * 
 * @return The number of continuing candidates with a higher quotient remainder
 * than this candidate 
 */
/*@ also
  @   protected normal_behavior
  @     requires state == COUNTING;
  @     requires isElected (fromCandidate);
  @     requires toCandidate.getStatus() == 
  @         election.tally.Candidate.CONTINUING;
  @     requires getSurplus(fromCandidate) < 
  @         getTotalTransferableVotes(fromCandidate);
  @     ensures \result == getCandidateRanking (fromCandidate, toCandidate);
  @*/
protected /*@ pure spec_public @*/ int getCandidateOrderByHighestRemainder(
  Candidate fromCandidate, Candidate toCandidate) {
  int numberHigherThan = 0;
  final int actualTransfers = getActualTransfers(fromCandidate, toCandidate);
  final int transferRemainder = 
	  getTransferRemainder(fromCandidate, toCandidate);

	for(int i=0; i<totalNumberOfCandidates; i++){
		if(candidates[i].getCandidateID() != toCandidate.getCandidateID()&& 
				    candidates[i].getStatus() == CandidateStatus.CONTINUING){
        if(getTransferRemainder(fromCandidate, 
        		candidates[i]) > transferRemainder){
						numberHigherThan++;
					} else {
            final boolean equalRemainders = 
              getTransferRemainder(fromCandidate, candidates[i]) == 
                transferRemainder;
            final int transfersToOther = 
              getActualTransfers(fromCandidate, candidates[i]);
            if(equalRemainders &&	
            		transfersToOther > actualTransfers){
            	numberHigherThan++;
            }
            else if(equalRemainders && 
            		transfersToOther == actualTransfers && 
            		isHigherThan (candidates[i], toCandidate)){
            	numberHigherThan++;
            }
          }
					
				}
			}
	return numberHigherThan;
}

/**
 * Get the maximum number of votes transferable to continuing candidates.
 * 
 * @param fromCandidate Candidate ID fromwhich to check the transfers
 * 
 * @return Number of votes potentially transferable from this candidate
 */
/*@ also
  @   protected normal_behavior
  @     requires (state == COUNTING);
  @     requires candidateList != null && (\forall int i;
  @              0 <= i && i < totalNumberOfCandidates; 
  @              candidateList[i] != null);
  @     requires (fromCandidate.getStatus() == CandidateStatus.ELECTED) ||
  @       (fromCandidate.getStatus() == CandidateStatus.ELIMINATED);
  @     ensures \result == numberTransferable (fromCandidate);
  @*/
protected /*@ pure spec_public @*/ int getTotalTransferableVotes(
    final /*@ non_null @*/ Candidate fromCandidate) {
    int numberOfTransfers = 0;
 	for (int i = 0; i < totalNumberOfCandidates; i++) {
 		numberOfTransfers += getPotentialTransfers(
 				fromCandidate, candidates[i].getCandidateID());
 	}
	return numberOfTransfers;
} 

/**
 * Transfer votes from one candidate to another.
 * 
 * @param fromCandidate Elected or excluded candidate
 * @param toCandidate Continuing candidate
 * @param numberOfVotes Number of votes to be transferred
 * 
 * <BON>command</BON>
 */
/*@ also
  @   protected normal_behavior
  @     requires fromCandidate.getStatus() != Candidate.CONTINUING;
  @     requires toCandidate.getStatus() == Candidate.CONTINUING;
  @     requires numberOfVotes == getActualTransfers (fromCandidate,toCandidate) +
  @       getRoundedFractionalValue (fromCandidate, toCandidate);
  @		assignable ballotsToCount;
  @     ensures fromCandidate.getTotalVote() ==
  @       \old (fromCandidate.getTotalVote()) - numberOfVotes;
  @     ensures toCandidate.getTotalVote() ==
  @       \old (toCandidate.getTotalVote()) + numberOfVotes;
  @*/
public abstract void transferVotes(/*@ non_null @*/ Candidate fromCandidate, 
		/*@ non_null @*/ Candidate toCandidate, int numberOfVotes);

/**
 * Update list of decision events.
 * 
 * @param The decision to be added.
 */
/*@ also
  @   requires state == COUNTING;
  @   assignable decisions[*], decisionsTaken;
  @   ensures (\forall int i; 0 <= i && i < totalCandidates;
  @     isElected (candidateList[i]) ==> (\exists int k;
  @     0 <= k && k < numberOfDecisions;
  @   (decisionsMade[k].candidateID == candidateList[i].getCandidateID()) &&
  @   ((decisionsMade[k].decisionTaken == Decision.ELECT_BY_QUOTA) ||
  @   (decisionsMade[k].decisionTaken == Decision.DEEM_ELECTED))) &&
  @   (\forall int n; 0 <= n && n < numberOfDecisions;
  @   (decisionsMade[n].candidateID == candidateList[i].getCandidateID())
  @   ==> (decisionsMade[n].decisionTaken != Decision.EXCLUDE)));
  @*/
	protected void updateDecisions(Decision decision) {
		decisions[decisionsTaken] = decision;
		decisionsTaken++;
}

	/**
	 * Who is the highest continuing candidate, not yet elected?
	 * 
	 * @return The continuing candidate with the most votes
	 */
	/*@ requires 1 <= getNumberContinuing();
	  @ requires candidateList != null && (\forall int c;
	  @          0 <= c && c < totalNumberOfCandidates; candidateList[c] != null);
	  @ ensures (\max int i; 0 <= i && i < totalCandidates && 
	  @   candidateList[i].getStatus() == Candidate.CONTINUING;
	  @   countBallotsFor(candidateList[i].getCandidateID())) 
	  @   == countBallotsFor(candidateList[\result].getCandidateID());
	  @ ensures \result == -1 || (\exists int i; 0 <= i && i < totalCandidates && 
	  @   candidates[i].getStatus() == Candidate.CONTINUING; i == \result);
	  @ ensures 0 <= \result && \result < totalCandidates;
	  @ ensures candidateList[\result] != null;
	  @*/
	public /*@ pure @*/ int findHighestCandidate() {
		
	  int highestCandidate = -1;  
		long mostVotes = 0;
	
		for (int i=0; i < totalNumberOfCandidates; i++) {
			if (candidates[i].getStatus() == CandidateStatus.CONTINUING) {
			  final int votes = countBallotsFor(candidates[i].getCandidateID());
        if (votes > mostVotes) {
				     mostVotes = votes;
				     highestCandidate = i;
			  } else if (0 <= highestCandidate && votes == mostVotes &&
				    isHigherThan(candidates[i],candidates[highestCandidate])) {
					   highestCandidate =  i;
			  }
			}
		}
		
		return highestCandidate;
	}

	/**
	 * Who is the lowest continuing candidate?
	 * 
	 * @return The continuing candidate with the least votes
	 */
	/*@ requires 1 <= totalCandidates;
	  @ requires \nonnullelements(candidates);
	  @ ensures (\forall int i; 
	  @   0 <= i && i < totalCandidates && 
	  @   candidateList[i].getStatus() == CandidateStatus.CONTINUING;
	  @   countBallotsFor(candidateList[i].getCandidateID()) >= 
	  @   countBallotsFor(candidateList[\result].getCandidateID()));
	  @ ensures -1 == \result || (\exists int i; 
	  @   0 <= i && i < totalCandidates && 
	  @   candidateList[i].getStatus() == CandidateStatus.CONTINUING;
	  @   i == \result);
	  @*/
	public /*@ pure @*/ int findLowestCandidate() {
		
		long leastVotes = CountConfiguration.MAXVOTES;
		int lowest = -1; 

		for (int i=0; i < totalNumberOfCandidates; i++) {
			if (candidates[i].getStatus() == CandidateStatus.CONTINUING) {
			  final int votes = countBallotsFor(candidates[i].getCandidateID());
			  if (votes < leastVotes) {
				    leastVotes = votes;
				    lowest = i;
			  } else if (0 <= lowest && votes == leastVotes &&
 				    isHigherThan(candidates[lowest],candidates[i])) {
					lowest = i;
			  }
			}
		}
		
		return lowest;
	} //@ nowarn;

	/**
	 * Exclude one candidate from the election.
	 * 
	 * @param loser The candidate to be excluded
	 */
	/*@ requires candidateList[loser].getStatus() == Candidate.CONTINUING;
	  @ requires candidateList[loser] != null;
	  @ requires remainingSeats < getNumberContinuing();
	  @ requires (state == COUNTING);
	  @ requires 0 <= loser && loser < getNumberContinuing();
	  @ assignable candidateList, decisions[*], decisionsTaken;
	  @ assignable candidateList[loser];
	  @ ensures remainingSeats <= getNumberContinuing();
	  @ ensures numberElected <= seats;
	  @ ensures \old(lowestContinuingVote) <= lowestContinuingVote;
	  @ ensures candidateList[loser].getStatus() == Candidate.ELIMINATED;
	  @ ensures (\forall int b; 0 <= b && b < ballotsToCount.length;
	  @   ballotsToCount[b].getCandidateID() != candidateList[loser].getCandidateID());
	  @*/
	public void eliminateCandidate(final int loser) {
		final int candidateID = candidates[loser].getCandidateID();

		candidates[loser].declareEliminated(); //@ nowarn;
		redistributeBallots(candidateID); //@ nowarn;
		auditDecision(DecisionStatus.EXCLUDE, candidateID);
	}

	/**
	 * Audit a decision event.
	 * 
	 * @param decisionType The type of decision made
	 * @param candidateID The candidate about which the decision was made
	 */
	/*@ requires (\exists int i; 0 <= i && i < totalCandidates;
	  @  candidates[i].getCandidateID() == candidateID);
	  @ requires (decisionType == Decision.EXCLUDE) ||
	  @   (decisionType == Decision.DEEM_ELECTED) ||
	  @   (decisionType == Decision.ELECT_BY_QUOTA);
	  @ assignable decisions[*], decisionsTaken;
	  @ ensures \old(numberOfDecisions) < numberOfDecisions;
	  @*/
	protected void auditDecision(final byte decisionType, final int candidateID) {
		 
		Decision decision = new Decision(); // NOPMD
		decision.atCountNumber = countNumberValue;
		decision.candidateID = candidateID;
		decision.chosenByLot = false;
		decision.decisionTaken = decisionType;
		updateDecisions(decision); //@ nowarn;
	}

	/**
	 * Redistribute the transferable ballots of an excluded candidate.
	 * 
	 * @param The unique identifier for the excluded candidate
	 */
	/*@ requires candidateID != Ballot.NONTRANSFERABLE;
	  @ requires ballots != null && (\forall int b;
	  @          0 <= b && b < totalVotes; ballots[b] != null &&
	  @          ballots[b].countNumberAtLastTransfer <= countNumberValue);
	  @ assignable ballots[*];
	  @ ensures (\forall int b; 0 <= b && b < ballotsToCount.length;
	  @   ballotsToCount[b].getCandidateID() != candidateID);
	  @*/
	protected void redistributeBallots(final int candidateID) {

		for (int b = 0; b < totalNumberOfVotes; b++) {
			if (ballots[b].getCandidateID() == candidateID) {
				
				transferBallot(ballots[b]); //@ nowarn;
			}
		}
	} //@ nowarn;

	/**
	 * Transfer the ballot until non-transferable or a continuing candidate is found.
	 * 
	 * @param ballot The ballot
	 */
	/*@ requires ballot.countNumberAtLastTransfer <= countNumberValue;
	  @ assignable ballot.countNumberAtLastTransfer;
	  @ assignable ballot.positionInList;
	  @ assignable ballot.candidateIDAtCount[*];
	  @*/
	public void transferBallot(/*@ non_null @*/ Ballot ballot) {
		 
		while ((ballot.getCandidateID() != Ballot.NONTRANSFERABLE) && 
				(!isContinuingCandidateID(ballot.getCandidateID()))) {
			ballot.transfer(countNumberValue);
 		}
	}
	
	public abstract void count();

	/**
	 * Elect this winning candidate.
	 * 
	 * @param winner The candidate with enough votes to win
	 */
	//@ requires 0 <= winner && winner < totalCandidates;
	//@ requires candidateList[winner] != null;
	//@ requires candidateList[winner].getStatus() == Candidate.CONTINUING;
	//@ requires numberElected < seats;
	//@ requires 0 < getNumberContinuing();
	//@ requires 0 < remainingSeats;
	//@ assignable candidates, decisions, decisionsTaken, numberOfCandidatesElected;
	//@ assignable totalRemainingSeats;
	//@ assignable candidates[winner], candidates[winner].state;
	//@ ensures isElected (candidateList[winner]);
	//@ ensures 1 + \old(numberElected) == numberElected;
	//@ ensures \old(getNumberContinuing()) == 1 + getNumberContinuing();
	//@ ensures \old(remainingSeats) == 1 + remainingSeats;
	public void electCandidate(int winner) {
	  candidates[winner].declareElected();
		auditDecision(DecisionStatus.DEEM_ELECTED,candidates[winner].getCandidateID()); //@ nowarn;
		numberOfCandidatesElected++;
 		totalRemainingSeats--;
	}

	/*@ also 
	  @ requires candidates != null && 
	  @          (\forall int c; 0 <= c && c < totalNumberOfCandidates;
	  @          candidates[c] != null);
	  @ ensures \result == numberOfContinuingCandidates();
	  @*/
	public /*@ pure @*/ int getNumberContinuing() {
		int numberContinuing = 0;
		
		for (int i = 0; i < totalNumberOfCandidates; i++) {
			if (candidates[i].getStatus() == CandidateStatus.CONTINUING) {
				numberContinuing++;
			}
		}
		
 		return numberContinuing;
	}
	
	/*@ ensures \result == (\num_of int i; i <= 0 && 
	  @         i < totalNumberOfCandidates;
	  @         candidateList[i].getStatus() == CandidateStatus.CONTINUING);
	  @
	  @ public pure model int numberOfContinuingCandidates() {
	  @ int numberContinuing = 0;
	  @	
	  @	for (int i = 0; i < totalNumberOfCandidates; i++) {
	  @		if (candidateList[i].getStatus() == CandidateStatus.CONTINUING) {
	  @			numberContinuing++;
	  @		}
	  @	}
	  @	
 	  @	return numberContinuing;
	  @ }
	  @*/
}