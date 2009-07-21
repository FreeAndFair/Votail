package election.tally;

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
 * @design
 * This Java package <code>election.tally</code> is designed to be used with 
 * either an optical ballot scan system or else a remote online voting system 
 * that supplies a valid set of ballots and candidate IDs to be counted by this 
 * algorithm and takes care of system level issues such as security, 
 * authentication and data storage.
 * 
 * @process
 * This JML specification and associated Java code is intended 
 * to be verifiable using the Extended Static Checking for Java
 * version 2 tool (ESCJava2), the Mobius Program Verification Environment (PVE),
 * JML4 and other JML software engineering tools. The BON specification
 * is intended to be checkable with the BONc tool.
 * 
 * @see <a href="http://www.irishstatuebook.ie/1992_23.html">Part XIX of the 
   Electoral Act, 1992</a>
 * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_2.pdf">Department of
   Environment and Local Government: Count Requirements and Commentary on Count
   Rules, sections 3-16</a>
 * @see <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 * Formal Verification of Remote Voting</a> 
 * @see <a href="http://kind.ucd.ie/products/opensource/ESCJava2/">
 * ESCJava/2 static checker for Java</a>
 * @see <a href="http://www.jmlspecs.org/">JML Homepage</a>  
 */
//@ refine "AbstractBallotCounting.java-refined";
public abstract class AbstractBallotCounting extends ElectionStatus {
	/**
	 * Outer level of Abstract State Machine for Election Algorithm.
	 */
	/*@ public model byte state;
	  @ public invariant EMPTY < SETTING_UP;
	  @ public invariant SETTING_UP < PRELOAD;
	  @ public invariant PRELOAD < LOADING;
	  @ public invariant LOADING < PRECOUNT;
	  @ public invariant PRECOUNT < COUNTING;
	  @ public invariant COUNTING < FINISHED;
	  @ public initially state == EMPTY;
	  @ public constraint \old (state) <= state;
	  @ public invariant (state == EMPTY) || (state == SETTING_UP) || 
	  @   (state == PRELOAD) ||
	  @   (state == LOADING) || (state == PRECOUNT) || 
	  @   (state == COUNTING) ||
	  @   (state == FINISHED);
	  @*/
	
	protected transient /*@ spec_public @*/ byte status; //@ in state;
  //@ public represents state <- status;
	/*@
	  @ public invariant status == EMPTY ||status == SETTING_UP || 
	  @   status == PRELOAD ||
	  @   status == LOADING || status == PRECOUNT || status == COUNTING ||
	  @   status == FINISHED;
	  @*/
	
	/** List of decisions made */
	/*@ public model non_null election.tally.Decision[] decisionsMade;
	  @ public invariant 
	  @   (\forall int i; 0 <= i && i < numberOfDecisions;
	  @   decisionsMade[i].decisionTaken != Decision.NO_DECISION &&
	  @   decisionsMade[i].atCountNumber < countNumber &&
	  @   (\exists int k; 0 <= k && k < totalCandidates;
	  @     decisionsMade[i].candidateID == 
	  @     candidateList[k].getCandidateID()));
	  @ protected invariant numberOfDecisions < decisions.length;
	  @*/
	
	protected transient /*@ spec_public @*/ Decision[] decisions;
   //@ protected represents decisionsMade <- decisions;

	/** Number of decisions made */
	/*@ public model int numberOfDecisions;
	  @ public initially numberOfDecisions == 0 || decisionsMade == null ||
	  @   (\forall int i; 0 <= i && i < numberOfDecisions;
	  @   decisionsMade[i].decisionTaken == Decision.NO_DECISION);
	  @ public invariant 0 <= numberOfDecisions;
	  @ public constraint 
	  @   \old (numberOfDecisions) <= numberOfDecisions;
	  @ public constraint (state != COUNTING) ==>
	  @   numberOfDecisions == \old (numberOfDecisions);
	  @*/
	//@ represents numberOfDecisions <- decisions.length;
	
	/** List of details for each candidate.
	* @constraint There are no duplicates in the list of candidate 
	* IDs and, once the counting starts, there must be a ballot paper 
	* associated with each vote held by a candidate.
	*/
   //@ public model non_null Candidate[] candidateList;
	/*@ public invariant (state == PRELOAD || state == LOADING || 
	  @   state == PRECOUNT)
	  @ ==>
	  @ (\forall int i; 0 <= i && i < totalCandidates;
	  @   candidateList[i].getStatus() == Candidate.CONTINUING &&
	  @   candidateList[i].getTotalVote() == 0 &&
	  @   candidateList[i].getOriginalVote() == 0);
	  @
	  @ public invariant (state == PRELOAD || state == LOADING ||   
	  @   state == PRECOUNT ||
	  @   state == COUNTING || state == FINISHED)
	  @ ==>
	  @   (\forall int i, j;
	  @     0 <= i && i < totalCandidates && 
	  @     i < j && j < totalCandidates;
	  @     candidateList[i].getCandidateID() != 
	  @     candidateList[j].getCandidateID());
	  @
	  @ public invariant (state == PRELOAD || state == LOADING || 
	  @   state == PRECOUNT ||
	  @   state == COUNTING || state == FINISHED)
	  @ ==>
	  @   (\forall int i;
	  @     0 <= i && i < totalCandidates;
	  @     candidateList[i].getCandidateID() != 
	  @     Ballot.NONTRANSFERABLE);
	  @
	  @ protected invariant (state == COUNTING || state == FINISHED)
	  @ ==> 
	  @  (\forall int i; 0 <= i && i < totalCandidates;
	  @    candidateList[i].getTotalVote() ==
	  @    countBallotsFor (candidateList[i].getCandidateID()));
	  @*/

	/** List of candidates for election */
	protected transient /*@ spec_public non_null @*/ Candidate[] candidates;
   //@ protected represents candidateList <- candidates;
	

	/** List of contents of each ballot paper that will be counted. */
   //@ public model non_null Ballot[] ballotsToCount;
	/*@ protected invariant (state >= PRECOUNT)
	  @ ==>
	  @   (\forall int i, j;
	  @     0 <= i && i < totalVotes && i < j && j < totalVotes;
	  @     ballotsToCount[i].getBallotID() != ballotsToCount[j].getBallotID());
	  @*/
	protected transient Ballot[] ballots;
   //@ protected represents ballotsToCount <- ballots;
	
	/** Total number of candidates for election */
   //@ public model int totalCandidates;
   //@ public invariant 0 <= totalCandidates;
   //@ public invariant totalCandidates <= candidateList.length;
	/*@ public constraint (state >= LOADING) ==>
	  @ totalCandidates == \old (totalCandidates);
	  @ protected invariant (state == FINISHED) ==> totalCandidates ==
	  @   numberElected + numberEliminated;
	  @ public invariant (state == COUNTING) ==> 1 <= totalCandidates;
	  @*/
	protected transient /*@ spec_public @*/ int totalNumberOfCandidates;
   //@ public represents totalCandidates <- totalNumberOfCandidates;
	
	/** Number of candidates elected so far */
   //@ public model int numberElected;
   //@ protected invariant 0 <= numberElected;
   //@ protected invariant numberElected <= seats;
	/*@ protected invariant (state <= PRECOUNT) ==> numberElected == 0;
	  @ protected invariant (COUNTING <= state && state <= FINISHED)
	  @ ==> 
	  @   numberElected == (\num_of int i; 0 <= i && i < totalCandidates;
	  @   isElected(candidateList[i]));
	  @ protected invariant (state == FINISHED) ==>
	  @   numberElected == seats;
	  @ protected constraint (state == COUNTING) ==>
	  @   \old(numberElected) <= numberElected;
	  @*/
	/** Number of candidates elected so far */
	protected transient /*@ spec_public @*/ int numberOfCandidatesElected;
   //@ public represents numberElected <- numberOfCandidatesElected;
	
	/** Number of candidates excluded from election so far */
   //@ public model int numberEliminated;
   //@ protected invariant 0 <= numberEliminated;
   //@ protected invariant numberEliminated <= totalCandidates - seats;
	/*@ protected invariant (state == COUNTING || state == FINISHED)
	  @ ==> 
	  @  numberEliminated == (\num_of int i; 0 <= i && i < totalCandidates;
	  @  candidateList[i].getStatus() == Candidate.ELIMINATED);
	  @*/
	/** Number of candidates excluded from election so far */
	protected transient /*@ spec_public @*/ int numberOfCandidatesEliminated;
   //@ public represents numberEliminated <- numberOfCandidatesEliminated;

	/** Number of seats to be filled in this election */
   //@ public model int seats;
   //@ public invariant 0 <= seats;
   //@ public invariant seats <= totalSeats;
	/*@ public constraint (state == LOADING || state == COUNTING) ==>
	  @   (seats == \old (seats));
	  @ public invariant (state == COUNTING) ==> (1 <= seats);
	  @*/
	/** Number of seats in this election */
	protected transient /*@ spec_public @*/ int numberOfSeats;
   //@ public represents seats <- numberOfSeats;
	
	/** Total number of seats in this constituency
	 * @design The constitution and laws of Ireland do not allow less than three or
	 * more than five seats in each Dail constituency, but this could change in
	 * future and is not an essential part of the specification.
	 */
   //@ public model int totalSeats;
   //@ public invariant 0 <= totalSeats;
	/*@ public constraint (LOADING <= state) ==>
	  @   (totalSeats == \old (totalSeats)) && (1 <= totalSeats);
	  @*/
	/** Number of seats in this constituency */
	protected transient int totalNumberOfSeats;
  //@ protected represents totalSeats <- totalNumberOfSeats;

	/** Total number of valid votes in this election */
   //@ public model int totalVotes;
   //@ public invariant 0 <= totalVotes;
   /*@ public invariant (state == PRECOUNT || state == COUNTING || state == FINISHED)
     @   ==> totalVotes <= ballotsToCount.length;
	   @ public invariant (state == EMPTY || state == SETTING_UP || 
	   @   state == PRELOAD)
	   @ ==> 
	   @   totalVotes == 0;
	   @ public constraint (state == LOADING)
	   @ ==> 
	   @   \old (totalVotes) <= totalVotes;
	   @ public constraint (state == PRECOUNT || state == COUNTING ||
	   @   state == FINISHED)
	   @ ==> 
	   @  totalVotes == \old (totalVotes);
	   @*/
	
   /** Total number of valid ballot papers */
	protected transient int totalNumberOfVotes;
   
   /** 
    * Article 16 of the constitution of the Republic or Ireland specifies 
    * a maximum of 30,000 people per seat, and the current electoral laws 
    * specify a maximum of five seats per national constituency, so the 
    * maximum possible number of ballots is 150,000. 
    */
	final protected static int MAXVOTES = 150000;
   
   //@ protected represents totalVotes <- totalNumberOfVotes;
	
	/** Number of votes so far which did not have a transfer to
	 * a continuing candidate */
   //@ public model int nonTransferableVotes;
   //@ public invariant 0 <= nonTransferableVotes;
   //@ public invariant nonTransferableVotes <= totalVotes;
	/*@ protected invariant (state == COUNTING || state == FINISHED)
	  @ ==> nonTransferableVotes == 
	  @   (\num_of int i; 0 <= i && i < totalVotes;
	  @     ballotsToCount[i].getCandidateID() == Ballot.NONTRANSFERABLE);
	  @*/
	protected /*@ spec_public @*/ int totalofNonTransferableVotes;
   //@ protected represents nonTransferableVotes <- totalofNonTransferableVotes;

	/** Number of votes needed to guarantee election */
  //@ public invariant 0 <= getQuota();
  //@ public invariant getQuota() <= totalVotes;
	/*@ public invariant (state == COUNTING) ==>
	  @   getQuota() == 1 + (totalVotes / (seats + 1));
	  @*/
 
	/** Number of votes needed to save deposit unless elected */
   //@ public model int depositSavingThreshold;
   //@ public invariant 0 <= depositSavingThreshold;
   //@ public invariant depositSavingThreshold <= totalVotes;
	/*@ public invariant (state == COUNTING) 
	  @ ==> depositSavingThreshold ==
	  @   (((totalVotes / (totalSeats + 1)) + 1) / 4) + 1;
	  @*/
	protected transient /*@ spec_public @*/ int savingThreshold;
   //@ protected represents depositSavingThreshold <- savingThreshold;

	/** Number of rounds of counting so far */
   //@ public model int countNumber;
   //@ public initially countNumber == 0;
   //@ public invariant 0 <= countNumber;
   //@ public invariant countNumber < Candidate.MAXCOUNT;
	/*@ public constraint (state == COUNTING) ==> 
	  @   \old(countNumber) <= countNumber;
	  @
	  @ public constraint (state == COUNTING) ==>
	  @   countNumber <= \old (countNumber) + 1;
	  @*/
	protected transient /*@ spec_public @*/ int countNumberValue;
   //@ protected represents countNumber <- countNumberValue;

	/** Number of candidates with surplus votes */
   //@ public model int numberOfSurpluses;
   //@ public invariant 0 <= numberOfSurpluses;
   //@ protected invariant numberOfSurpluses <= numberElected;
	protected /*@ spec_public @*/ int totalNumberOfSurpluses;
   //@ protected represents numberOfSurpluses <- totalNumberOfSurpluses;

	/** Total number of undistributed surplus votes */
   //@ public model int sumOfSurpluses;
   //@ public invariant 0 <= sumOfSurpluses;
   //@ public invariant sumOfSurpluses <= totalVotes;
	/*@ invariant (state == COUNTING) 
	  @ ==> sumOfSurpluses == (\sum int i; 
	  @   0 <= i && i < totalCandidates; getSurplus(candidateList[i]));
	  @*/
	/** Number of candidates with surplus votes */
	protected /*@ spec_public @*/ int totalSumOfSurpluses;
   //@ protected represents sumOfSurpluses <- totalSumOfSurpluses;

	
   //@ public model int remainingSeats;
   //@ public invariant 0 <= remainingSeats;
   //@ public invariant remainingSeats <= seats;
	/*@ public invariant (state <= PRECOUNT) ==> 
	  @   remainingSeats == seats;
	  @ public invariant (state == FINISHED) ==>
	  @   remainingSeats == 0;
	  @ protected invariant (state == COUNTING) ==>
	  @   remainingSeats == (seats - numberElected);
	  @*/
	
	protected transient /*@ spec_public @*/ int totalRemainingSeats;
   /*@ protected represents remainingSeats <- numberOfSeats - numberOfCandidatesElected;
     @*/

	/** Number of candidates neither elected nor excluded from election */
  //@ public invariant 0 <= getNumberContinuing();
	/*@ public invariant 
	  @   getNumberContinuing() <= totalCandidates;
	  @
	  @ public invariant (state == FINISHED) ==>
	  @   getNumberContinuing() == 0;
	  @ invariant (state == COUNTING) ==>  
	  @   getNumberContinuing() ==
	  @   (totalCandidates - numberElected) - numberEliminated;
	  @*/
  	
	/** There must be at least one continuing candidate for each remaining seat
	 * @see requirement 11, section 4, item 4, page 16
	 */
	/*@ invariant (state == COUNTING) ==>
	  @   remainingSeats <= getNumberContinuing();
	  @*/

	/** The lowest non-zero number of votes held by a continuing candidate */
   //@ public model int lowestContinuingVote;
   //@ public invariant 0 < lowestContinuingVote;
	/*@ public invariant
	  @   (\exists int k; 0 <= k && k < totalCandidates;
	  @     candidateList[k].getStatus() == Candidate.CONTINUING &&
	  @     0 < candidateList[k].getTotalVote())
	  @ ==> lowestContinuingVote ==
	  @   (\min int i; 0 <= i && i < totalCandidates &&
	  @     candidateList[i].getStatus() == Candidate.CONTINUING &&
	  @     0 < candidateList[i].getTotalVote();
	  @     candidateList[i].getTotalVote());
	  @*/
	/** Lowest continuing vote */
	protected int lowestVote;
   //@ protected represents lowestContinuingVote <- lowestVote;

	/** The second lowest non-zero number of votes held by a continuing candidate */
   //@ public model int nextHighestVote;
   //@ public invariant lowestContinuingVote < nextHighestVote;
	/*@ public invariant
	  @   (\exists int k; 0 <= k && k < totalCandidates;
	  @     candidateList[k].getStatus() == Candidate.CONTINUING &&
	  @     lowestContinuingVote < candidateList[k].getTotalVote())
	  @ ==> nextHighestVote ==
	  @   (\min int i; 0 <= i && i < totalCandidates &&
	  @     candidateList[i].getStatus() == Candidate.CONTINUING &&
	  @     lowestContinuingVote < candidateList[i].getTotalVote();
	  @     candidateList[i].getTotalVote());
	  @*/
	/** The second lowest non-zero number of votes held by a continuing
	                          candidate */
	protected int nextHighest;
   //@ protected represents nextHighestVote <- nextHighest;

	/** The highest number of votes held by a continuing candidate */
   //@ public model int highestContinuingVote;
   //@ public invariant highestContinuingVote < getQuota();
	/*@ public invariant (0 < getNumberContinuing())
	  @ ==> highestContinuingVote ==
	  @   (\max int i; 0 < i && i < totalCandidates &&
	  @     candidateList[i].getStatus() == Candidate.CONTINUING;
	  @     candidateList[i].getTotalVote());
	  @*/
	/** The highest number of votes held by a continuing candidate */
	protected int highestContinuing;
   //@ protected represents highestContinuingVote <- highestContinuing;

	/** Highest available surplus for distribution */
   //@ public model int highestSurplus;
   //@ public invariant 0 <= highestSurplus;
   //@ public invariant highestSurplus <= sumOfSurpluses;
	/*@ invariant (state == COUNTING) ==> highestSurplus ==
	  @   (\max int i; 0 < i && i < totalCandidates; 
	  @   getSurplus(candidateList[i]));
	  @*/
	/** The highest number of votes held by a continuing candidate */
	protected int highestAvailableSurplus;
   //@ protected represents highestSurplus <- highestAvailableSurplus;

	/** Sum of continuing votes other than the highest */
   //@ public model int sumOfOtherContinuingVotes;
   //@ public invariant 0 <= sumOfOtherContinuingVotes;
   //@ public invariant sumOfOtherContinuingVotes <= totalVotes;
	/*@ invariant (state == COUNTING) ==> sumOfOtherContinuingVotes ==
	  @ (\sum int i; 0 <= i && i < totalCandidates &&
	  @ candidateList[i].getStatus() == Candidate.CONTINUING
	  @ && candidateList[i].getTotalVote() < highestContinuingVote;
	  @ candidateList[i].getTotalVote());
	  @*/
	/** The highest number of votes held by a continuing candidate */
	protected int totalSumOfOtherContinuingVotes;
   //@ protected represents sumOfOtherContinuingVotes <- totalSumOfOtherContinuingVotes;

	/** Number of candidates with equal highest continuing votes */
   //@ public model int numberOfEqualHighestContinuing;
   //@ public invariant 0 <= numberOfEqualHighestContinuing;
	/*@ public invariant
	  @ numberOfEqualHighestContinuing <= getNumberContinuing();
	  @ public invariant (state == COUNTING) ==> numberOfEqualHighestContinuing ==
	  @ (\num_of int i; 0 <= i && i < totalCandidates &&
	  @ candidateList[i].getStatus() == Candidate.CONTINUING;
	  @ candidateList[i].getTotalVote() == highestContinuingVote);
	  @*/
	/** Number of candidates with equal highest continuing votes */
	protected int totalNumberOfEqualHighestContinuing;
   //@ protected represents numberOfEqualHighestContinuing <- totalNumberOfEqualHighestContinuing;
	
	/** Number of candidates with equal lowest non-zero votes */
   //@ public model int numberOfEqualLowestContinuing;
   //@ public invariant 0 <= numberOfEqualLowestContinuing;
	/*@ public invariant
	  @ numberOfEqualLowestContinuing <= getNumberContinuing();
	  @ public invariant (state == COUNTING) ==> numberOfEqualLowestContinuing ==
	  @ (\num_of int i; 0 <= i && i < totalCandidates &&
	  @   candidateList[i].getStatus() == Candidate.CONTINUING;
	  @   candidateList[i].getTotalVote() == lowestContinuingVote);
	  @*/
	/**  Number of candidates with equal lowest non-zero votes */
	protected int totalNumberOfEqualLowestContinuing;
   /*@ protected represents numberOfEqualLowestContinuing <- 
     @                      totalNumberOfEqualLowestContinuing;
     @ 
     @*/
	
	/**
	 * Number of decisions taken.
	 */
	//@ public invariant decisionsTaken <= decisions.length;
	protected transient /*@ spec_public @*/ int decisionsTaken;
	
/**
 * @design The election count algorithm is modeled as a two tier abstract state
 * machine with states and transitions between those states:
 * 
 *  <p> The normal path for the outer tier is:
 *  <p> Empty --> SETUP --> PRELOAD --> LOADING -->
 *  PRECOUNT --> COUNTING --> FINISHED
 *   
 */	

/**
 * Default Constructor.
 */
/*@ also
  @   public normal_behavior
  @		assignable state, countNumber, numberElected, numberEliminated,
  @       countNumberValue, numberOfCandidatesElected, 
  @       numberOfCandidatesEliminated, decisions;
  @     ensures state == EMPTY;
  @     ensures countNumber == 0;
  @     ensures numberElected == 0;
  @*/
public AbstractBallotCounting(){
  super();
	status = EMPTY;
	countNumberValue = 0;
	numberOfCandidatesElected = 0;
	numberOfCandidatesEliminated = 0;
	decisions = new Decision[0];
	//@ assume numberOfDecisions == 0;
} //@ nowarn;

/**
 * Determine if the candidate has enough votes to be elected.
 * 
 * @param candidate The candidate in question
 * @return True if the candidate has at least a quota of votes
 * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_1.pdf">CEV guidelines, page 79, paragraph 120(2)</a>
 * 
 * <BON>query "Has the candidate at least a quota of votes?"</BON>
 */
/*@ also
  @   public normal_behavior
  @     requires candidate != null;
  @     requires 0 <= countNumber;
  @     ensures \result <==> (candidate.getTotalVote() >= getQuota());
  @*/
public /*@ pure @*/ boolean hasQuota(final /*@ non_null @*/ Candidate candidate){
	return (candidate.getTotalVote() >= getQuota()); //@ nowarn;
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
 	final int totalVote = candidate.getTotalVote(); //@ nowarn;
	if (totalVote > getQuota()) {			
 		surplus = totalVote - getQuota();
	}
	return surplus;
}

/**
 * How many elected candidates have surplus votes available for redistribution?
 * 
 * @return the totalNumberOfSurpluses
 */
protected /*@ pure @*/ int getTotalNumberOfSurpluses() {
	return totalNumberOfSurpluses;
} //@ nowarn;

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
protected /*@ pure @*/ int getTotalSumOfSurpluses() {
	return totalSumOfSurpluses;
} //@ nowarn;

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
 */
/*@ also
  @   protected normal_behavior
  @     requires (state == COUNTING) || (state == FINISHED);
  @     ensures \result <==> (candidateList[index].getOriginalVote() >= depositSavingThreshold) ||
  @       (isElected (candidateList[index]) == true);
  @*/
public /*@ pure @*/ boolean isDepositSaved(final int index){
 	final int originalVote = candidates[index].getOriginalVote(); //@ nowarn;
	final boolean elected = isElected (candidates[index]); //@ nowarn;
	return ((originalVote >= savingThreshold)
		|| elected);
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
  @   ensures totalVotes == nonTransferableVotes +
  @     (\sum int i; 0 <= i && i < totalCandidates;
  @   candidateList[i].getTotalVote());
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
  @     requires electionParameters.candidateList != null;
  @     requires (\forall int c; 0 <= c && c < electionParameters.numberOfCandidates;
  @              electionParameters.candidateList[c] != null);
  @     requires electionParameters.numberOfCandidates <= electionParameters.candidateList.length;
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
	this.candidates = new Candidate[totalNumberOfCandidates]; //@ nowarn;
	for (int i = 0; i < totalNumberOfCandidates; i++) {
		this.candidates[i] = electionParameters.getCandidate(i); //@ nowarn;
	}
	decisions = new Decision[Decision.MAX_DECISIONS]; //@ nowarn;
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
 	ballots = new Ballot[totalNumberOfVotes]; //@ nowarn;
 	int index = 0;
 	while (index < totalNumberOfVotes && ballotBox.isNextBallot()) {
 		ballots[index++] = ballotBox.getNextBallot(); //@ nowarn;
 	}
 	status = PRECOUNT;
 	
 	// Number of first preferences for each candidate
 	calculateFirstPreferences(); //@ nowarn;
}

/**
 * Droop quota
 * 
 * @return Number of votes required to ensure election
 */
/*@ also requires 0 < numberOfSeats;
  @*/
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
		final int numberOfBallotsInPile = countBallotsFor(candidateID);
		candidates[c].addVote(numberOfBallotsInPile, countNumberValue); //@ nowarn;
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
  @     requires state == COUNTING;
  @     requires 0 < toCandidateID;
  @     requires toCandidateID != Ballot.NONTRANSFERABLE;
  @     requires ballotsToCount != null;
  @     requires (\forall int b; 0 <= b && b < totalVotes; ballotsToCount[b] != null);
  @     ensures \result== (\num_of int j; 0 <= j && j < totalVotes;
  @       (ballotsToCount[j].isAssignedTo(fromCandidate.getCandidateID())) &&
  @       (getNextContinuingPreference(ballotsToCount[j]) == toCandidateID));
  @*/
	protected /*@ pure spec_public @*/ int getPotentialTransfers(
	  final Candidate fromCandidate, final int toCandidateID) {
		int numberOfBallots = 0;
 		for (int j = 0; j < totalNumberOfVotes; j++) {
			if (ballots[j].isAssignedTo(fromCandidate.getCandidateID()) && //@ nowarn;
			    (getNextContinuingPreference(ballots[j]) == toCandidateID)) {
					numberOfBallots++;
				}
			
		}
	return numberOfBallots;
	} //@ nowarn Post;

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
		return false;
	} //@ nowarn;

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
  @   requires (state == COUNTING);
  @   requires isElected (fromCandidate) || 
  @            (fromCandidate.getStatus() == CandidateStatus.ELIMINATED);
  @   requires toCandidate.getStatus() == CandidateStatus.CONTINUING;
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
		int numberOfVotes = getPotentialTransfers (fromCandidate, 
				toCandidate.getCandidateID());
 		if (isElected(fromCandidate) && 
		    (getSurplus(fromCandidate) < getTotalTransferableVotes(
		    		fromCandidate))) {
 			 numberOfVotes *= getTransferFactor(fromCandidate);
		}

    return numberOfVotes;
	}

protected /*@ pure @*/ int getTransferFactor(
		final /*@ non_null @*/ Candidate fromCandidate) {
  return (getSurplus (fromCandidate) / 
		  getTotalTransferableVotes (fromCandidate)); //@ nowarn;
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
 * @param firstCandidate
 * The first of the candidates to be selected from
 * 
 * @param secondCandidate
 * The second of the candidates to be selected from
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
protected /*@ pure spec_public @*/ int randomSelection(
		/*@ non_null @*/ Candidate firstCandidate, 
		/*@ non_null @*/ Candidate secondCandidate) {
	
 		if (firstCandidate.randomNumber < secondCandidate.randomNumber) {
			return firstCandidate.candidateID;
		}
		return secondCandidate.candidateID; 
}

/**
 * List each ballot ID in order by random number used to show how the votes 
 * have been mixed and numbered.
 * 
 * @param ballot Ballot for which to get the order of
 * @return Order of this ballot in numbered list of ballots
 */
/*@ also
  @   protected normal_behavior 
  @     requires ballotsToCount != null && (\forall int b;
  @              0 <= b && b < totalVotes; ballotsToCount[b] != null);
  @     ensures 1 <= \result;
  @     ensures \result <= ballotsToCount.length;
  @*/
protected /*@ pure @*/ int getOrder(Ballot ballot){
    // Determine the number of ballots with a lower random number
	  int order = 1;
	  for (int b = 0; b < totalNumberOfVotes; b++) {
		  if (ballots[b].isAfter(ballot)) { //@ nowarn;
			  order++;
		  }
	  }
	  return order;
	} //@ nowarn;

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
  @       ((getActualTransfers(fromCandidate, toCandidate) *
  @       getTotalTransferableVotes (fromCandidate)) /
  @       getSurplus(fromCandidate));
  @*/
protected /*@ pure spec_public @*/ int getTransferRemainder(
          /*@ non_null @*/ Candidate fromCandidate, 
          /*@ non_null @*/ Candidate toCandidate){
  return getPotentialTransfers(fromCandidate, toCandidate.getCandidateID()) //@ nowarn;
    - ((getActualTransfers(fromCandidate, toCandidate) * //@ nowarn;
    		getTotalTransferableVotes (fromCandidate)) / getSurplus(fromCandidate)); //@ nowarn;
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
		
		return secondCandidate.isAfter(firstCandidate); //@ nowarn;
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
  @     requires toCandidate.getStatus() == election.tally.Candidate.CONTINUING;
  @     requires getSurplus(fromCandidate) < getTotalTransferableVotes(fromCandidate);
  @     ensures \result == (\num_of int i; i <= 0 && i < totalCandidates &&
  @       candidateList[i].getCandidateID() != toCandidate.getCandidateID()&&
  @       candidateList[i].getStatus() == election.tally.Candidate.CONTINUING;
  @       (getTransferRemainder(fromCandidate, candidateList[i]) >
  @       getTransferRemainder(fromCandidate, toCandidate)) ||
  @       ((getTransferRemainder(fromCandidate, candidateList[i]) ==
  @       getTransferRemainder(fromCandidate, toCandidate)) &&
  @       (getActualTransfers(fromCandidate, candidateList[i]) >
  @       getActualTransfers(fromCandidate, toCandidate))) ||
  @       ((((getTransferRemainder(fromCandidate, candidateList[i]) ==
  @       getTransferRemainder(fromCandidate, toCandidate)) &&
  @       (getActualTransfers(fromCandidate, candidateList[i]) ==
  @       getActualTransfers(fromCandidate, toCandidate)))) &&
  @       isHigherThan (candidateList[i], toCandidate)));
  @*/
protected /*@ pure spec_public @*/ int getCandidateOrderByHighestRemainder(Candidate fromCandidate, Candidate toCandidate){
	int numberHigherThan = 0;
	 
			for(int i=0; i<totalNumberOfCandidates; i++){
				if(candidates[i].getCandidateID() != toCandidate.getCandidateID()&& candidates[i].getStatus() == CandidateStatus.CONTINUING){
					if(getTransferRemainder(fromCandidate, candidates[i]) > getTransferRemainder(fromCandidate, toCandidate)){
						numberHigherThan++;
					}
					else if(getTransferRemainder(fromCandidate, candidates[i]) == getTransferRemainder(fromCandidate, toCandidate) &&	
							getActualTransfers(fromCandidate, candidates[i]) > getActualTransfers(fromCandidate, toCandidate)){
						numberHigherThan++;
					}
					else if(getTransferRemainder(fromCandidate, candidates[i]) == getTransferRemainder(fromCandidate, toCandidate) && 
							getActualTransfers(fromCandidate, candidates[i]) == getActualTransfers(fromCandidate, toCandidate) && 
							isHigherThan (candidates[i], toCandidate)){
						numberHigherThan++;
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
  @     ensures \result == (\sum int i; 0 <= i && i < totalCandidates;
  @       getPotentialTransfers (fromCandidate, 
  @       candidateList[i].getCandidateID()));
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
	  @   candidates[i].getStatus() == Candidate.CONTINUING;
	  @   candidateList[i].getTotalVote()) 
	  @   == candidateList[\result].getTotalVote();
	  @ ensures (\exists int i; 0 <= i && i < totalCandidates && 
	  @   candidates[i].getStatus() == Candidate.CONTINUING; i == \result);
	  @ ensures 0 <= \result && \result < totalCandidates;
	  @ ensures candidateList[\result] != null;
	  @*/
	public /*@ pure @*/ int findHighestCandidate() {
		
		long mostVotes = 0;
		int highestCandidate = -1;
	
		for (int i=0; i < totalNumberOfCandidates; i++) {
			if (candidates[i].getStatus() == CandidateStatus.CONTINUING) {
			  if (candidates[i].getTotalVote() > mostVotes) {
				     mostVotes = candidates[i].getTotalVote();
				     highestCandidate = i;
			} else if (candidates[i].getTotalVote() == mostVotes && 0 <= highestCandidate &&
				    isHigherThan(candidates[i],candidates[highestCandidate])) {
					   highestCandidate =  i;
			  }
			}
		}
		
		return highestCandidate;
	} //@ nowarn;

	/**
	 * Who is the lowest continuing candidate?
	 * 
	 * @return The continuing candidate with the least votes
	 */
	/*@ requires 1 <= totalCandidates;
	  @ requires \nonnullelements(candidates);
	  @ ensures (\forall int i; 
	  @   0 <= i && i < totalCandidates && candidateList[i].getStatus() == Candidate.CONTINUING;
	  @   candidateList[i].getTotalVote() >= candidateList[\result].getTotalVote());
	  @ ensures (\exists int i; 
	  @   0 <= i && i < totalCandidates && candidateList[i].getStatus() == Candidate.CONTINUING;
	  @   i == \result);
	  @*/
	public /*@ pure @*/ int findLowestCandidate() {
		
		long leastVotes = MAXVOTES;
		int index = 0; 

		for (int i=0; i < totalNumberOfCandidates; i++) {
			if (candidates[i].getStatus() == CandidateStatus.CONTINUING) {
			  if (candidates[i].getTotalVote() < leastVotes) {
				leastVotes = candidates[i].getTotalVote();
				index = i;
			  } else if (candidates[i].getTotalVote() == leastVotes &&
 				    isHigherThan(candidates[index],candidates[i])) {
					index = i;
			  }
			}
		}
		
		return index;
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
		auditDecision(Decision.EXCLUDE, candidateID);
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
	  @*/
	protected void transferBallot(/*@ non_null @*/ Ballot ballot) {
		 
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
		auditDecision(Decision.DEEM_ELECTED,candidates[winner].getCandidateID()); //@ nowarn;
		numberOfCandidatesElected++;
 		totalRemainingSeats--;
	}

	/*@ also 
	  @ requires candidates != null && (\forall int c; 0 <= c && c < totalNumberOfCandidates;
	  @          candidates[c] != null);
	  @ ensures \result == (\num_of int i; 0 <= 0 && i < totalNumberOfCandidates;
	  @         candidates[i].getStatus() == CandidateStatus.CONTINUING);
	  @*/
	protected /*@ pure spec_public @*/ int getNumberContinuing() {
		int numberContinuing = 0;
		
		for (int i = 0; i < totalNumberOfCandidates; i++) {
			if (candidates[i].getStatus() == CandidateStatus.CONTINUING) {
				numberContinuing++;
			}
		}
		
 		return numberContinuing;
	}
}