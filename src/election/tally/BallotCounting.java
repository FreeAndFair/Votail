package election.tally;

import java.util.logging.Logger;

/**
 * Ballot counting for elections to Dail Eireann - the lower house of the Irish
 * Parliament.
 * 
 * @author Dermot Cochran Permission is hereby granted, free of charge, to any
 *         person obtaining a copy of this software and associated documentation
 *         files (the "Software"), to deal in the Software without restriction,
 *         including without limitation the rights to use, copy, modify, merge,
 *         publish, distribute, sublicense, and/or sell copies of the Software,
 *         and to permit persons to whom the Software is furnished to do so,
 *         subject to the following conditions: The above copyright notice and
 *         this permission notice shall be included in all copies or substantial
 *         portions of the Software. THE SOFTWARE IS PROVIDED "AS IS", WITHOUT
 *         WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
 *         TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR
 *         PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 *         COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 *         LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
 *         ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 *         OTHER DEALINGS IN THE SOFTWARE. This work was supported, in part, by
 *         Science Foundation Ireland grant 03/CE2/I303_1 to Lero - the Irish
 *         Software Engineering Research Centre (www.lero.ie) and, in part, by
 *         the European Project Mobius IST 15909 within the IST 6th Framework,
 *         and in part by the IT University of Copenhagen.
 *         This software reflects only the authors' views and the European
 *         Community is not liable for any use that may be made of the
 *         information contained therein.
 * @see <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 *      Formal Verification and Risk Analysis for Remote Voting Systems</a>
 */
public class BallotCounting extends AbstractBallotCounting {
  
  /**
   * Default constructor for BallotCounting. Creates and initialises the inner
   * state machine for count status.
   */
  public BallotCounting() {
    super();
    // TODO 2009.10.14 ESC invariant warning
    countStatus = new CountStatus(); //@ nowarn;
    countStatus.changeState(AbstractCountStatus.NO_SEATS_FILLED_YET);
    // TODO 2009.10.14 ESC postcondition warning
  }
  
  /**
   * Inner class for state machine
   */
  public class CountStatus extends AbstractCountStatus {
    
    // Initial state
    /**
     * Inner state machine for counting of Dail election ballots.
     */
    //@ ensures READY_TO_COUNT == this.substate;
    public CountStatus() {
      this.substate = READY_TO_COUNT;
    }
    
    protected/*@ spec_public @*/int substate;
    
    /**
     * Get the state of the inner automaton for counting ballots in Dail
     * elections.
     * 
     * @return The state of the count.
     */
    /*@ also ensures \result == substate;
      @*/
    public/*@ pure @*/int getState() {
      return this.substate;
    }
    
    /**
     * Move along the next valid transition in state.
     * 
     * @param newState
     *          The next stage of counting.
     */
    //@ also assignable substate;
    //@ ensures newState == getState();
    public void changeState(final int newState) {
      substate = newState;
    }
    
    /**
     * Is this a valid state for the count to be in?
     * 
     * @param value
     *          The state to be checked.
     * @return <code>true</code> if this stage exists with the automaton for
     *         counting of Dail ballots
     */
    public/*@ pure @*/boolean isPossibleState(final int value) {
      return ((READY_TO_COUNT == value) || (NO_SEATS_FILLED_YET == value)
          || (CANDIDATES_HAVE_QUOTA == value) || (CANDIDATE_ELECTED == value)
          || (NO_SURPLUS_AVAILABLE == value) || (SURPLUS_AVAILABLE == value)
          || (READY_TO_ALLOCATE_SURPLUS == value)
          || (READY_TO_MOVE_BALLOTS == value) || (CANDIDATE_EXCLUDED == value)
          || (READY_FOR_NEXT_ROUND_OF_COUNTING == value)
          || (LAST_SEAT_BEING_FILLED == value)
          || (MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS == value)
          || (ONE_OR_MORE_SEATS_REMAINING == value)
          || (ALL_SEATS_FILLED == value) || (END_OF_COUNT == value) || (ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT == value));
    }
  }
  
  // Status of the ballot counting process
  public CountStatus countStatus;
  
  protected/*@ spec_public @*/Logger logger;
  
  /**
   * Distribute the surplus of an elected candidate.
   * 
   * @param winner
   *          The elected candidate
   */
  /*@ also
    @   requires state == COUNTING;
    @   requires countStatus.getState() == AbstractCountStatus.SURPLUS_AVAILABLE;
    @   requires isElected (candidateList[winner]);
    @   requires \nonnullelements (candidateList);
    @   requires 0 <= winner && winner < candidateList.length;
    @*/
  public void distributeSurplus(final int winner) {
    //@ assert candidateList[winner] != null;
    final int surplus = getSurplus(candidates[winner]);
    final int totalTransferableVotes =
        getTotalTransferableVotes(candidates[winner]);
    if (0 < surplus && 0 < totalTransferableVotes) {
      countStatus.changeState(AbstractCountStatus.READY_TO_MOVE_BALLOTS);
      
      for (int i = 0; i < totalNumberOfCandidates; i++) {
        moveSurplusBallots(winner, i);
      }
      // Move non-transferable part of surplus
      removeNonTransferableBallots(winner, surplus, totalTransferableVotes);
    }
    
    countStatus
        .changeState(AbstractCountStatus.READY_FOR_NEXT_ROUND_OF_COUNTING);
    //@ assert getSurplus (candidateList[winner]) == 0;
  }
  
  /**
   * Move surplus ballots from a winner's stack to another continuing candidate.
   * 
   * @param winner
   * @param index
   */
  //@ requires 0 <= index && index < candidateList.length;
  //@ requires 0 <= winner && winner < candidateList.length;
  //@ requires \nonnullelements (candidateList);
  protected void moveSurplusBallots(final int winner, final int index) {
    //@ assert candidateList[index] != null;
    if ((index != winner) &&
    // TODO 2009.10.15 JML null reference warning
        (candidates[index].getStatus() == CandidateStatus.CONTINUING)) {
      final int numberOfTransfers = calculateNumberOfTransfers(winner, index);
      // TODO 2009.10.15 ESC precondition warning
      transferVotes(candidates[winner], candidates[index], numberOfTransfers); //@ nowarn;
    }
  }
  
  //@ requires 0 <= winner && winner < candidateList.length;
  //@ requires \nonnullelements (candidateList);
  //@ requires \nonnullelements (ballotsToCount);
  protected void removeNonTransferableBallots(final int winner,
      final int surplus, final int totalTransferableVotes) {
    if (surplus > totalTransferableVotes) {
      int numberToRemove = surplus - totalTransferableVotes;
      //@ assert 0 < numberToRemove;
      //@ assert candidateList[winner] != null;
      final int fromCandidateID = candidates[winner].getCandidateID();
      for (int b = 0; b < ballots.length; b++) {
        //@ assert ballotsToCount[b] != null;
        if ((ballots[b].isAssignedTo(fromCandidateID))
            && (0 < numberToRemove)
            && (getNextContinuingPreference(ballots[b]) == Ballot.NONTRANSFERABLE)) {
          transferBallot(ballots[b]);
          numberToRemove--;
        }
      }
    }
  }
  
  //@ requires 0 <= index && index < candidateList.length;
  //@ requires 0 <= winner && winner < candidateList.length;
  //@ requires \nonnullelements (candidateList);
  protected int calculateNumberOfTransfers(final int winner, final int index) {
    int numberOfTransfers =
    // TODO 2009.10.15 JML null dereference warning
        // TODO 2009.10.15 ESC precondition warning
        getActualTransfers(candidates[winner], candidates[index]); //@ nowarn;
    
    // TODO 2009.10.15 ESC precondition warning
    if (0 <= getTransferShortfall(candidates[winner])) { //@ nowarn;
      numberOfTransfers +=
      // TODO 2009.10.15 ESC precondition warning
          getRoundedFractionalValue(candidates[winner], candidates[index]); //@ nowarn;
    }
    return numberOfTransfers;
  }
  
  /**
   * Transfer votes from one Dail candidate to another.
   * 
   * @param fromCandidate
   *          The elected or excluded candidate from which to transfer votes
   * @param toCandidate
   *          The continuing candidate to receive the transferred votes
   * @param numberOfVotes
   *          The number of votes to be transferred
   */
  //@ also
  //@   requires state == COUNTING;
  //@   requires countStatus.getState() == AbstractCountStatus.READY_TO_MOVE_BALLOTS;
  public void transferVotes(final/*@ non_null @*/Candidate fromCandidate,
      final/*@ non_null @*/Candidate toCandidate, final int numberOfVotes) {
    
    // Update the totals for each candidate
    // TODO 2009.10.15 ESC precondition warning
    fromCandidate.removeVote(numberOfVotes, countNumberValue); //@ nowarn;
    // TODO 2009.10.15 ESC precondition warning
    toCandidate.addVote(numberOfVotes, countNumberValue); //@ nowarn;
    
    // Transfer the required number of ballots
    final int fromCandidateID = fromCandidate.getCandidateID();
    final int toCandidateID = toCandidate.getCandidateID();
    int ballotsMoved = 0;
    // TODO 2009.10.15 ESC null dereference warning
    for (int b = 0; b < ballots.length; b++) { //@ nowarn;
      // TODO 2009.10.15 ESC null dereference warning 
      if ((ballots[b].getCandidateID() == fromCandidateID) && //@ nowarn;
          (getNextContinuingPreference(ballots[b]) == toCandidateID)) {
        // TODO 2009.10.15 ESC assignable warning
        transferBallot(ballots[b]); //@ nowarn;
        ballotsMoved++;
        if (ballotsMoved == numberOfVotes) {
          break;
        }
      }
    }
    // TODO 2009.10.15 ESC warning
  } //@ nowarn Post;
  
  /**
   * Count the ballots for this constituency using the rules of proportional
   * representation by single transferable vote.
   * 
   * @see "requirement 1, section 3, item 2, page 12"
   */
  /*@ also
    @   requires state == PRECOUNT || state == COUNTING;
    @   requires \nonnullelements (candidateList);
    @		assignable countNumberValue, ballotsToCount, candidateList[*];
    @   assignable candidates, candidates[*];
    @		assignable totalRemainingSeats, countStatus;
    @		assignable savingThreshold, ballots, ballotsToCount;
    @		assignable numberOfCandidatesElected;
    @		assignable numberOfCandidatesEliminated;
    @		assignable status, countStatus;
    @		assignable remainingSeats, totalRemainingSeats;
    @   assignable candidateList;
    @   assignable logger;
    @   ensures state == ElectionStatus.FINISHED;
    @*/
  public void count() {
    
    // Start or else resume the counting of ballots
    if (status < ElectionStatus.COUNTING) {
      // TODO 2009.10.14 ESC warning
      startCounting(); //@ nowarn;
    }
    
    // TODO 2009.10.15 ESC invariant warning
    while (getNumberContinuing() > totalRemainingSeats && //@ nowarn;
        0 < totalRemainingSeats && // infinite loop detected 2011.01.20
        countNumberValue < CountConfiguration.MAXCOUNT) {
      incrementCountNumber(); //@ nowarn;
      
      // TODO 2009.10.15 ESC assignable warning
      countStatus.changeState( //@ nowarn;
          AbstractCountStatus.MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS);
      
      // Transfer surplus votes from winning candidates
      // TODO 2009.10.15 ESC precondition warning
      logger.info("Total surplus votes: " + getTotalSumOfSurpluses());
      electCandidatesWithSurplus(); //@ nowarn;
      
      // Exclusion of lowest continuing candidates if no surplus
      // TODO 2009.10.15 ESC precondition warning
      excludeLowestCandidates(); //@ nowarn;
      // TODO 2009.10.15 ESC invariant warning
    }
    
    // Filling of last seats
    // TODO 2009.10.15 ESC warnings
    if (getNumberContinuing() == totalRemainingSeats) { //@ nowarn Invariant ;
      fillLastSeats(); //@ nowarn;
      
    }
    
    // TODO 2009.10.16 ESC assignable warning
    countStatus.changeState(AbstractCountStatus.END_OF_COUNT); //@ nowarn Modifies ;
    status = ElectionStatus.FINISHED;
    // TODO 2009.10.16 ESC postcondition warning
  } //@ nowarn;
  
  /**
   * Elect any candidate with a quota or more of votes.
   */
  /*@ assignable candidateList, ballotsToCount, candidates,
    @   numberOfCandidatesElected, totalRemainingSeats;
    @*/
  protected void electCandidatesWithSurplus() {
    while (candidatesWithQuota()
        && countNumberValue < CountConfiguration.MAXCOUNT
        && getNumberContinuing() > totalRemainingSeats) {
      
      countStatus.changeState(AbstractCountStatus.CANDIDATES_HAVE_QUOTA);
      final int winner = findHighestCandidate();
      
      // Elect highest continuing candidate
      updateCountStatus(AbstractCountStatus.CANDIDATE_ELECTED);
      //@ assert 0 <= winner && winner < totalCandidates;
      //@ assert candidateList[winner].getStatus() == Candidate.CONTINUING;
      //@ assert numberElected < seats;
      //@ assert 0 < remainingSeats;
      /*@ assert (hasQuota(candidateList[winner])) 
        @   || (winner == findHighestCandidate())
        @   || (getNumberContinuing() == totalRemainingSeats);
        @*/
      electCandidate(winner);
      if (0 < getSurplus(candidates[winner])) {
        countStatus.changeState(AbstractCountStatus.SURPLUS_AVAILABLE);
        distributeSurplus(winner);
      }
      
    }
  }
  
  /**
   * @return <code>true</code> if there is at least one continuing candidate
   *         with a quota of votes
   */
  protected/*@ pure @*/boolean candidatesWithQuota() {
    for (int i = 0; i < totalNumberOfCandidates; i++) {
      if ((candidates[i].getStatus() == CandidateStatus.CONTINUING)
          && hasQuota(candidates[i])) {
        return true;
      }
    }
    return false;
  }
  
  /*@ requires \nonnullelements (candidateList);
    @ assignable countStatus, countNumberValue, candidates, candidateList;
    @ assignable numberOfCandidatesEliminated, ballots, ballotsToCount;
    @*/
  protected void excludeLowestCandidates() {
    while (!candidatesWithQuota()
        && getNumberContinuing() > totalRemainingSeats
        && countNumberValue < CountConfiguration.MAXCOUNT) {
      
      // TODO 2009.10.14 ESC assignable warning
      countStatus.changeState(AbstractCountStatus.NO_SURPLUS_AVAILABLE); //@ nowarn;
      // TODO 2009.10.15 ESC precondition warning
      final int loser = findLowestCandidate(); //@ nowarn;
      
      if (loser != NONE_FOUND_YET) {
        
        // TODO 2009.10.15 ESC precondition warning
        countStatus.changeState(AbstractCountStatus.CANDIDATE_EXCLUDED); //@ nowarn;
        // TODO 2009.10.15 ESC precondition warning
        eliminateCandidate(loser); //@ nowarn;
        // TODO 2009.10.15 ESC assignable warning
        countStatus.changeState(AbstractCountStatus.READY_TO_MOVE_BALLOTS); //@ nowarn;
        // TODO 2009.10.15 ESC null warning
        redistributeBallots(candidates[loser].getCandidateID()); //@ nowarn;
      }
    }
    // TODO 2009.10.15 ESC warnings
  } //@ nowarn;
  
  /**
   * As the number of remaining seats equals the number of continuing
   * candidates, all continuing candidates are deemed to be elected without
   * reaching the quota.
   */
  /*@ requires candidateList != null;
    @ requires \nonnullelements (candidateList);
    @ requires getContinuingCandidates() == totalRemainingSeats;
    @ requires countStatus != null;
    @ assignable candidateList[*], countNumber, countNumberValue;
    @ assignable numberOfCandidatesElected, totalRemainingSeats;
    @ assignable candidates;
    @ ensures 0 == totalRemainingSeats;
    @*/
  protected void fillLastSeats() {
    // TODO 2009.10.14 ESC assignable warning
    countStatus.changeState(AbstractCountStatus.LAST_SEAT_BEING_FILLED); // @ nowarn;
    for (int c = 0; c < totalNumberOfCandidates; c++) {
      if (isContinuingCandidateID(candidates[c].getCandidateID())) {
        // TODO 2009.10.15 ESC precondition warning
        electCandidate(c); // @ nowarn;
      }
    }
  }
  
  /*@ requires state == PRECOUNT;
    @ assignable state, countStatus, countNumberValue, totalRemainingSeats,
    @   savingThreshold, numberOfCandidatesElected, numberOfCandidatesEliminated;
    @ assignable logger;
    @ ensures state == COUNTING;
    @ ensures logger != null;
    @*/
  public void startCounting() {
    logger = Logger.getLogger("election.tally.BallotCounting");
    status = ElectionStatus.COUNTING;
    countStatus.changeState(AbstractCountStatus.NO_SEATS_FILLED_YET);
    countNumberValue = 0;
    
    totalRemainingSeats = numberOfSeats;
    // TODO 2009.10.14 ESC invariant warning
    savingThreshold = getDepositSavingThreshold(); // @ nowarn;
    numberOfCandidatesElected = 0;
    numberOfCandidatesEliminated = 0;
    // TODO 2009.10.14 ESC postcondition warning
  } // @ nowarn;
  
  /**
   * Get the number of votes required in order to recoup election expenses or
   * qualify for funding in future elections.
   * 
   * @return
   */
  public/*@ pure @*/int getDepositSavingThreshold() {
    return 1 + (getQuota() / 4);
  }
  
  /*@ requires state == COUNTING && countStatus != null;
    @ assignable countStatus.substate;
    @*/
  public void updateCountStatus(final int countingStatus) {
    // TODO 2009.10.14 ESC assignable warning
    countStatus.changeState(countingStatus); //@ nowarn;
  }
  
  //@ assignable countNumberValue;
  //@ ensures \old(countNumberValue) + 1 == countNumberValue;
  public void incrementCountNumber() {
    countNumberValue++;
  }
  
  /*@ ensures totalRemainingSeats == \result;
    @
    @ public model pure int getRemainingSeats() {
    @   return totalRemainingSeats;
    @ }
    @*/
  
  
  /*@ ensures getNumberContinuing() == \result;
    @
    @ public model pure int getContinuingCandidates() {
    @   return getNumberContinuing();
    @ }
    @*/
  
  /**
   * Return the status of the count
   * 
   * @return The status of the count
   */
  //@ requires countStatus != null;
  //@ ensures \result == countStatus;
  public/*@ pure @*/AbstractCountStatus getCountStatus() {
    return countStatus;
  }
  
  public/*@ pure*/String getResults() {
    StringBuffer buffer = new StringBuffer();
    
    buffer.append("quota = " + this.getQuota());
    buffer.append(" threshold = " + this.getSavingThreshold() + "\n");
    buffer.append(this.countNumberValue + " rounds of counting ");
    buffer.append(this.totalNumberOfCandidates + " candidates\n");
    
    for (int index = 0; index < this.totalNumberOfCandidates; index++) {
      final Candidate candidate = candidates[index];
      buffer.append("(" + candidate.toString() + ") ");
      if (isDepositSaved(index)) {
        buffer.append(" saved deposit ");
      }
    }
    
    return buffer.toString();
  }
  
  /**
   * Get the number of rounds of counting so far.
   * <p>
   * A new round of counting happens after each transferal of votes by
   * distribution of surpluses or elimination of lowest candidates.
   * </p>
   * 
   * @return The number of rounds of counting so far.
   */
  //@ ensures \result == this.countNumberValue;
  public/*@ pure @*/int getNumberOfRounds() {
    return this.countNumberValue;
  }
  
  public Candidate getCandidate(int i) {
    return candidates[i];
  }
}