package election.tally;



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
    countStatus = new CountStatus();
    countStatus.changeState(AbstractCountStatus.NO_SEATS_FILLED_YET);
    this.numberOfSeats = 0;
    this.totalNumberOfSeats = 0;
  }
  
  
    
    /** Inner ASM */
  public /*@ non_null @*/ CountStatus countStatus;
  
  /**
   * Distribute the surplus of an elected candidate.
   * 
   * @param winner
   *          The elected candidate
   */
  /*@ also
    @   requires state == COUNTING;
    @   requires countStatus.getState() == 
    @     AbstractCountStatus.SURPLUS_AVAILABLE;
    @   requires isElected (candidateList[winner]);
    @   requires 0 <= winner && winner < candidateList.length;
    @*/
  public void distributeSurplus(final int winner) {
    final int surplus = getSurplus(candidates[winner]);
    final int totalTransferableVotes =
        getTotalTransferableVotes(candidates[winner]);
    if (0 < surplus && 0 < totalTransferableVotes) {
      countStatus.changeState(AbstractCountStatus.READY_TO_MOVE_BALLOTS);
      
      /*@ loop_invariant (0 < i) ==>
        @   (\old (countBallotsFor(candidates[winner].getCandidateID())) + 
        @     \old (countBallotsFor(candidates[i-1].getCandidateID())) ==
        @   (countBallotsFor(candidates[winner].getCandidateID()) +
        @     countBallotsFor(candidates[i-1].getCandidateID())));
        @*/
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
    if ((index != winner) &&
        (candidates[index].getStatus() == CandidateStatus.CONTINUING)) {
      final int numberOfTransfers = calculateNumberOfTransfers(winner, index);
      transferVotes(candidates[winner], candidates[index], numberOfTransfers);
    }
  }
  
  //@ requires 0 <= winner && winner < candidateList.length;
  //@ requires state == COUNTING;
  protected void removeNonTransferableBallots(final int winner,
      final int surplus, final int totalTransferableVotes) {
    if (surplus > totalTransferableVotes) {
      int numberToRemove = surplus - totalTransferableVotes;
      //@ assert 0 < numberToRemove;
      //@ assert candidateList[winner] != null;
      final int fromCandidateID = candidates[winner].getCandidateID();
      /*@ loop_invariant (0 < b) ==> 
        @   !(ballots[b-1].isAssignedTo(fromCandidateID));
        @ decreasing numberToRemove;
        @*/
      for (int b = 0; b < ballots.length; b++) {
        if ((ballots[b].isAssignedTo(fromCandidateID))
            && (0 < numberToRemove)
            && (getNextContinuingPreference(ballots[b]) == 
              Ballot.NONTRANSFERABLE)) {
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
        getActualTransfers(candidates[winner], candidates[index]);
    
    if (0 <= getTransferShortfall(candidates[winner])) {
      numberOfTransfers +=
          getRoundedFractionalValue(candidates[winner], candidates[index]);
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
    
    
    
    // Transfer the required number of ballots
    final int fromCandidateID = fromCandidate.getCandidateID();
    final int toCandidateID = toCandidate.getCandidateID();
    int ballotsMoved = 0;
    /*@ loop_invariant (0 < b) ==>
      @   ((ballotsMoved <= numberOfVotes) &&
      @   (\old(ballots[b-1].isAssignedTo(fromCandidate.getCandidateID())) ==>
      @     ballots[b-1].isAssignedTo(toCandidate.getCandidateID())));
      @*/
    for (int b = 0; b < ballots.length; b++) { 
      if ((ballots[b].getCandidateID() == fromCandidateID) && 
          (getNextContinuingPreference(ballots[b]) == toCandidateID)) {
        transferBallot(ballots[b]); 
        ballotsMoved++;
        if (ballotsMoved == numberOfVotes) {
          break;
        }
      }
    }
    
    // Update the totals for each candidate
    fromCandidate.removeVote(ballotsMoved, countNumberValue); 
    toCandidate.addVote(ballotsMoved, countNumberValue); 
    
  } 
  
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
    @   ensures state == ElectionStatus.FINISHED;
    @*/
  public void count() {
    
    // Start or else resume the counting of ballots
    if (status < ElectionStatus.COUNTING) {
      startCounting(); 
    }
    
    while (getNumberContinuing() > totalRemainingSeats && 
        0 < totalRemainingSeats && // infinite loop detected by Uilioch and fixed 2011.01.20
        countNumberValue < CountConfiguration.MAXCOUNT) {
      incrementCountNumber(); 
      
      countStatus.changeState( 
          AbstractCountStatus.MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS);
      
      // Transfer surplus votes from winning candidates
      electCandidatesWithSurplus(); 
      
      // Exclusion of lowest continuing candidates if no surplus
      excludeLowestCandidates(); 
    }
    
    // Filling of last seats
    if (getNumberContinuing() == totalRemainingSeats) { 
      fillLastSeats();
      
    }
    
    countStatus.changeState(AbstractCountStatus.END_OF_COUNT);
    status = ElectionStatus.FINISHED;
  } //@ 
  
  /**
   * Elect any candidate with a quota or more of votes.
   */
  /*@ requires state == COUNTING;
    @ assignable candidateList, ballotsToCount, candidates,
    @   numberOfCandidatesElected, totalRemainingSeats;
    @ assignable countStatus;
    @ ensures countStatus.substate == AbstractCountStatus.CANDIDATE_ELECTED ||
    @   countStatus.substate == AbstractCountStatus.SURPLUS_AVAILABLE;
    @*/
  protected void electCandidatesWithSurplus() {
    while (candidatesWithQuota()
        && countNumberValue < CountConfiguration.MAXCOUNT
        && getNumberContinuing() > totalRemainingSeats) {
      
      updateCountStatus(AbstractCountStatus.CANDIDATES_HAVE_QUOTA);
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
        updateCountStatus(AbstractCountStatus.SURPLUS_AVAILABLE);
        distributeSurplus(winner);
      }
      
    }
  }
  
  /**
   * Indicates if there are any continuing candidates with at least a quota
   * of votes; these candidates are ready to be deemed elected by quota.
   * 
   * @return <code>true</code> if there exists a continuing candidate
   *         who has quota of votes
   */
  /*@ requires PRECOUNT <= state;
    @ ensures \result == (\exists int i; 0 <= i && i < totalNumberOfCandidates;
    @   (candidates[i].getStatus() == CandidateStatus.CONTINUING)
    @   && hasQuota(candidates[i]));
    @*/
  protected/*@ pure @*/boolean candidatesWithQuota() {
    /*@ loop_invariant !(\exists int c; 0 <= c && c < i;
      @   (candidates[i].getStatus() == CandidateStatus.CONTINUING) && 
      @   hasQuota(candidates[i])); 
      @*/
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
    @ assignable countStatus.substate;
    @*/
  protected void excludeLowestCandidates() {
    while (!candidatesWithQuota()
        && getNumberContinuing() > totalRemainingSeats
        && countNumberValue < CountConfiguration.MAXCOUNT) {
      
       countStatus.changeState(AbstractCountStatus.NO_SURPLUS_AVAILABLE);  
       final int loser = findLowestCandidate();  
      
      if (loser != NONE_FOUND_YET) {
        
         countStatus.changeState(AbstractCountStatus.CANDIDATE_EXCLUDED); 
         eliminateCandidate(loser); //@ 
         countStatus.changeState(AbstractCountStatus.READY_TO_MOVE_BALLOTS); 
         redistributeBallots(candidates[loser].getCandidateID()); 
      }
      else {
        break; // Infinite loop detected by Uilioch; fixed 2011.08.03
      }
    }
   } 
  
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
    countStatus.changeState(AbstractCountStatus.LAST_SEAT_BEING_FILLED); 
    for (int c = 0; c < totalNumberOfCandidates; c++) {
      if (isContinuingCandidateID(candidates[c].getCandidateID())) {
        electCandidate(c); 
      }
    }
  }
  
  /*@ requires state == PRECOUNT;
    @ assignable state, countStatus, countStatus.substate, countNumberValue, 
    @   totalRemainingSeats, savingThreshold, numberOfCandidatesElected, 
    @   numberOfCandidatesEliminated;
    @ ensures state == COUNTING;
    @*/
  public void startCounting() {
    status = ElectionStatus.COUNTING;
    countStatus.changeState(AbstractCountStatus.NO_SEATS_FILLED_YET);
    countNumberValue = 0;
    
    totalRemainingSeats = numberOfSeats;
    savingThreshold = getDepositSavingThreshold();
    numberOfCandidatesElected = 0;
    numberOfCandidatesEliminated = 0;
  } 
  
  /**
   * Get the number of votes required in order to recoup election expenses or
   * qualify for funding in future elections.
   * 
   * @return
   */
  //@ ensures \result == 1 + (getQuota() / 4);
  public/*@ pure @*/int getDepositSavingThreshold() {
    return 1 + (getQuota() / 4);
  }
  
  /*@ requires state == COUNTING;
    @ requires countStatus.isPossibleState (countingStatus);
    @ assignable countStatus, countStatus.substate;
    @ ensures countingStatus == countStatus.getState();
    @*/
  public void updateCountStatus(final int countingStatus) {
    countStatus.changeState(countingStatus);
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
  
  //@ ensures 3*totalNumberOfCandidates + 60 <= \result.length();
  public/*@ pure non_null */String getResults() {
    final StringBuffer buffer = new StringBuffer(150);
    
    buffer.append("quota = ");
    buffer.append(Integer.toString(this.getQuota()));
    buffer.append(" threshold = ");
    buffer.append(Integer.toString(this.getDepositSavingThreshold()));
    buffer.append(' ');
    buffer.append(Integer.toString(this.countNumberValue));
    buffer.append(" rounds of counting ");
    buffer.append(Integer.toString(this.totalNumberOfCandidates));
    buffer.append(" candidates\n");
    
    //@ loop_invariant 3*index + 60 <= buffer.length();
    for (int index = 0; index < this.totalNumberOfCandidates; index++) {
      final Candidate candidate = candidates[index];
      buffer.append("(" + candidate.toString() + ") ");
      if (isDepositSaved(index)) {
        buffer.append(" reached threshold ");
      }
    }
    
    return buffer.toString();
  }
  
  //@ requires 0 <= index && index < candidates.length;
  //@ ensures \result == candidates[index]; 
  public /*@ pure @*/ Candidate getCandidate(final int index) {
    return candidates[index];
  }

  
}