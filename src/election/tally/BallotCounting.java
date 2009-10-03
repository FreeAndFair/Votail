package election.tally;

 
/**
 * Ballot counting for elections to Dail Eireann - the lower house of the Irish 
 * Parliament.
 * 
 * @author Dermot Cochran
 * @copyright 2009 Dermot Cochran
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
 * @see <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 * Formal Verification and Risk Analysis for Remote Voting Systems</a>
 *
 */
public class BallotCounting extends AbstractBallotCounting {

	/**
	 * Inner class for state machine
	 */
	public class CountStatus extends AbstractCountStatus {
		
		// Initial state
		/**
		 * Inner state machine for counting of Dail election ballots.
		 */
		public CountStatus() {
		  super();
			substate = READY_TO_COUNT;
		}

		//@ public invariant isPossibleState (substate);
		//@ public constraint isTransition(\old(substate), substate);
		//@ public initially substate == READY_TO_COUNT;
 		protected /*@ spec_public @*/ int substate;
 		
 		/**
 		 * Get the state of the inner automaton for counting ballots in Dail elections.
 		 * 
 		 * @return The state of the count.
 		 */
 		/*@ also ensures \result == substate;
 		  @
 		  @*/
 		public /*@ pure @*/ int getState() {
			return substate;
		}
 

 		/**
 		 * Move along the next valid transition in state.
 		 * 
 		 * @param newState The next stage of counting.
 		 */
 		//@ also ensures newState == getState();
		public void changeState(final int newState) {
			substate = newState;
		}

		/**
		 * Is this a valid state for the count to be in?
		 * @param value The state to be checked.
		 * 
		 * @return <code>true</code> if this state exists with the automaton for counting of Dail ballots
		 */
		public /*@ pure @*/ boolean isPossibleState(final int value) {
 			return ((READY_TO_COUNT == value) ||
 					(NO_SEATS_FILLED_YET == value) ||
 					(CANDIDATES_HAVE_QUOTA == value) ||
 					(CANDIDATE_ELECTED == value) ||
 					(NO_SURPLUS_AVAILABLE == value) ||
 					(SURPLUS_AVAILABLE == value) ||
  				(READY_TO_ALLOCATE_SURPLUS == value) ||
   				(READY_TO_MOVE_BALLOTS == value) ||
 					(CANDIDATE_EXCLUDED == value) ||
 					(READY_FOR_NEXT_ROUND_OF_COUNTING == value) ||
 					(LAST_SEAT_BEING_FILLED == value) ||
 					(MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS == value) ||
 					(ONE_OR_MORE_SEATS_REMAINING == value) ||
 					(ALL_SEATS_FILLED == value) ||
 					(END_OF_COUNT == value) ||
 					(ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT == value));
		}
	}

	// Status of the ballot counting process
	/*@ public invariant (state == COUNTING) ==> countStatus != null;
	  @*/
	public CountStatus countStatus;
	 
  /**
   * Distribute the surplus of an elected candidate.
   *
   * @param winner The elected candidate
   */
	/*@ also
	  @   requires state == COUNTING;
	  @   requires countStatus.getState() 
	  @     == AbstractCountStatus.SURPLUS_AVAILABLE;
	  @   requires isElected (candidateList[winner]);
	  @*/
	public void distributeSurplus(final int winner) {
    final int surplus = getSurplus(candidates[winner]);
    final int totalTransferableVotes = 
      getTotalTransferableVotes(candidates[winner]);
    if (0 < surplus) {
      countStatus.changeState(AbstractCountStatus.READY_TO_MOVE_BALLOTS);

      for (int i = 0; i < totalNumberOfCandidates; i++) {
        moveSurplusBallots(winner, surplus, totalTransferableVotes, i);
      }
    }
    
    // Move non-transferable part of surplus
    removeNonTransferableBallots(winner, surplus, totalTransferableVotes);

    countStatus.changeState(
      AbstractCountStatus.READY_FOR_NEXT_ROUND_OF_COUNTING);
    //@ assert getSurplus (candidateList[winner]) == 0;
	}


  protected void moveSurplusBallots(final int winner, final int surplus,
                                    final int totalTransferableVotes, final int index) {
    if ((index != winner) && 
      (candidates[index].getStatus() == CandidateStatus.CONTINUING)) {
      final int numberOfTransfers = calculateNumberOfTransfers(
        winner, surplus, totalTransferableVotes, index);
      transferVotes(candidates[winner], candidates[index], numberOfTransfers);
    }
  }


  protected void removeNonTransferableBallots(final int winner,
                                              final int surplus,
                                              final int totalTransferableVotes) {
    if (surplus > totalTransferableVotes) {
      int nonTransferables = surplus - totalTransferableVotes;
      final int fromCandidateID = candidates[winner].getCandidateID();
      for (int b = 0; b < totalNumberOfVotes; b++) {
        if ((ballots[b].getCandidateID() == fromCandidateID) &&
            (0 < nonTransferables) &&
          (getNextContinuingPreference(ballots[b]) == Ballot.NONTRANSFERABLE)) {
          transferBallot (ballots[b]);
          nonTransferables--;
        }
      }
    }
  }


  protected int calculateNumberOfTransfers(final int winner, final int surplus,
                                           final int totalTransferableVotes,
                                           final int index) {
    int numberOfTransfers = 
      getActualTransfers(candidates[winner], candidates[index]);
    
    if (surplus < totalTransferableVotes) {
      numberOfTransfers += 
        getRoundedFractionalValue(candidates[winner],candidates[index]);
    }
    return numberOfTransfers;
  }

	
	/**
	 * Transfer votes from one Dail candidate to another.
	 * 
	 * @param fromCandidate The elected or excluded candidate from which to transfer votes
	 * @param toCandidate The continuing candidate to receive the transferred votes
	 * @param numberOfVotes The number of votes to be transferred
	 */
	//@ also
	//@   requires state == COUNTING;
	//@   requires countStatus.getState() == AbstractCountStatus.READY_TO_MOVE_BALLOTS;
	public void transferVotes(final /*@ non_null @*/ Candidate fromCandidate,
			final /*@ non_null @*/ Candidate toCandidate, final int numberOfVotes) {
		
		// Update the totals for each candidate
    fromCandidate.removeVote(numberOfVotes, countNumberValue);
    toCandidate.addVote(numberOfVotes, countNumberValue);

    // Transfer the required number of ballots
    final int fromCandidateID = fromCandidate.getCandidateID();
    final int toCandidateID = toCandidate.getCandidateID();
    int ballotsMoved = 0;
    for (int b = 0; b < totalNumberOfVotes; b++) {
      if ((ballots[b].getCandidateID() == fromCandidateID) &&
        (getNextContinuingPreference(ballots[b]) == toCandidateID)) {
        transferBallot (ballots[b]);
        ballotsMoved++;
        if (ballotsMoved == numberOfVotes) {
          break;
        }
      }
    }
	}

	/**
	 * Count the ballots for this constituency using the rules of 
	 * proportional representation by single transferable vote.
	 * 
	 * @see "requirement 1, section 3, item 2, page 12"
	 */
	/*@ also
	  @     requires state == PRECOUNT || state == COUNTING;
	  @		assignable countNumberValue, ballotsToCount, candidateList[*];
	  @     assignable candidates, candidates[*];
	  @		assignable totalRemainingSeats, countStatus;
	  @		assignable savingThreshold;
	  @		assignable numberOfCandidatesElected;
	  @		assignable numberOfCandidatesEliminated;
	  @		assignable totalofNonTransferableVotes;
    @   assignable sumOfSurpluses, totalSumOfSurpluses;
	  @		assignable decisions, decisionsTaken;
	  @		assignable remainingSeats, totalRemainingSeats;
	  @     ensures state == ElectionStatus.FINISHED;
	  @*/
	public void count() {
		
		// Start or else resume the counting of ballots
		if (status < ElectionStatus.COUNTING) {
			startCounting();
		}
		
		while (getNumberContinuing() > totalRemainingSeats && 
			countNumberValue < CountConfiguration.MAXCOUNT) {
			countStatus.changeState(
				AbstractCountStatus.MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS);

			// Calculate surpluses
      calculateSurpluses();

      // Transfer surplus votes from winning candidates
      electCandidatesWithSurplus();
			
			// Exclusion of lowest continuing candidates if no surplus
      excludeLowestCandidates();
      incrementCountNumber();
    }
		
		// Filling of last seats
		if (getNumberContinuing() == totalRemainingSeats) {
			fillLastSeats();
				
		}
		countStatus.changeState(AbstractCountStatus.END_OF_COUNT);	
		status = ElectionStatus.FINISHED;
	}


  protected void electCandidatesWithSurplus() {
    while (getTotalSumOfSurpluses() > 0
           && countNumberValue < CountConfiguration.MAXCOUNT
           && getNumberContinuing() > totalRemainingSeats) {
      
      countStatus.changeState(AbstractCountStatus.CANDIDATES_HAVE_QUOTA);
      final int winner = findHighestCandidate();

      if (winner == NONE_FOUND_YET) {
        break;  // No more continuing candidates to elect
      }
      
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
      countStatus.changeState(AbstractCountStatus.SURPLUS_AVAILABLE);
      distributeSurplus(winner);
      calculateSurpluses();
    }
  }


	/*@ assignable countStatus, countNumberValue, candidates, candidateList;
	  @ assignable decisionsTaken, numberOfCandidatesEliminated;
	  @ assignable sumOfSurpluses, totalSumOfSurpluses;
	  @*/
  protected void excludeLowestCandidates() {
    while (getTotalSumOfSurpluses() == 0
        && getNumberContinuing() > totalRemainingSeats
        && countNumberValue < CountConfiguration.MAXCOUNT) {
      
      countStatus.changeState(AbstractCountStatus.NO_SURPLUS_AVAILABLE);
      final int loser = findLowestCandidate();
      
      if (loser == NONE_FOUND_YET) {
        break; // No more continuing candidates to eliminate
      }
        
      countStatus.changeState(AbstractCountStatus.CANDIDATE_EXCLUDED);
      eliminateCandidate(loser);
      countStatus.changeState(AbstractCountStatus.READY_TO_MOVE_BALLOTS);
      redistributeBallots(candidates[loser].getCandidateID());
      calculateSurpluses();
      }
  }

	/*@ assignable candidateList[*], countNumber, countNumberValue;
	  @ assignable numberOfCandidatesElected, totalRemainingSeats;
	  @ assignable candidates, decisions, decisionsTaken;
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
	  @ assignable state, countStatus, countNumberValue, totalRemainingSeats,
	  @   savingThreshold, numberOfCandidatesElected, 
	  @   numberOfCandidatesEliminated, totalofNonTransferableVotes;
	  @ ensures state == COUNTING;
	  @*/
	public void startCounting() {
    status = ElectionStatus.COUNTING;
    countNumberValue = 0;

    totalRemainingSeats = numberOfSeats;
    savingThreshold = 1 + (getQuota() / 4);
    numberOfCandidatesElected = 0;
    numberOfCandidatesEliminated = 0;
    totalofNonTransferableVotes = 0;
  }


	/**
	 * Default constructor for BallotCounting.
	 * 
	 * Creates and initialises the inner state machine for count status.
	 */
  public BallotCounting() {
    super();
    countStatus = new CountStatus();
		countStatus.changeState(AbstractCountStatus.NO_SEATS_FILLED_YET);
  }

	/*@ requires state == COUNTING && countStatus != null;
	  @ assignable countStatus;
	  @*/
	public void updateCountStatus(final int countingStatus) {
		countStatus.changeState(countingStatus);
	}

	/**
	 * Recalculate the number of surplus votes available for transfer.
	 */
	//@ assignable sumOfSurpluses, totalSumOfSurpluses;
  public void calculateSurpluses() {
    int sumOfSurpluses = 0;

    for (int c = 0; c < totalNumberOfCandidates; c++) {
      final int surplus = getSurplus(candidates[c]);
      if (surplus > 0) {
        sumOfSurpluses += surplus;
      }
    }
    setTotalSumOfSurpluses(sumOfSurpluses);
  }

	//@ assignable countNumberValue;
	//@ ensures \old(countNumberValue) + 1 == countNumberValue;
	public void incrementCountNumber() {
		countNumberValue++;		
	}

	//@ ensures totalRemainingSeats == \result;
  public /*@ pure @*/ int getRemainingSeats() {
    return totalRemainingSeats;
  }

  //@ ensures getNumberContinuing() == \result;
  public /*@ pure @*/ int getContinuingCandidates() {
    return getNumberContinuing();
  }

}
