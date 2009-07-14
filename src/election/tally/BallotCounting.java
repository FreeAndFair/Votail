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
 * @see <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">Formal Verification and Risk Analysis for Remote Voting Systems</a>
 *
 */
public class BallotCounting extends AbstractBallotCounting {

	/**
	 * Inner class for state machine
	 */
	public class BallotCountingMachine implements BallotCountingModel {
		
		// Initial state
		/**
		 * Inner state machine for counting of Dail election ballots.
		 */
		public BallotCountingMachine() {
			substate = READY_TO_COUNT;
		} //@ nowarn;

		//@ public invariant isPossibleState (substate);
		//@ public constraint isTransition(\old(substate), substate);
		//@ public initially substate == READY_TO_COUNT;
 		protected /*@ spec_public @*/ int substate;
 		
 		/**
 		 * Get the state of the inner automaton for counting ballots in Dail elections.
 		 * 
 		 * @return The state of the count.
 		 */
 		//@ also ensures \result == substate;
 		public /*@ pure @*/ int getState() {
			return substate;
		} //@ nowarn;

 		/**
 		 * Move along the next valid transition in state.
 		 * 
 		 * @param newState The next stage of counting.
 		 */
 		//@ also ensures newState == getState();
		public void changeState(final int newState) {
			substate = newState;
		} //@ nowarn;

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
 					(READY_TO_CALCULATE_ROUNDING_TRANSFERS == value) ||
 					(READY_TO_ALLOCATE_SURPLUS == value) ||
 					(READY_TO_ADJUST_NUMBER_OF_TRANSFERS == value) ||
 					(READY_TO_MOVE_BALLOTS == value) ||
 					(CANDIDATE_EXCLUDED == value) ||
 					(READY_FOR_NEXT_ROUND_OF_COUNTING == value) ||
 					(LAST_SEAT_BEING_FILLED == value) ||
 					(MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS == value) ||
 					(ONE_OR_MORE_SEATS_REMAINING == value) ||
 					(ALL_SEATS_FILLED == value) ||
 					(END_OF_COUNT == value) ||
 					(ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT == value));
		} //@ nowarn;
		
		/**
		 * Is this a valid transition in the counts state?
		 * @param fromState The previous status.
		 * @param toState The next status.
		 * 
		 * @return <code>true</code> if this transition exists with the automaton for counting of Dail ballots
		 */
		public /*@ pure @*/ boolean isTransition(final int fromState, final int toState) {
			
			// Self transitions are allowed
			if (toState == fromState) {
				return true;
			}
			
			// No transitions into the initial state
			else if (READY_TO_COUNT == toState) {
				return false;
			}
			
			// No transitions away from final state
			else if (END_OF_COUNT == fromState) {
				return false;
			}
			
			// Transition: Calculate Quota
			else if ((READY_TO_COUNT == fromState) && (NO_SEATS_FILLED_YET == toState)) {
				return true;
			}
			
			// Transition: Find Highest Continuing Candidate with Quota
			else if (((NO_SEATS_FILLED_YET == fromState) || 
					(CANDIDATES_HAVE_QUOTA == fromState) ||
					(MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS == fromState)) &&
				((CANDIDATE_ELECTED == toState) ||	
					(NO_SURPLUS_AVAILABLE == toState))) {
					return true;
				}
			
			// Transition: Calculate Surplus
			else if ((CANDIDATE_ELECTED == fromState) &&
			   ((CANDIDATES_HAVE_QUOTA == toState) ||
					   (SURPLUS_AVAILABLE == toState) ||
					   (NO_SURPLUS_AVAILABLE == toState))) {
				   return true;
			   }
			
			// Transition: Calculate Transfer Factor
			else if ((SURPLUS_AVAILABLE == fromState) && 
					(READY_TO_ALLOCATE_SURPLUS == toState)) {
				return true;
			}
			
			// Transition: Calculate Non-Fractional Transfers
			else if ((READY_TO_ALLOCATE_SURPLUS == fromState) &&
					(READY_TO_CALCULATE_ROUNDING_TRANSFERS == toState)) {
				return true;
			}
			
			// Transition: Calculate Fractional Differences
			else if ((READY_TO_CALCULATE_ROUNDING_TRANSFERS == fromState) &&
					(READY_TO_ADJUST_NUMBER_OF_TRANSFERS == toState)) {
				return true;
			}
			
			// Transition: Calculate Adjusted Number of Transfers
			else if ((READY_TO_ADJUST_NUMBER_OF_TRANSFERS == fromState) &&
					(READY_TO_MOVE_BALLOTS == toState)) {
				return true;
			}
			
			// Transition: Calculate Transfers
			else if ((CANDIDATE_EXCLUDED == fromState) &&
					(READY_TO_MOVE_BALLOTS == toState)) {
				return true;
			}
			
			// Transition: Move the Ballots
			else if ((READY_TO_MOVE_BALLOTS == fromState) && 
					(READY_FOR_NEXT_ROUND_OF_COUNTING == toState)) {
				return true;
			}
			
			// Transition: Select Lowest Continuing Candidates for Exclusion
			else if (((NO_SURPLUS_AVAILABLE == fromState) ||
					(LAST_SEAT_BEING_FILLED == fromState)) &&
					(CANDIDATE_EXCLUDED == toState)) {
				return true;
			}
			
			// Transition: Count Continuing Candidates
			else if ((ONE_OR_MORE_SEATS_REMAINING == fromState) &&
					((LAST_SEAT_BEING_FILLED == toState) ||
					(MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS == toState) ||
					(ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT == toState))) {
				return true;
			}
			
			// Transition: Check Remaining Seats
			else if ((READY_FOR_NEXT_ROUND_OF_COUNTING == fromState) &&
					((ONE_OR_MORE_SEATS_REMAINING == toState) ||
					(ALL_SEATS_FILLED == toState))) {
				return true;
			}
			
			// Transition: Declare Remaining Candidates Elected
			else if ((ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT == fromState) &&
					(ALL_SEATS_FILLED == toState)) {
				return true;
			}
			
			// Transition: Close the Count
			else if ((ALL_SEATS_FILLED == fromState) &&
					(END_OF_COUNT == toState)) {
				return true;
			}
			
			// No other state transitions are possible
			return false;
		} //@ nowarn;
		
	 

		public boolean isPossibleStateForFractionalBallots(final int value) {
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
					(ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT == value) ||
					(READY_TO_REWEIGHT_BALLOTS == value));
		}
	
		public boolean isTransitionForFractionalBallots(final int fromState, final int toState) {
			// Self transitions are allowed
			if (toState == fromState) {
				return true;
			}
			
			// No transitions into the initial state
			else if (READY_TO_COUNT == toState) {
				return false;
			}
			
			// No transitions away from final state
			else if (END_OF_COUNT == fromState) {
				return false;
			}
			
			// Transition: Calculate Quota
			else if ((READY_TO_COUNT == fromState) && 
					(NO_SEATS_FILLED_YET == toState)) {
				return true;
			}
			
			// Transition: Find Highest Continuing Candidate with Quota
			else if (((NO_SEATS_FILLED_YET == fromState) || 
					(CANDIDATES_HAVE_QUOTA == fromState) ||
					(MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS == fromState)) &&
				((CANDIDATE_ELECTED == toState) ||	
					(NO_SURPLUS_AVAILABLE == toState))) {
					return true;
				}
			
			// Transition: Calculate Surplus
			else if ((CANDIDATE_ELECTED == fromState) &&
			   ((CANDIDATES_HAVE_QUOTA == toState) ||
					   (SURPLUS_AVAILABLE == toState) ||
					   (NO_SURPLUS_AVAILABLE == toState))) {
				   return true;
			   }
			
			// Transition: Calculate Weight Factor
			else if ((SURPLUS_AVAILABLE == fromState) && 
					(READY_TO_REWEIGHT_BALLOTS == toState)) {
				return true;
			}
			
			// Transition: Weight and Transfer Ballots
			else if ((READY_TO_REWEIGHT_BALLOTS == fromState) &&
					(READY_FOR_NEXT_ROUND_OF_COUNTING == toState)) {
				return true;
			}
			
			// Transition: Move the Ballots
			else if ((READY_TO_MOVE_BALLOTS == fromState) && 
					(READY_FOR_NEXT_ROUND_OF_COUNTING == toState)) {
				return true;
			}
			
			// Transition: Calculate Transfers
			else if ((CANDIDATE_EXCLUDED == fromState) &&
					(READY_TO_MOVE_BALLOTS == toState)) {
				return true;
			}
			
			// Transition: Select Lowest Continuing Candidates for Exclusion
			else if (((NO_SURPLUS_AVAILABLE == fromState) ||
					(LAST_SEAT_BEING_FILLED == fromState)) &&
					(CANDIDATE_EXCLUDED == toState)) {
				return true;
			}
			
			// Transition: Count Continuing Candidates
			else if ((ONE_OR_MORE_SEATS_REMAINING == fromState) &&
					((LAST_SEAT_BEING_FILLED == toState) ||
					(MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS == toState) ||
					(ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT == toState))) {
				return true;
			}
			
			// Transition: Check Remaining Seats
			else if ((READY_FOR_NEXT_ROUND_OF_COUNTING == fromState) &&
					((ONE_OR_MORE_SEATS_REMAINING == toState) ||
					(ALL_SEATS_FILLED == toState))) {
				return true;
			}
			
			// Transition: Declare Remaining Candidates Elected
			else if ((ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT == fromState) &&
					(ALL_SEATS_FILLED == toState)) {
				return true;
			}
			
			// Transition: Close the Count
			else if ((ALL_SEATS_FILLED == fromState) &&
					(END_OF_COUNT == toState)) {
				return true;
			}
			
			// No other state transitions are possible
			return false;
		}

	
	}

	// Model of the ballot counting process
	private /*@ spec_public @*/ BallotCountingModel ballotCountingMachine;
	
	/**
	 * Default constructor.
	 */
	public BallotCounting() {
		super();
		ballotCountingMachine = new BallotCountingMachine();
	}
	 
    /**
     * Distribute the surplus of an elected Dail candidate.
     * 
     * @param w The elected Dail candidate
     */
	//@ also
	//@   requires ballotCountingMachine.getState() == BallotCountingModel.SURPLUS_AVAILABLE;
	public void distributeSurplus(final int w) {
		for (int i = 0; i < totalNumberOfCandidates; i++) {
			if (candidates[i].getStatus() == CandidateStatus.CONTINUING) {
				int numberOfTransfers = getActualTransfers (candidates[w], candidates[i]);
				if (0 < numberOfTransfers) {
					transferVotes (candidates[w], candidates[i], numberOfTransfers);
				}
			}
			
		}
		ballotCountingMachine.changeState(BallotCountingModel.READY_FOR_NEXT_ROUND_OF_COUNTING);
	}

	
	/**
	 * Transfer votes from one Dail candidate to another.
	 * 
	 * @param fromCandidate The elected or excluded candidate from which to transfer votes
	 * @param toCandidate The continuing candidate to receive the transferred votes
	 * @param numberOfVotes The number of votes to be transferred
	 */
	//@ also
	//@   requires ballotCountingMachine.getState() == BallotCountingModel.READY_TO_MOVE_BALLOTS;
	public void transferVotes(/*@ non_null @*/ Candidate fromCandidate,
			/*@ non_null @*/ Candidate toCandidate, int numberOfVotes) {
		
		// Update the totals for each candidate
		fromCandidate.removeVote(numberOfVotes, countNumberValue);
		toCandidate.addVote(numberOfVotes, countNumberValue);
		
		// Transfer the required number of ballots
		int fromCandidateID = fromCandidate.getCandidateID();
		int toCandidateID = toCandidate.getCandidateID();
		int ballotsMoved = 0;
		for (int b = 0; b < totalNumberOfVotes && ballotsMoved < numberOfVotes; b++) {
			if ((ballots[b].getCandidateID() == fromCandidateID) &&
				(ballots[b].getNextPreference(1) == toCandidateID)) {
				 
						ballots[b].transfer(countNumberValue);
						ballotsMoved++;
				 
			}
		}
		//@ assert (numberOfVotes == ballotsMoved);
	}

	 
	/**
	 * What is the Droop Quota for this electoral constituency?
	 * 
	 * @return The Droop Quota for this electoral constituency.
	 */
	//@ ensures quota == \result;
	public /*@ pure @*/ int getQuota() {
 		return numberOfVotesRequired;
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
	  @		assignable totalNumberOfContinuingCandidates;
	  @		assignable totalRemainingSeats;
	  @		assignable numberOfVotesRequired, savingThreshold;
	  @		assignable numberOfCandidatesElected;
	  @		assignable numberOfCandidatesEliminated;
	  @		assignable totalofNonTransferableVotes;
	  @		assignable numberOfSurpluses, sumOfSurpluses;
	  @     assignable totalNumberOfSurluses, totalSumOfurpluses;
	  @		assignable decisions, decisionsTaken;
	  @     ensures state == FINISHED;
	  @*/
	public void count() {
		
		// Start or else resume the counting of ballots
		if (status == PRECOUNT) {
			status = COUNTING;
			countNumberValue = 0;
			ballotCountingMachine.changeState(BallotCountingModel.NO_SEATS_FILLED_YET);
			
			// Reset all initial values if not already started or if doing a full recount
			totalNumberOfContinuingCandidates = totalNumberOfCandidates;
			totalRemainingSeats = numberOfSeats;
			numberOfVotesRequired = 1 + (totalNumberOfVotes / (1 + numberOfSeats));
			savingThreshold = 1 + ((totalNumberOfVotes / (1 + totalNumberOfSeats)) / 4);
			numberOfCandidatesElected = 0;
			numberOfCandidatesEliminated = 0;
			totalofNonTransferableVotes = 0;
		}
		
		// Recalculate number of continuing candidates
		totalNumberOfContinuingCandidates = getNumberContinuing();
		
		while (totalNumberOfContinuingCandidates > totalRemainingSeats && 
				countNumberValue < Candidate.MAXCOUNT) {
			ballotCountingMachine.changeState(
					BallotCountingModel.MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS);

			// Calculate surpluses
			calculateSurpluses();
			
			// Transfer surplus votes from winning candidates
			while (totalNumberOfSurpluses > 0 && countNumberValue < Candidate.MAXCOUNT-1) {
				ballotCountingMachine.changeState(BallotCountingModel.CANDIDATES_HAVE_QUOTA);
				int winner = findHighestCandidate();
				
				ballotCountingMachine.changeState(BallotCountingModel.CANDIDATE_ELECTED);
				electCandidate(winner);

				ballotCountingMachine.changeState(BallotCountingModel.SURPLUS_AVAILABLE);
				distributeSurplus(winner);
				calculateSurpluses();
			}
			
			// Even if no surplus then elect any candidate with a full quota
			for (int c = 0; c < totalNumberOfCandidates; c++) {
				if (hasQuota(candidates[c])) {
					ballotCountingMachine.changeState(BallotCountingModel.CANDIDATES_HAVE_QUOTA);
					electCandidate(c);
					ballotCountingMachine.changeState(BallotCountingModel.CANDIDATE_ELECTED);
				}
			}
			
			// Exclusion of lowest continuing candidate if no surplus
			if (totalNumberOfContinuingCandidates > totalRemainingSeats && 
					countNumberValue < Candidate.MAXCOUNT) {
			  ballotCountingMachine.changeState(BallotCountingModel.NO_SURPLUS_AVAILABLE);	
			  int loser = findLowestCandidate();
			
			  ballotCountingMachine.changeState(BallotCountingModel.CANDIDATE_EXCLUDED);	
			  eliminateCandidate(loser);
			  numberOfCandidatesEliminated++;
			  totalNumberOfContinuingCandidates--;
			
			  ballotCountingMachine.changeState(BallotCountingModel.READY_TO_MOVE_BALLOTS);	
			  redistributeBallots(candidates[loser].getCandidateID());
 			}
			countNumberValue++;
		}
		
		// Filling of last seats
		if (totalNumberOfContinuingCandidates == totalRemainingSeats) {
			ballotCountingMachine.changeState(BallotCountingModel.LAST_SEAT_BEING_FILLED);	
			for (int c = 0; c < totalNumberOfCandidates; c++) {
				if (isContinuingCandidateID(candidates[c].getCandidateID())) {
					electCandidate(c);
				}
			countNumberValue++;
			}
				
		}
		ballotCountingMachine.changeState(BallotCountingModel.END_OF_COUNT);	
		status = FINISHED;
	}

	//@ assignable numberOfSurpluses, sumOfSurpluses, totalNumberOfSurpluses, totalSumOfSurpluses;
	private /*@ spec_public @*/ void calculateSurpluses() {
		int numberOfSurpluses = 0;
		int sumOfSurpluses = 0;
		int surplus = 0;
	
		for (int c=0; c < totalNumberOfCandidates; c++) {
			surplus = getSurplus(candidates[c]);
			if (surplus > 0) {
				numberOfSurpluses++;
				sumOfSurpluses += numberOfSurpluses;
			}
		}
		setTotalNumberOfSurpluses(numberOfSurpluses);
		setTotalSumOfSurpluses(sumOfSurpluses);
	}

	/**
	 * Get the list of decisions taken
	 * 
	 * @return The list of decisions
	 */
	public /*@ pure @*/ StringBuffer getDecisionLog() {
		StringBuffer log = new StringBuffer();
		for (int d = 0; d < decisionsTaken; d++) {
			log.append("At count number " + decisions[d].atCountNumber);
			log.append(", candidate " + decisions[d].candidateID);
			log.append(" was " + decisions[d].toString());
			if (decisions[d].chosenByLot) {
				log.append(" by random selection");
			}
			log.append(".\n");
		}
		return log;
	}

	//@ ensures \old(countNumber) + 1 == countNumber;
	public void incrementCountNumber() {
		countNumberValue++;
		
	}

}
