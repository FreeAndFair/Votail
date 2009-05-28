package election.tally.dail;

import election.tally.AbstractBallotCounting;
import election.tally.BallotCountingModel;
import election.tally.Candidate;
 
/**
 * Ballot counting for elections to D‡il ƒireann - the lower house of the Irish 
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
 */
public class DailBallotCounting extends AbstractBallotCounting {

	/**
	 * Inner class for state machine
	 */
	public class BallotCountingMachine implements BallotCountingModel {
		
		// Initial state
		public BallotCountingMachine() {
			state = READY_TO_COUNT;
		}

		//@ public invariant isPossibleState (state);
		//@ public constraint isTransition(\old(state), state);
 		private /*@ spec_public @*/ int state;
 		
 		/**
 		 * Get the state of the inner automaton for counting ballots in Dail elections.
 		 * 
 		 * @return The state of the count.
 		 */
 		//@ also ensures \result == state;
 		public int getState() {
			return state;
		}

 		/**
 		 * Move along the next valid transition in state.
 		 */
 		//@ also ensures newState == state;
		public void changeState(final int newState) {
			state = newState;
		}

		/**
		 * Is this a valid state for the count to be in?
		 * 
		 * @return <code>true</code> if this state exists with the automaton for counting of Dail ballots
		 */
		public boolean isPossibleState(final int value) {
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
		}
		
		/**
		 * Is this a valid transition in the counts state?
		 * 
		 * @return <code>true</code> if this transition exists with the automaton for counting of Dail ballots
		 */
		public boolean isTransition(final int fromState, final int toState) {
			
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
		}
		
	}



	private BallotCountingModel ballotCountingMachine;

	 
    /**
     * Distribute the surplus of an elected Dail candidate.
     * 
     * @param candidate The elected Dail candidate
     */
	//@ also
	//@ requires ballotCountingMachine.getState() == BallotCountingModel.SURPLUS_AVAILABLE;
	public void distributeSurplus(/*@ non_null @*/ final Candidate candidate) {
		for (int i = 0; i < totalNumberOfCandidates; i++) {
			if (candidates[i].getStatus() == Candidate.CONTINUING) {
				int numberOfTransfers = getActualTransfers (candidate, candidates[i]);
				if (0 < numberOfTransfers) {
					transferVotes (candidate, candidates[i], numberOfTransfers);
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
		assert (numberOfVotes == ballotsMoved);
	}

	 
	/**
	 * What is the Droop Quota for this electoral constituency?
	 * 
	 * @return The Droop Quota for this electoral constituency.
	 */
	//@ requires 0 < numberOfSeats;
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
	  @   normal public_behavior
	  @     requires state == PRECOUNT;
	  @     ensures state == FINISHED;
	  @*/
	public void count() {
		
		status = COUNTING;
		countNumberValue = 0;
		
		while (totalNumberOfContinuingCandidates > totalRemainingSeats) {
			ballotCountingMachine.changeState(BallotCountingModel.MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS);

		
			// Transfer surplus votes from winning candidates
			while (totalNumberOfSurpluses > 0) {
				ballotCountingMachine.changeState(BallotCountingModel.CANDIDATES_HAVE_QUOTA);
				Candidate winner = findHighestCandidate();
				
				ballotCountingMachine.changeState(BallotCountingModel.CANDIDATE_ELECTED);
				winner.declareElected();

				ballotCountingMachine.changeState(BallotCountingModel.SURPLUS_AVAILABLE);
				distributeSurplus(winner);
				countNumberValue++;
			}
			
			// Exclusion of lowest continuing candidate
			ballotCountingMachine.changeState(BallotCountingModel.NO_SURPLUS_AVAILABLE);	
			Candidate loser = findLowestCandidate();
			
			ballotCountingMachine.changeState(BallotCountingModel.CANDIDATE_EXCLUDED);	
			loser.declareEliminated();
			
			ballotCountingMachine.changeState(BallotCountingModel.READY_TO_MOVE_BALLOTS);	
			redistributeBallots(loser.getCandidateID());
			countNumberValue++;
		}
		
		// Filling of last seats
		if (totalNumberOfContinuingCandidates == totalRemainingSeats) {
			ballotCountingMachine.changeState(BallotCountingModel.LAST_SEAT_BEING_FILLED);	
			for (int c = 0; c < totalNumberOfCandidates; c++) {
				if (isContinuingCandidateID(candidates[c].getCandidateID())) {
					candidates[c].declareElected();
				}
			countNumberValue++;
			}
				
		}
		ballotCountingMachine.changeState(BallotCountingModel.END_OF_COUNT);	
		status = FINISHED;
	}

}
