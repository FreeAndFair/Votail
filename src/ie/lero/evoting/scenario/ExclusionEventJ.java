package ie.lero.evoting.scenario;

import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.CandidateStatus;
import election.tally.Election;
import election.tally.mock.MockBallot;

/**
 * This is a test for the correctness of the ballot counting process in the 
 * event that the lowest continuing candidate is excluded from election.
 * 
 * @author <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 * Dermot Cochran</a>
 * 
 * @see election.tally.Candidate
 */
public class ExclusionEventJ extends AbstractEvent {

	/**
	 * Execute this scenario.
	 */
	//@ requires ballotCounting != null;
	public final void testExclusion() {
	 	
	 	final int lowestCandidate = ballotCounting.findLowestCandidate();
		ballotCounting.eliminateCandidate(lowestCandidate);
	 	
	 	//@ assert 0 == ballotCounting.report().getNumberElected();
		//@ assert 1 == ballotCounting.report().getTotalNumberOfCounts();
 	}

	/**
	 * Create test data for a mock election.
	 */
	public ExclusionEventJ() {
		
		ballotBox = new BallotBox();
		ballotCounting = new BallotCounting();
		parameters = new Election();
		parameters.totalNumberOfSeats = 4;
		parameters.numberOfSeatsInThisElection = 4;
		
		// Generate candidates
		int numberOfCandidates = 2 + parameters.numberOfSeatsInThisElection;
		Candidate[] candidates = new Candidate[numberOfCandidates];
		for (int i = 0; i < numberOfCandidates; i++) {
			candidates[i] = new Candidate();
			assertTrue (candidates[i].getStatus() == CandidateStatus.CONTINUING);
			int numberOfVotes = i*1000;
			candidates[i].addVote(numberOfVotes, 1);
			
			// Generate first preference ballots
			for (int b = 0; b < numberOfVotes; b++) {
				
				MockBallot ballot = new MockBallot();
			    ballot.setFirstPreference(candidates[i].getCandidateID());
				ballotBox.accept(ballot);
			}
		}
		
		parameters.setCandidateList(candidates);
 	 	ballotCounting.setup(parameters);
 	 	ballotCounting.load(ballotBox);
	}
}
