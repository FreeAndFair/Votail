package ie.lero.evoting.scenario;

import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;
import election.tally.mock.MockBallot;

/**
 * @author <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 * Dermot Cochran</a>
 */
public class SurplusCalculationEventC extends VotailEventTestCase{
	
	/**
	 * Create the scenario data needed
	 */
	protected void setUp() {
		ballotCounting = new BallotCounting();
		ballotBox = new BallotBox();
		parameters = new Election();
		parameters.totalNumberOfSeats = 2;
		parameters.numberOfSeatsInThisElection = parameters.totalNumberOfSeats;
		parameters.numberOfCandidates = 3;
		
		// Generate sample candidates
	 	Candidate[] candidates = new Candidate[parameters.numberOfCandidates];
	 	int[] candidateIDList = new int[parameters.numberOfCandidates];
	 	int numberOfPreferences = parameters.numberOfCandidates;
	 	
		for (int i = 0; i < parameters.numberOfCandidates; i++) {
			candidates[i] = new Candidate();
  			candidateIDList[i] = candidates[i].getCandidateID();
		}

		final int numberOfVotes = 10000;
		candidates[0].addVote(numberOfVotes, 0);
		
		for (int b = 0; b < numberOfVotes && 
		        ballotBox.size() < Ballot.MAX_BALLOTS; b++) {
				MockBallot testBallot = new MockBallot();
				testBallot.setMultiplePreferences(
						candidateIDList,numberOfPreferences);
				ballotBox.accept(testBallot);
			
		}
	 	parameters.setCandidateList(candidates);
	}
	 
	/**
	 * Test the distribution of surplus ballots.
	 */
	public void testDistributionOfSurplus() {
	 
	 	ballotCounting.setup(parameters);
	 	ballotCounting.load(ballotBox);
 	 	//@ assert 3334 == ballotCounting.getQuota();
	 	
	 	// Find and distribute the first surplus
	 	final int indexOfHighestCandidate = ballotCounting.findHighestCandidate();
	 	//@ assert 0 <= indexOfHighestCandidate;
	 	
 		ballotCounting.electCandidate(indexOfHighestCandidate);
 	 	ballotCounting.distributeSurplus(indexOfHighestCandidate);
 	 	
	 	//@ assert 1 == ballotCounting.report().getNumberElected();
		//@ assert 1 == ballotCounting.report().getTotalNumberOfCounts();
	}
}
