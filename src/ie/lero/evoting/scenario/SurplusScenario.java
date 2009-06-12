package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;

/**
 * @author Dermot Cochran
 * @copyright 2009 Dermot Cochran
 */
public class SurplusScenario extends TestCase{
	
	protected BallotCounting ballotCounting;
	protected Election parameters;
	protected Candidate candidate;
	protected BallotBox ballotBox;
	
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

		int numberOfVotes = 10000;
		candidates[0].addVote(numberOfVotes, 0);
		
		// Generate first preference ballots to match
		for (int b = 0; b < numberOfVotes && ballotBox.size() < Ballot.MAX_BALLOTS; b++) {
				Ballot testBallot = new Ballot();
				testBallot.setMultiplePreferences(candidateIDList,numberOfPreferences);
				ballotBox.accept(testBallot);
			
		}
	 	parameters.setCandidateList(candidates);
	}
	 
	/**
	 * Test the distribution of surplus ballots
	 */
	public void testDistributionOfSurplus() {
	 
	 	ballotCounting.setup(parameters);
	 	ballotCounting.load(ballotBox);
 	 	
 	 	System.out.println("Quota: " + ballotCounting.getQuota() + "\n");
	 	
	 	// Find and distribute the first surplus
	 	int c = ballotCounting.findHighestCandidate();
 		ballotCounting.electCandidate(c);

 	 	ballotCounting.distributeSurplus(c);
 	 	
	 	//@ assert 1 == ballotCounting.report().getNumberElected();
		//@ assert ballotCounting.report().hasSavedDeposit(candidate1.getCandidateID());
		//@ assert ballotCounting.report().isElected(candidate2.getCandidateID());
		//@ assert 1 == ballotCounting.report().getTotalNumberofCounts();
	}
}
