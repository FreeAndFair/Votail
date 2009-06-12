package ie.lero.evoting.scenario;

import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;
import election.tally.Report;

/**
 * @author Dermot Cochran
 * @copyright 2009 Dermot Cochran
 */
public class SurplusScenario {
	
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
	 	System.out.println("Generated " + ballotBox.size() + " ballot papers for " +
	 			parameters.numberOfCandidates + " candidates.");
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
 	 	ballotCounting.incrementCountNumber();
	 	Report report = ballotCounting.report();
	 	//@ assert 0 < report.getNumberElected();
	 	
	 	// Declare the results
	 	System.out.println(report.getResults());
	 	System.out.println(ballotCounting.getDecisionLog());
	}
	
	/**
	 * Election of the highest candidate and distribution of their surplus ballots.
	 * 
	 * @param args Optional parameters to use when running this scenario
	 */
	public static void main(String[] args) {
		SurplusScenario scenario = new SurplusScenario();
		scenario.setUp();
		scenario.testDistributionOfSurplus();
	}
}
