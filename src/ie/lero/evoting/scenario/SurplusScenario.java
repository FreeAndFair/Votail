package ie.lero.evoting.scenario;

import scenario.util.TestBallot;
import election.tally.Ballot;
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
	protected scenario.util.TestBallotBox ballotBox;
	
	/**
	 * Create the scenario data needed
	 */
	protected void setUp() {
		ballotCounting = new BallotCounting();
		ballotBox = new scenario.util.TestBallotBox();
		parameters = new Election();
		parameters.totalNumberOfSeats = 5;
		parameters.numberOfSeatsInThisElection = parameters.totalNumberOfSeats;
		parameters.numberOfCandidates = Candidate.MAX_CANDIDATES / 2;
		
		// Generate sample candidates
	 	Candidate[] candidates = new Candidate[parameters.numberOfCandidates];
	 	int[] candidateIDList = new int[parameters.numberOfCandidates];
	 	int numberOfPreferences = 1;
	 	
		for (int i = 0; i < parameters.numberOfCandidates; i++) {
			candidates[i] = new Candidate();
			int numberOfVotes = 10*i+100;
			candidates[i].addVote(numberOfVotes, 1);
			
			// Use an arbitrary number of preferences, less than the full list
			numberOfPreferences = 1 + i / 3;
			candidateIDList[i] = candidates[i].getCandidateID();
			
			// Generate first preference ballots to match
			for (int b = 0; b < numberOfVotes && ballotBox.size() < Ballot.MAX_BALLOTS; b++) {
				if (i == 0) {
					ballotBox.addBallot(candidates[i].getCandidateID());
				}
				else {
					Ballot testBallot = new TestBallot(candidateIDList,numberOfPreferences);
					ballotBox.accept(testBallot);
				}
			}
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
	 	
	 	// Find and distribute the first surplus
	 	int c = ballotCounting.findHighestCandidate();
 		ballotCounting.electCandidate(c);
 	 	ballotCounting.distributeSurplus(c);
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
