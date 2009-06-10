package ie.lero.evoting.scenario;

import election.tally.AbstractBallotCounting;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;

/**
 * This is a test for the correctness of the ballot counting process in the 
 * event that the lowest continuing candidate is excluded from election.
 * 
 * @author <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 * Dermot Cochran</a>
 * 
 * @see election.tally.Candidate
 */
public class ExclusionScenario implements Scenario {

	private AbstractBallotCounting ballotCounting;
	private scenario.util.TestBallotBox ballotBox;

	
	/**
	 * Execute this scenario.
	 */
	public final void run() {
	 	
 	 	Candidate candidate = ballotCounting.findLowestCandidate();
	 	ballotCounting.eliminateCandidate(candidate);
 	}

	/**
	 * Create test data for a mock election.
	 */
	public ExclusionScenario() {
		
		ballotBox = new scenario.util.TestBallotBox();
		ballotCounting = new BallotCounting();
		Election parameters = new Election();
		parameters.totalNumberOfSeats = 4;
		parameters.numberOfSeatsInThisElection = 4;
		
		// Generate candidates
		int numberOfCandidates = 2 + parameters.numberOfSeatsInThisElection;
		Candidate[] candidates = new Candidate[numberOfCandidates];
		for (int i = 0; i < numberOfCandidates; i++) {
			candidates[i] = new Candidate();
			int numberOfVotes = i*1000;
			candidates[i].addVote(numberOfVotes, 1);
			
			// Generate first preference ballots
			for (int b = 0; b < numberOfVotes; b++) {
				
				ballotBox.addBallot(candidates[i].getCandidateID());
			}
		}
		
		parameters.setCandidateList(candidates);
 	 	ballotCounting.setup(parameters);
 	 	ballotCounting.load(ballotBox);
	}
	
	/**
	 * Test the event that the lowest continuing candidate is excluded from 
	 * election.
	 * 
	 * @param args unused
	 */
	public static void main(String[] args) {
		Scenario scenario = new ExclusionScenario();
		scenario.run();
	}
}
