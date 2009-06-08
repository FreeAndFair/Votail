package ie.lero.evoting.scenario;

import election.tally.Ballot;
import election.tally.Candidate;
import election.tally.Election;
import election.tally.Report;
import election.tally.dail.DailBallotCounting;

/**
 * @author Dermot Cochran
 * @copyright 2009 Dermot Cochran
 */
public class SurplusScenario {
	
	protected DailBallotCounting ballotCounting;
	protected Election parameters;
	protected Candidate candidate;
	protected scenario.util.TestBallotBox ballotBox;
	
	/**
	 * Create the scenario data needed
	 */
	protected void setUp() {
		ballotCounting = new DailBallotCounting();
		ballotBox = new scenario.util.TestBallotBox();
		parameters = new Election();
		parameters.totalNumberOfSeats = 5;
		parameters.numberOfSeatsInThisElection = parameters.totalNumberOfSeats;
		parameters.numberOfCandidates = Candidate.MAX_CANDIDATES;
		
		// Generate sample candidates
	 	Candidate[] candidates = new Candidate[parameters.numberOfCandidates];
		for (int i = 0; i < parameters.numberOfCandidates; i++) {
			candidates[i] = new Candidate();
			int numberOfVotes = i+100;
			candidates[i].addVote(numberOfVotes, 1);
			
			// Generate first preference ballots to match
			for (int b = 0; b < numberOfVotes && ballotBox.size() < Ballot.MAX_BALLOTS; b++) {
				ballotBox.addBallot(candidates[i].getCandidateID());
			}
		}
	 	parameters.setCandidateList(candidates);	
	}
	 
	/**
	 * Test the distribution of surplus ballots
	 */
	public void testDistributionOfSurplus() {
	 
	 	ballotCounting.setup(parameters);
	 	candidate = ballotCounting.findHighestCandidate();
	 	//@ assert candidate.getStatus() == Candidate.CONTINUING;
		candidate.declareElected();
 		//@ assert candidate.getStatus() == Candidate.ELECTED;
	 	ballotCounting.distributeSurplus(candidate);
	 	Report report = ballotCounting.report();
	 	System.out.println(report.getResults());
	 	System.out.println(ballotCounting.getDecisionLog());
	}
	
	/**
	 * Election of the highest candidate and distribution of their surplus ballots.
	 */
	public static void main(String[] args) {
		SurplusScenario scenario = new SurplusScenario();
		scenario.setUp();
		scenario.testDistributionOfSurplus();
	}
}
