package scenario.internal;

import election.tally.Candidate;
import election.tally.ElectionParameters;
import election.tally.dail.DailBallotCounting;

/**
 * @author Dermot Cochran
 *
 */
public class DistributionOfSurplus {
	
	protected DailBallotCounting ballotCounting;
	protected ElectionParameters parameters;
	protected Candidate candidate;
	protected scenario.util.TestBallotBox ballotBox;
	
	/**
	 * Create the scenario data needed
	 */
	protected void setUp() throws Exception {
		ballotCounting = new DailBallotCounting();
		ballotBox = new scenario.util.TestBallotBox();
		parameters = new ElectionParameters();
		parameters.totalNumberOfSeats = 4;
		parameters.numberOfSeatsInThisElection = 4;
		parameters.numberOfCandidates = parameters.totalNumberOfSeats + 2;
		
		// Generate sample candidates
	 	Candidate[] candidates = new Candidate[parameters.numberOfCandidates];
		for (int i = 0; i < parameters.numberOfCandidates; i++) {
			candidates[i] = new Candidate();
			int numberOfVotes = i*1000;
			candidates[i].addVote(numberOfVotes, 1);
			
			// Generate first preference ballots to match
			for (int b = 0; b < numberOfVotes; b++) {
				ballotBox.addBallot(candidates[i].getCandidateID());
			}
		}
	 	parameters.setCandidateList(candidates);	
	}

	public void testDistributionOfSurplus() {
	 
	 	ballotCounting.setup(parameters);
	 	ballotCounting.distributeSurplus(ballotCounting.findHighestCandidate());
	}
}
