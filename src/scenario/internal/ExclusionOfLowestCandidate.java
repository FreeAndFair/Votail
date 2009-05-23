package scenario.internal;

import election.tally.Candidate;
import election.tally.ElectionParameters;
import election.tally.dail.DailBallotCounting;

/**
 * @author Dermot Cochran
 *
 */
public class ExclusionOfLowestCandidate {

	private DailBallotCounting ballotCounting;
	private scenario.util.TestBallotBox ballotBox;

	/**
	 * 
	 */
	public final void testExclusionOfLowestCandidate() {
	 	
	 	// Eliminate the lowest candidate
 	 	Candidate candidate = ballotCounting.findLowestCandidate();
	 	ballotCounting.eliminateCandidate(candidate);
 	}

	protected void setUp() throws Exception {
		
		ballotBox = new scenario.util.TestBallotBox();
		ballotCounting = new DailBallotCounting();
		ElectionParameters parameters = new ElectionParameters();
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
}
