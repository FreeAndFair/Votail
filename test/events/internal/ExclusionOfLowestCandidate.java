package internal;

import junit.framework.TestCase;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.Candidate;
import election.tally.ElectionParameters;
import election.tally.dail.DailBallotCounting;

public class ExclusionOfLowestCandidate extends TestCase {

	private DailBallotCounting ballotCounting;
	private int nextBallot;
	private BallotBox ballotBox;

	public final void testExclusionOfLowestCandidate() {
	 	
	 	// Eliminate the lowest candidate
 	 	Candidate candidate = ballotCounting.findLowestCandidate();
	 	ballotCounting.eliminateCandidate(candidate);
 	}

	protected void setUp() throws Exception {
		
		super.setUp();
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
				
				ballotBox.ballots[nextBallot++] = new Ballot(candidates[i].getCandidateID());
			}
		}
		
		
		parameters.setCandidateList(candidates);
 	 	ballotCounting.setup(parameters);
 	 	ballotCounting.load(ballotBox);
	}
}
