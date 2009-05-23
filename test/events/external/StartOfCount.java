package external;

import junit.framework.TestCase;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.Candidate;
import election.tally.ElectionParameters;
import election.tally.dail.DailBallotCounting;


public class StartOfCount extends TestCase {

	protected DailBallotCounting ballotCounting;
	protected ElectionParameters parameters;
	protected Candidate candidate;
	protected BallotBox ballotBox;

	/**
	 * Test that the count process is started correctly.
	 */
	public void testStartOfCount () {
		ballotCounting.setup(parameters);
		assert ballotCounting.getStatus() == DailBallotCounting.PRECOUNT;
		ballotCounting.count();
		assert ballotCounting.getStatus() == DailBallotCounting.FINISHED;
		
	}

	protected void setUp() throws Exception {
		super.setUp();
		ballotCounting = new DailBallotCounting();
		parameters = new ElectionParameters();
		parameters.totalNumberOfSeats = 4;
		parameters.numberOfSeatsInThisElection = 4;
		parameters.candidateIDs = new long[]{1,2,3};
		parameters.numberOfCandidates = 3;
		candidate = new Candidate();
		ballotBox = new BallotBox();
		ballotBox.numberOfBallots = 2;
		Ballot ballot1 = new Ballot();
		int[] list1 = {1};
		ballot1.load(list1 , list1.length);
		Ballot ballot2 = new Ballot();
		int[] list2 = {3,2};
		ballot2.load(list2 , list2.length);
		ballotBox.ballots =  new Ballot[] {ballot1,ballot2};
	}
}
