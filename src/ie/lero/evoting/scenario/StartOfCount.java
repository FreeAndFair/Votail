package ie.lero.evoting.scenario;

import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.Candidate;
import election.tally.ElectionParameters;
import election.tally.dail.DailBallotCounting;


/**
 * @author Dermot Cochran
 *
 */
public class StartOfCount {

	protected DailBallotCounting ballotCounting;
	protected ElectionParameters parameters;
	protected Candidate candidate;
	protected BallotBox ballotBox;

	/**
	 * Test that the count process is started correctly.
	 */
	//@ requires parameters != null;
	public void testStartOfCount () {
		ballotCounting.setup(parameters);
		//@ assert ballotCounting.getStatus() == AbstractBallotCounting.PRECOUNT;
		ballotCounting.count();
		//@ assert ballotCounting.getStatus() == AbstractBallotCounting.FINISHED;
		ballotCounting.report();
		
	}

	//@ ensures parameters != null;
	protected void setUp() {
		ballotCounting = new DailBallotCounting();
		parameters = new ElectionParameters();
		parameters.totalNumberOfSeats = 4;
		parameters.numberOfSeatsInThisElection = 4;
		parameters.numberOfCandidates = 3;
		candidate = new Candidate();
		ballotBox = new BallotBox();
		ballotBox.numberOfBallots = 2;
		Ballot ballot1 = new Ballot();
		int[] list1 = {1};
		ballot1.load(list1);
		Ballot ballot2 = new Ballot();
		int[] list2 = {3,2};
		ballot2.load(list2);
	}
	
	/**
	 * 
	 */
	public void main() {
		setUp();
		testStartOfCount();
	}
}
