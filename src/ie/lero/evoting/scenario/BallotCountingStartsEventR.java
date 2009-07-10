package ie.lero.evoting.scenario;

import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;
import election.tally.mock.MockBallot;

/**
 * @author <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 * Dermot Cochran</a>
 */
public class BallotCountingStartsEventR extends VotailEventTestCase {

	 
	protected Candidate candidate1, candidate2;
	 

	/**
	 * Test a close race between two almost equal candidates.
	 */
	public void testCount () {
		//@ assert ballotCounting.getStatus() == BallotCounting.EMPTY;
		ballotCounting.setup(parameters);
		
		//@ assert ballotCounting.getStatus() == BallotCounting.PRELOAD;
		MockBallot ballot = new MockBallot();
 		ballot.setFirstPreference(candidate2.getCandidateID());
 		ballotBox.accept(ballot);
 		ballotCounting.load(ballotBox);
		
		//@ assert ballotCounting.getStatus() == BallotCounting.PRECOUNT;
		ballotCounting.count();
	}

	//@ also ensures parameters != null;
	protected void setUp() {
		ballotCounting = new BallotCounting();
		parameters = new Election();
		parameters.totalNumberOfSeats = 1;
		parameters.numberOfSeatsInThisElection = 1;
		parameters.numberOfCandidates = 2;
		candidate1 = new Candidate();
		candidate2 = new Candidate();
		ballotBox = new BallotBox();
		
 		Candidate[] list = {candidate1,candidate2};
		parameters.setCandidateList(list);
 		
		for (int i = 0; i < 50; i++) {
		  MockBallot ballot = new MockBallot();
		  ballot.setFirstPreference(candidate1.getCandidateID());
		  ballotBox.accept(ballot);
		  ballot.setFirstPreference(candidate2.getCandidateID());
		  ballotBox.accept(ballot);
		}
		//@ assert ballotBox.size() == 101;
	}
}
