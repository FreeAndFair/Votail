package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;


/**
 * @author Dermot Cochran
 *
 */
public class StartOfCount extends TestCase {

	protected BallotCounting ballotCounting;
	protected /*@ spec_public @*/ Election parameters;
	protected Candidate candidate1, candidate2;
	protected BallotBox ballotBox;

	/**
	 * Test that the count process is started correctly.
	 */
	public void testCount () {
		ballotCounting.setup(parameters);
		ballotCounting.load(ballotBox);
		
		//@ assert ballotCounting.getStatus() == BallotCounting.PRECOUNT;
		ballotCounting.count();
		//@ assert ballotCounting.getStatus() == BallotCounting.FINISHED;
		
		//@ assert 1 == ballotCounting.report().getNumberElected();
		//@ assert ballotCounting.report().hasSavedDeposit(candidate1.getCandidateID());
		//@ assert ballotCounting.report().isElected(candidate2.getCandidateID());
		//@ assert 1 == ballotCounting.report().getTotalNumberofCounts();
	}

	//@ ensures parameters != null;
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
 		Ballot ballot = new Ballot();
 		ballot.setFirstPreference(candidate2.getCandidateID());
 		ballotBox.accept(ballot);

		// A close race between two almost equal candidates
		for (int i = 0; i < 50; i++) {
		  ballot = new Ballot();
		  ballot.setFirstPreference(candidate1.getCandidateID());
		  ballotBox.accept(ballot);
		  ballot = new Ballot();
		  ballot.setFirstPreference(candidate2.getCandidateID());
		  ballotBox.accept(ballot);
		}
		//@ assert ballotBox.size() == 101;
	}
}
