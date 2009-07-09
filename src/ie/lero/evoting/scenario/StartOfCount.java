package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;
import election.tally.Report;

/**
 * @author <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 * Dermot Cochran</a>
 */
public class StartOfCount extends TestCase {

	protected BallotCounting ballotCounting;
	protected /*@ spec_public @*/ Election parameters;
	protected Candidate candidate1, candidate2;
	protected BallotBox ballotBox;

	/**
	 * Test a close race between two almost equal candidates.
	 */
	public void testCount () {
		//@ assert ballotCounting.getStatus() == BallotCounting.EMPTY;
		ballotCounting.setup(parameters);
		
		//@ assert ballotCounting.getStatus() == BallotCounting.PRELOAD;
		Ballot ballot = new Ballot();
 		ballot.setFirstPreference(candidate2.getCandidateID());
 		ballotBox.accept(ballot);
 		ballotCounting.load(ballotBox);
		
		//@ assert ballotCounting.getStatus() == BallotCounting.PRECOUNT;
		ballotCounting.count();
		
		assertTrue(ballotCounting.getStatus() == election.tally.AbstractBallotCounting.FINISHED);
		//@ assert ballotCounting.getStatus() == BallotCounting.FINISHED;
		final Report report = ballotCounting.report();
		assertTrue(1 == report.getNumberElected());
		//@ assert 1 == ballotCounting.report().getNumberElected();
		assertTrue(ballotCounting.isDepositSaved(candidate1));
		//@ assert ballotCounting.isDepositSaved(candidate1);
		assertTrue(ballotCounting.isDepositSaved(candidate2));
		//@ assert ballotCounting.isDepositSaved(candidate2);
		assertTrue(ballotCounting.isElected(candidate2));
		//@ assert ballotCounting.isElected(candidate2);
		assertTrue(report.isElectedCandidateID(candidate2.getCandidateID()));
		/*@ assert ballotCounting.report().isElectedCandidateID(
		  @                                  candidate2.getCandidateID());
		  @*/
		assertTrue(1 == report.getTotalNumberOfCounts());
		//@ assert 1 == ballotCounting.report().getTotalNumberOfCounts();
	}
	
	/**
	 * Test a tie between two equal candidates.
	 */
	public void testTie () {
		//@ assert ballotCounting.getStatus() == BallotCounting.EMPTY;
		ballotCounting.setup(parameters);
		
		//@ assert ballotCounting.getStatus() == BallotCounting.PRELOAD;
		ballotCounting.load(ballotBox);
		
		//@ assert ballotCounting.getStatus() == BallotCounting.PRECOUNT;
		ballotCounting.count();
		
		//@ assert ballotCounting.getStatus() == BallotCounting.FINISHED;
		//@ assert 1 == ballotCounting.report().getNumberElected();
		//@ assert ballotCounting.isDepositSaved(candidate1);
		//@ assert ballotCounting.isDepositSaved(candidate2);
		//@ assert 1 == ballotCounting.report().getTotalNumberOfCounts();
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
		  Ballot ballot = new Ballot();
		  ballot.setFirstPreference(candidate1.getCandidateID());
		  ballotBox.accept(ballot);
		  ballot = new Ballot();
		  ballot.setFirstPreference(candidate2.getCandidateID());
		  ballotBox.accept(ballot);
		}
		//@ assert ballotBox.size() == 101;
	}
	
	// JML RAC
	public static void main (String[] args) {
		StartOfCount scenario = new StartOfCount();
		scenario.setUp();
		scenario.testCount();
		scenario.setUp();
		scenario.testTie();
	}
}
