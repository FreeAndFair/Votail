package ie.lero.evoting.scenario;

import scenario.util.TestBallotBox;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;


/**
 * @author Dermot Cochran
 *
 */
public class StartOfCount implements Scenario {

	protected BallotCounting ballotCounting;
	protected /*@ spec_public @*/ Election parameters;
	protected Candidate candidate;
	protected BallotBox ballotBox;

	/**
	 * Test that the count process is started correctly.
	 */
	public void run () {
		ballotCounting.setup(parameters);
		//@ assert ballotCounting.getStatus() == BallotCounting.PRECOUNT;
		ballotCounting.count();
		//@ assert ballotCounting.getStatus() == BallotCounting.FINISHED;
		ballotCounting.report();
		
	}

	//@ ensures parameters != null;
	public StartOfCount() {
		ballotCounting = new BallotCounting();
		parameters = new Election();
		parameters.totalNumberOfSeats = 4;
		parameters.numberOfSeatsInThisElection = 4;
		parameters.numberOfCandidates = 3;
		candidate = new Candidate();
		ballotBox = new TestBallotBox();
	}
	
	/**
	 * @param args unused
	 */
	public static void main(String[] args) {
		Scenario scenario = new StartOfCount();
		scenario.run();
	}
}
