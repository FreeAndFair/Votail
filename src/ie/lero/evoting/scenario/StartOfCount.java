package ie.lero.evoting.scenario;

import scenario.util.TestBallotBox;
import election.tally.BallotBox;
import election.tally.Candidate;
import election.tally.Election;
import election.tally.dail.DailBallotCounting;


/**
 * @author Dermot Cochran
 *
 */
public class StartOfCount implements Scenario {

	protected DailBallotCounting ballotCounting;
	protected /*@ spec_public @*/ Election parameters;
	protected Candidate candidate;
	protected BallotBox ballotBox;

	/**
	 * Test that the count process is started correctly.
	 */
	//@ requires parameters != null;
	public void run () {
		ballotCounting.setup(parameters);
		//@ assert ballotCounting.getStatus() == AbstractBallotCounting.PRECOUNT;
		ballotCounting.count();
		//@ assert ballotCounting.getStatus() == AbstractBallotCounting.FINISHED;
		ballotCounting.report();
		
	}

	//@ ensures parameters != null;
	public StartOfCount() {
		ballotCounting = new DailBallotCounting();
		parameters = new Election();
		parameters.totalNumberOfSeats = 4;
		parameters.numberOfSeatsInThisElection = 4;
		parameters.numberOfCandidates = 3;
		candidate = new Candidate();
		ballotBox = new TestBallotBox();
	}
	
	/**
	 * 
	 */
	public static void main(String[] args) {
		Scenario scenario = new StartOfCount();
		scenario.run();
	}
}
