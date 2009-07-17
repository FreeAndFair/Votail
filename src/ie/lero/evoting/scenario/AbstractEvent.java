package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Election;

public abstract class AbstractEvent extends TestCase {

	protected /*@ spec_public @*/ BallotCounting ballotCounting;
	protected /*@ spec_public @*/ BallotBox ballotBox;
	protected /*@ spec_public @*/ Election parameters;
	protected /*@ spec_public @*/ char eventCode;

	protected void setUp() throws Exception {
		super.setUp();
		setEventCode();
		parameters = new Election();
		ballotBox = new BallotBox();
		ballotCounting = new BallotCounting();
		setUpParameters();
		ballotCounting.setup(parameters);
		setUpBallotBox();
		ballotCounting.load(ballotBox);
	}

	//@ assignable ballotBox;
	protected abstract void setUpBallotBox();

	//@ assignable parameters; 
	protected abstract void setUpParameters();
	
	//@ assignable eventCode;
	//@ ensures 'A' <= eventCode;
	//@ ensures eventCode <= 'R';
	protected abstract void setEventCode();
	
	public abstract void testEvent();
}