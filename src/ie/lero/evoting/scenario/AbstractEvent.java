package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Election;

public abstract class AbstractEvent extends TestCase {

	protected /*@ spec_public @*/ BallotCounting ballotCounting;
	protected /*@ spec_public @*/ BallotBox ballotBox;
	protected /*@ spec_public @*/ Election parameters;
	protected /*@ spec_public @*/ char eventClass;

	public AbstractEvent() {
		super();
	}

	protected void setUp() throws Exception {
		super.setUp();
		setEventClass();
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
	
	//@ assignable eventClass;
	protected abstract void setEventClass();
}