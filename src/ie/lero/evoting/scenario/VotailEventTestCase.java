package ie.lero.evoting.scenario;

import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;
import junit.framework.TestCase;

public abstract class VotailEventTestCase extends TestCase {

	protected BallotCounting ballotCounting;
	protected BallotBox ballotBox;
	protected Election parameters;
	protected Candidate candidate;

	public VotailEventTestCase() {
		super();
	}

	public VotailEventTestCase(String name) {
		super(name);
	}

}