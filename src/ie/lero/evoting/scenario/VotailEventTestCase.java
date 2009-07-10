package ie.lero.evoting.scenario;

import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;
import junit.framework.TestCase;

public abstract class VotailEventTestCase extends TestCase {

	protected /*@ spec_public @*/ BallotCounting ballotCounting;
	protected /*@ spec_public @*/ BallotBox ballotBox;
	protected /*@ spec_public @*/ Election parameters;
	protected /*@ spec_public @*/ Candidate candidate;

	public VotailEventTestCase() {
		super();
	}

	public VotailEventTestCase(String name) {
		super(name);
	}

}