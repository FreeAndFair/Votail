package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Election;

public abstract class AbstractEvent extends TestCase {

	protected /*@ spec_public @*/ BallotCounting ballotCounting;
	protected /*@ spec_public @*/ BallotBox ballotBox;
	protected /*@ spec_public @*/ Election parameters;
}