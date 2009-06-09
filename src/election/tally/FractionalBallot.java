package election.tally;

public class FractionalBallot extends Ballot {

	protected class Weight {
		long numerator;
		long denominator;

	}

	Weight[] weights;
}
