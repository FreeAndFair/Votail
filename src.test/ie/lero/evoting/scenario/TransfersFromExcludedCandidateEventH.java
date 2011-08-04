package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.AbstractCountStatus;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Constituency;

public class TransfersFromExcludedCandidateEventH extends TestCase {
  
  public void testEvent() {
    final BallotCounting ballotCounting = new BallotCounting();
    final Constituency election = new Constituency();
    election.setNumberOfSeats(3, 4);
    election.setNumberOfCandidates(4);
    ballotCounting.setup(election);
    final BallotBox ballotBox = new BallotBox();
    final int[] preferences =
        { election.getCandidate(0).getCandidateID(),
            election.getCandidate(1).getCandidateID() };
    for (int i = 0; i < 3; i++) {
      final int[] preferenceA = { election.getCandidate(i).getCandidateID() };
      ballotBox.accept(preferenceA);
      ballotBox.accept(preferences);
    }
    
    ballotCounting.load(ballotBox);
    ballotCounting.startCounting();
    final int loser = ballotCounting.findLowestCandidate();
    ballotCounting.eliminateCandidate(loser);
    ballotCounting.incrementCountNumber();
    ballotCounting.updateCountStatus(AbstractCountStatus.CANDIDATE_EXCLUDED);
    //@ assert (ballotCounting.getContinuingCandidates() == 3);
  }
  
}
