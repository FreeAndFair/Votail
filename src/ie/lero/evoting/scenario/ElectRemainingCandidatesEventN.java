package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Constituency;

public class ElectRemainingCandidatesEventN extends TestCase {

  public void testEvent() {
    final BallotCounting ballotCounting = new BallotCounting();
    final Constituency constituency = new Constituency();
    constituency.setNumberOfSeats(3, 3);
    constituency.setNumberOfCandidates(4);
    ballotCounting.setup(constituency);
    final BallotBox ballotBox = new BallotBox();
    final Ballot ballot = new Ballot();
    for (int i = 0; i < 3; i++) {
      ballot.setFirstPreference(constituency.getCandidate(i).getCandidateID());
      ballotBox.accept(ballot);
    }
    ballotCounting.load(ballotBox);
    ballotCounting.count();
    for (int i = 0; i < 3; i++) {
      assertTrue(ballotCounting.isElected(constituency.getCandidate(i)));
    }
  }

}
