package ie.votail.scenario;

import ie.votail.tally.BallotBox;
import ie.votail.tally.BallotCounting;
import ie.votail.tally.Constituency;
import junit.framework.TestCase;

public class ElectRemainingCandidatesEventN extends TestCase {

  public void testEvent() {
    final BallotCounting ballotCounting = new BallotCounting();
    final Constituency constituency = new Constituency();
    constituency.setNumberOfSeats(3, 3);
    constituency.setNumberOfCandidates(4);
    // TODO precondition not established
    ballotCounting.setup(constituency); //@ nowarn;
    final BallotBox ballotBox = new BallotBox();
    final int[] preferences = new int[1];
      
    for (int i = 0; i < 3; i++) {
      preferences[0] = constituency.getCandidate(i).getCandidateID();
      ballotBox.accept(preferences); //@ nowarn;
    }
    ballotCounting.load(ballotBox);
    ballotCounting.count();
    for (int i = 0; i < 3; i++) {
      assertTrue(ballotCounting.isElected(constituency.getCandidate(i)));
    }
  }

}
