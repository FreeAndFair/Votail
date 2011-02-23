package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Constituency;

public class CheckRemainingSeatsEventM extends TestCase {

  public void testEvent() {
    final BallotCounting ballotCounting = new BallotCounting();
    final Constituency constituency = new Constituency();
    constituency.setNumberOfSeats(3,3);
    constituency.setNumberOfCandidates(4);
    // TODO precondition not established
    ballotCounting.setup(constituency); //@ nowarn;
    assertTrue(constituency.getNumberOfSeatsInThisElection() 
               == ballotCounting.getRemainingSeats()); //@ nowarn;
    final BallotBox ballotBox = new BallotBox();
    final int[] preferences = new int[1];
    preferences[0] = constituency.getCandidate(0).getCandidateID();
    ballotBox.accept(preferences);
    ballotCounting.load(ballotBox);
    assertTrue(constituency.getNumberOfSeatsInThisElection() 
               == ballotCounting.getRemainingSeats());
    ballotCounting.count();
    assertTrue(0 == ballotCounting.getRemainingSeats());
  }
}
