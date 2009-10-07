package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Constituency;

public class CheckRemainingSeatsEventM extends TestCase {

  public void testEvent() {
    final BallotCounting ballotCounting = new BallotCounting();
    final Constituency constituency = new Constituency();
    constituency.setNumberOfSeats(3,3);
    constituency.setNumberOfCandidates(4);
    ballotCounting.setup(constituency);
    assertTrue(constituency.getNumberOfSeatsInThisElection() 
               == ballotCounting.getRemainingSeats());
    final BallotBox ballotBox = new BallotBox();
    final Ballot ballot = new Ballot();
    ballot.setFirstPreference(constituency.getCandidate(0).getCandidateID());
    ballotBox.accept(ballot);
    ballotCounting.load(ballotBox);
    assertTrue(constituency.getNumberOfSeatsInThisElection() 
               == ballotCounting.getRemainingSeats());
    ballotCounting.count();
    assertTrue(0 == ballotCounting.getRemainingSeats());
  }
}
