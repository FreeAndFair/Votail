package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Constituency;

public class CheckRemainingSeatsEventM extends TestCase {

  public void testEvent() {
    BallotCounting ballotCounting = new BallotCounting();
    Constituency constituency = new Constituency();
    constituency.setNumberOfSeatsInThisElection(3);
    constituency.setTotalNumberOfSeats(3);
    constituency.setNumberOfCandidates(4);
    ballotCounting.setup(constituency);
    assertTrue(constituency.getNumberOfSeatsInThisElection() 
               == ballotCounting.getRemainingSeats());
    BallotBox ballotBox = new BallotBox();
    Ballot ballot = new Ballot();
    ballot.setFirstPreference(constituency.getCandidate(0).getCandidateID());
    ballotBox.accept(ballot);
    ballotCounting.load(ballotBox);
    assertTrue(constituency.getNumberOfSeatsInThisElection() 
               == ballotCounting.getRemainingSeats());
    ballotCounting.count();
    assertTrue(0 == ballotCounting.getRemainingSeats());
  }
}
