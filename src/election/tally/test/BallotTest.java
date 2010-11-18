package election.tally.test;

import org.testng.Assert;
import org.testng.annotations.Test;

import election.tally.Ballot;

public class BallotTest {
  @Test
  public void testBallot_toString() {
    int [] preferences = {1,2,3};
    Ballot ballot = new Ballot(preferences);
    Assert.assertEquals(ballot.toString(),"(1 2 3)");
  }
}
