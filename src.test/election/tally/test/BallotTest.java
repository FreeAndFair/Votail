package election.tally.test;

import org.junit.Assert;
import org.junit.Test;

import election.tally.Ballot;

public class BallotTest {
  @Test
  public void testBallot_toString() {
    final int [] preferences = {1,2,3};
    final Ballot ballot = new Ballot(preferences);
    Assert.assertEquals(ballot.toString(),"(1 2 3)");
  }
}
