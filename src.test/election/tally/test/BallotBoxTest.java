package election.tally.test;

import org.junit.Assert;
import org.junit.Test;

import election.tally.BallotBox;

public class BallotBoxTest {
  @Test
  public void testBallotBox_toString() {
    int [] preferences = {1,2,3};
    BallotBox box = new BallotBox();
    box.accept(preferences);
    box.accept(preferences);
    Assert.assertEquals(box.toString(),"[2 ballots ](1 2 3)(1 2 3)");
  }
}
