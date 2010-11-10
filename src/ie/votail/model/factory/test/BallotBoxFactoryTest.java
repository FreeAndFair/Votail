package ie.votail.model.factory.test;

import ie.votail.model.Outcome;
import ie.votail.model.Scenario;
import ie.votail.model.factory.BallotBoxFactory;
import junit.framework.TestCase;

import org.junit.Test;

import election.tally.BallotBox;

public class BallotBoxFactoryTest extends TestCase {

  @Test
  public void testGenerateBallotBox() {
    Scenario scenario = new Scenario();
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    BallotBoxFactory ballotBoxFactory 
      = new BallotBoxFactory("models/voting.als","testdata/test.log");
    BallotBox ballotBox = ballotBoxFactory.generateBallotBox(scenario, 10, 5);
    assertFalse (ballotBox == null);
  }
}
