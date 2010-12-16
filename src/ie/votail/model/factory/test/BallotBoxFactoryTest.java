package ie.votail.model.factory.test;

import ie.votail.model.Outcome;
import ie.votail.model.Scenario;
import ie.votail.model.factory.BallotBoxFactory;
import junit.framework.TestCase;

import org.junit.Test;

import election.tally.BallotBox;

public class BallotBoxFactoryTest extends TestCase {

  private static final int EXPECTED_NUMBER_OF_BALLOTS_WL = 3;
  private static final String MODELS_VOTING_ALS = "models/voting.als";

  @Test
  public void testGenerateBallotBox() {
    Scenario scenario = new Scenario();
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    //scenario.addOutcome(Outcome.EarlyLoser);
    //scenario.addOutcome(Outcome.SoreLoser);
    BallotBoxFactory /*@ non_null*/ ballotBoxFactory 
      = new BallotBoxFactory(BallotBoxFactoryTest.MODELS_VOTING_ALS);
    BallotBox ballotBox = ballotBoxFactory.generateBallotBox(scenario, 7);
    assertFalse (ballotBox == null);
    assertEquals (BallotBoxFactoryTest.EXPECTED_NUMBER_OF_BALLOTS_WL, 
      ballotBox.size());
  }
}
