package ie.votail.model.factory.test;

import ie.votail.model.Outcome;
import ie.votail.model.Scenario;
import ie.votail.model.factory.BallotBoxFactory;
import junit.framework.TestCase;

import org.junit.Test;

import election.tally.BallotBox;
import election.tally.BallotCounting;

public class BallotBoxFactoryTest extends TestCase {

  private static final String MODELS_VOTING_ALS = "models/voting.als";

  @Test
  public void testGenerateSmallestBallotBox() {
    Scenario scenario = new Scenario();
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    BallotBoxFactory /*@ non_null*/ ballotBoxFactory 
      = new BallotBoxFactory(BallotBoxFactoryTest.MODELS_VOTING_ALS);
    BallotBox ballotBox = ballotBoxFactory.generateBallotBox(scenario, 7);
    assertFalse (ballotBox == null);
    assertEquals (1, ballotBox.size());
    BallotCounting counter = new BallotCounting();
    counter.load(ballotBox);
    counter.count();
    assertTrue (counter.verify(scenario));
  }
  
  @Test
  public void testGenerateSmallBallotBox() {
    Scenario scenario = new Scenario();
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    scenario.addOutcome(Outcome.EarlyLoser);
    BallotBoxFactory /*@ non_null*/ ballotBoxFactory 
      = new BallotBoxFactory(BallotBoxFactoryTest.MODELS_VOTING_ALS);
    BallotBox ballotBox = ballotBoxFactory.generateBallotBox(scenario, 7);
    assertFalse (ballotBox == null);
    assertEquals (2, ballotBox.size());
    BallotCounting counter = new BallotCounting();
    counter.load(ballotBox);
    counter.count();
    assertTrue (counter.verify(scenario));
  }
  
  @Test
  public void testGenerateBallotBox() {
    Scenario scenario = new Scenario();
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    scenario.addOutcome(Outcome.EarlyLoser);
    scenario.addOutcome(Outcome.SoreLoser);
    BallotBoxFactory /*@ non_null*/ ballotBoxFactory 
      = new BallotBoxFactory(BallotBoxFactoryTest.MODELS_VOTING_ALS);
    BallotBox ballotBox = ballotBoxFactory.generateBallotBox(scenario, 7);
    assertFalse (ballotBox == null);
    assertEquals (4, ballotBox.size());
    BallotCounting counter = new BallotCounting();
    counter.load(ballotBox);
    counter.count();
    assertTrue (counter.verify(scenario));
  }
}
