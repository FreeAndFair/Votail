package ie.votail.model.factory.test;

import ie.votail.model.Method;
import ie.votail.model.Outcome;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.ElectionConfiguration;
import ie.votail.model.factory.BallotBoxFactory;
import junit.framework.TestCase;

import org.junit.Test;

import election.tally.AbstractBallotCounting;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Constituency;

public class BallotBoxFactoryTest extends TestCase {


  @Test
  public void testGenerateSmallestBallotBox() {
    ElectoralScenario scenario = new ElectoralScenario(Method.STV);
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    BallotBoxFactory /*@ non_null*/ ballotBoxFactory = new BallotBoxFactory();
    BallotBox ballotBox = ballotBoxFactory.extractBallots(scenario, 7);
    assertFalse(ballotBox == null);
    assertEquals(1, ballotBox.size());
    BallotCounting counter = new BallotCounting();
    counter.load(ballotBox);
    counter.count();
    assertTrue(counter.getStatus() == AbstractBallotCounting.FINISHED);
  }

  @Test
  public void testGenerateSmallBallotBox() {
    ElectoralScenario scenario = new ElectoralScenario(Method.STV);
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    scenario.addOutcome(Outcome.EarlyLoser);
    BallotBoxFactory /*@ non_null*/ ballotBoxFactory = new BallotBoxFactory();
    ElectionConfiguration electionConfiguration = ballotBoxFactory.extractBallots(scenario, 7);
    assertFalse(electionConfiguration == null);
    BallotCounting counter = new BallotCounting();
    counter.setup(electionConfiguration.getConstituency());
    counter.load(electionConfiguration);
    counter.count();
    assertTrue(counter.getStatus() == AbstractBallotCounting.FINISHED);
  }

  @Test
  public void testGenerateBallotBox() {
    ElectoralScenario scenario = new ElectoralScenario(Method.STV);
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    scenario.addOutcome(Outcome.EarlyLoser);
    scenario.addOutcome(Outcome.SoreLoser);
    BallotBoxFactory /*@ non_null*/ ballotBoxFactory = new BallotBoxFactory();
    ElectionConfiguration electionConfiguration 
      = ballotBoxFactory.extractBallots(scenario, 7);
    checkElectionConfiguration(electionConfiguration);
  }

  @Test
  public void testBallotBoxForTiedScenario() {
    ElectoralScenario scenario = new ElectoralScenario(Method.STV);
    scenario.addOutcome(Outcome.TiedWinner);
    scenario.addOutcome(Outcome.TiedLoser);
    BallotBoxFactory /*@ non_null*/ voteFactory = new BallotBoxFactory();
    ElectionConfiguration voteTable = voteFactory.extractBallots(scenario, 7);
    checkElectionConfiguration(voteTable);
  }

  /**
   * @param voteTable
   */
  protected void checkElectionConfiguration (
     ElectionConfiguration electionConfiguration) {
    Constituency constituency = electionConfiguration.getConstituency();
    assertFalse(electionConfiguration == null);
    BallotCounting counter = new BallotCounting();
    counter.setup(constituency);
    counter.load(electionConfiguration);
    counter.count();
    assertTrue(counter.getStatus() == AbstractBallotCounting.FINISHED);
  }
}
