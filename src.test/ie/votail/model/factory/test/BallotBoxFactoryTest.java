package ie.votail.model.factory.test;

import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.Method;
import ie.votail.model.Outcome;
import ie.votail.model.factory.BallotBoxFactory;
import junit.framework.TestCase;

import org.junit.Test;

import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Constituency;

public class BallotBoxFactoryTest extends TestCase {
  
  
  public void testGenerateSmallestBallotBox() {
    final ElectoralScenario scenario = new ElectoralScenario(Method.STV, false);
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    final BallotBoxFactory /*@ non_null*/ballotBoxFactory = new BallotBoxFactory();
    final BallotBox ballotBox = ballotBoxFactory.extractBallots(scenario, 7);
    assertFalse(ballotBox == null);
    assertEquals(2, ballotBox.size());
  }
  
  @Test
  public void testGenerateSmallBallotBox() {
    final ElectoralScenario scenario = new ElectoralScenario(Method.STV, false);
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    scenario.addOutcome(Outcome.EarlyLoser);
    final BallotBoxFactory /*@ non_null*/ballotBoxFactory = new BallotBoxFactory();
    final ElectionConfiguration electionConfiguration =
        ballotBoxFactory.extractBallots(scenario, 7);
    assertFalse(electionConfiguration == null);
    final BallotCounting counter = new BallotCounting();
    counter.setup(electionConfiguration.getConstituency());
    counter.load(electionConfiguration);
    counter.count();
    //@ assert (counter.getStatus() == AbstractBallotCounting.FINISHED);
  }
  
  @Test
  public void testGenerateBallotBox() {
    final ElectoralScenario scenario = new ElectoralScenario(Method.STV, false);
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    scenario.addOutcome(Outcome.EarlyLoser);
    scenario.addOutcome(Outcome.SoreLoser);
    final BallotBoxFactory /*@ non_null*/ballotBoxFactory = new BallotBoxFactory();
    ElectionConfiguration electionConfiguration =
        ballotBoxFactory.extractBallots(scenario, 7);
    checkElectionConfiguration(electionConfiguration);
  }
  
  @Test
  public void testBallotBoxForTiedScenario() {
    ElectoralScenario scenario = new ElectoralScenario(Method.STV, false);
    scenario.addOutcome(Outcome.TiedWinner);
    scenario.addOutcome(Outcome.TiedLoser);
    BallotBoxFactory /*@ non_null*/voteFactory = new BallotBoxFactory();
    ElectionConfiguration voteTable = voteFactory.extractBallots(scenario, 7);
    checkElectionConfiguration(voteTable);
  }
  
  /**
   * @param voteTable
   */
  protected void checkElectionConfiguration(
      final ElectionConfiguration electionConfiguration) {
    Constituency constituency = electionConfiguration.getConstituency();
    BallotCounting counter = new BallotCounting();
    counter.setup(constituency);
    counter.load(electionConfiguration);
    counter.count();
    //@ assert (counter.getStatus() == AbstractBallotCounting.FINISHED);
  }
}
