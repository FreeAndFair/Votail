package ie.votail.model.factory.test;

import ie.votail.model.Outcome;
import ie.votail.model.Scenario;
import ie.votail.model.VoteTable;
import ie.votail.model.factory.VoteFactory;
import junit.framework.TestCase;

import org.junit.Test;

import election.tally.AbstractBallotCounting;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Constituency;

public class VoteFactoryTest extends TestCase {


  @Test
  public void testGenerateSmallestBallotBox() {
    Scenario scenario = new Scenario(1);
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    VoteFactory /*@ non_null*/ voteFactory = new VoteFactory();
    VoteTable voteTable = voteFactory.generateVoteTable(scenario, 7);
    BallotBox ballotBox = voteTable.getBallotBox();
    Constituency constituency = voteTable.getConstituency();
    assertFalse(ballotBox == null);
    assertEquals(1, ballotBox.size());
    BallotCounting counter = new BallotCounting();
    counter.load(ballotBox);
    counter.count();
    assertTrue(counter.getStatus() == AbstractBallotCounting.FINISHED);
  }

  @Test
  public void testGenerateSmallBallotBox() {
    Scenario scenario = new Scenario(1);
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    scenario.addOutcome(Outcome.EarlyLoser);
    VoteFactory /*@ non_null*/ voteFactory = new VoteFactory();
    VoteTable voteTable = voteFactory.generateVoteTable(scenario, 7);
    BallotBox ballotBox = voteTable.getBallotBox();
    Constituency constituency = voteTable.getConstituency();
    assertFalse(ballotBox == null);
    BallotCounting counter = new BallotCounting();
    counter.setup(constituency);
    counter.load(ballotBox);
    counter.count();
    assertTrue(counter.getStatus() == AbstractBallotCounting.FINISHED);
  }

  @Test
  public void testGenerateBallotBox() {
    Scenario scenario = new Scenario(1);
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    scenario.addOutcome(Outcome.EarlyLoser);
    scenario.addOutcome(Outcome.SoreLoser);
    VoteFactory /*@ non_null*/ voteFactory = new VoteFactory();
    VoteTable voteTable = voteFactory.generateVoteTable(scenario, 7);
    checkVoteTable(voteTable);
  }

  @Test
  public void testBallotBoxForTiedScenario() {
    Scenario scenario = new Scenario(1);
    scenario.addOutcome(Outcome.TiedWinner);
    scenario.addOutcome(Outcome.TiedLoser);
    VoteFactory /*@ non_null*/ voteFactory = new VoteFactory();
    VoteTable voteTable = voteFactory.generateVoteTable(scenario, 7);
    checkVoteTable(voteTable);
  }

  /**
   * @param voteTable
   */
  protected void checkVoteTable(VoteTable voteTable) {
    BallotBox ballotBox = voteTable.getBallotBox();
    Constituency constituency = voteTable.getConstituency();
    assertFalse(ballotBox == null);
    BallotCounting counter = new BallotCounting();
    counter.setup(constituency);
    counter.load(ballotBox);
    counter.count();
    assertTrue(counter.getStatus() == AbstractBallotCounting.FINISHED);
  }
}
