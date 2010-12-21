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

  public static final String MODELS_VOTING_ALS = "models/voting.als";

  @Test
  public void testGenerateSmallestBallotBox() {
    Scenario scenario = new Scenario(1);
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    VoteFactory /*@ non_null*/ voteFactory 
      = new VoteFactory(VoteFactoryTest.MODELS_VOTING_ALS);
    VoteTable voteTable = voteFactory.generateVoteTable(scenario, 7);
    BallotBox ballotBox = voteTable.getBallotBox();
    Constituency constituency = voteTable.getConstituency();
    assertFalse (ballotBox == null);
    assertEquals (1, ballotBox.size());
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
    VoteFactory /*@ non_null*/ voteFactory 
    = new VoteFactory(VoteFactoryTest.MODELS_VOTING_ALS);
  VoteTable voteTable = voteFactory.generateVoteTable(scenario, 7);
  BallotBox ballotBox = voteTable.getBallotBox();
  Constituency constituency = voteTable.getConstituency();
    assertFalse (ballotBox == null);
    assertEquals (2, ballotBox.size());
    BallotCounting counter = new BallotCounting();
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
    VoteFactory /*@ non_null*/ voteFactory 
    = new VoteFactory(VoteFactoryTest.MODELS_VOTING_ALS);
  VoteTable voteTable = voteFactory.generateVoteTable(scenario, 7);
  BallotBox ballotBox = voteTable.getBallotBox();
  Constituency constituency = voteTable.getConstituency();
    assertFalse (ballotBox == null);
    assertEquals (4, ballotBox.size());
    BallotCounting counter = new BallotCounting();
    counter.load(ballotBox);
    counter.count();
    assertTrue(counter.getStatus() == AbstractBallotCounting.FINISHED);
  }
}
