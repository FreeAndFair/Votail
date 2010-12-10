package ie.votail.model.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import ie.votail.model.Outcome;
import ie.votail.model.Scenario;

import org.junit.Test;

public class ScenarioTest {

  @Test
  public void testToString() {
    Scenario scenario = new Scenario();
    assertEquals("Scenario: ()",scenario.toString());
    scenario.addOutcome(Outcome.Winner);
    scenario.addOutcome(Outcome.Loser);
    assertEquals("Scenario: (Winner,Loser)",scenario.toString());
  }

  @Test
  public void testAddOutcome() {
    Scenario scenario = new Scenario();
    assertFalse(scenario.hasTiedSoreLoser());
    scenario.addOutcome(Outcome.TiedSoreLoser);
    assertTrue(scenario.hasTiedSoreLoser());
  }

  @Test
  public void testToPredicate() {
    Scenario scenario = new Scenario();
    scenario.addOutcome(Outcome.TiedWinner);
    scenario.addOutcome(Outcome.TiedLoser);
    assertEquals(
      "some disj c0,c1: Candidate | c0.outcome = TiedWinner and c1.outcome = TiedLoser",
      scenario.toPredicate());
  }

  @Test
  public void testCanonical() {
    Scenario scenario = new Scenario();
    scenario.addOutcome(Outcome.EarlyLoser);
    Scenario canonical = scenario.canonical();
    assertTrue (scenario.equivalentTo(canonical));
  }

  @Test
  public void testAppend() {
    Scenario scenario = new Scenario();
    Scenario oneWinner = scenario.append(Outcome.Winner);
    Scenario oneLoser = scenario.append(Outcome.Loser);
    Scenario twoOutcomes = oneWinner.append(Outcome.Loser);
    assertEquals (1,twoOutcomes.numberOfWinners());
    assertEquals (1,oneWinner.numberOfWinners());
    assertEquals (0,oneLoser.numberOfWinners());
    assertFalse (oneWinner.equivalentTo(oneLoser));
    assertFalse (scenario.equivalentTo(oneLoser));
    assertTrue (twoOutcomes.equivalentTo(oneLoser.append(Outcome.Winner)));
  }

  @Test
  public void testIsTied() {
    Scenario scenario = new Scenario();
    assertFalse (scenario.isTied());
    scenario.addOutcome(Outcome.TiedWinner);
    assertTrue (scenario.isTied());
  }

  @Test
  public void testNumberOfScenarios() {
    assertEquals (Scenario.totalNumberOfScenarios(2), 
                  Scenario.numberOfScenarios(1, 1));  
  }

  @Test
  public void testTotalNumberOfScenarios() {
    assertEquals (
      Scenario.numberOfScenarios(2, 1) + Scenario.numberOfScenarios(1, 2), 
      Scenario.totalNumberOfScenarios(3));
  }

}
