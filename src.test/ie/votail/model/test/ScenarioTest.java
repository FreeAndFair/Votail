package ie.votail.model.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.Method;
import ie.votail.model.Outcome;

import org.junit.Test;

public class ScenarioTest {

  @Test
  public void testAddOutcome() {
    final ElectoralScenario scenario = new ElectoralScenario(Method.STV, false);
    assertFalse(scenario.hasOutcome(Outcome.TiedSoreLoser));
    scenario.addOutcome(Outcome.TiedSoreLoser);
    assertTrue(scenario.hasOutcome(Outcome.TiedSoreLoser));
  }

  @Test
  public void testCanonical() {
    final ElectoralScenario scenario = new ElectoralScenario(Method.STV, false);
    scenario.addOutcome(Outcome.EarlyLoser);
    final ElectoralScenario canonical = scenario.canonical();
    assertTrue (scenario.equivalentTo(canonical));
  }

  @Test
  public void testAppend() {
    final ElectoralScenario scenario = new ElectoralScenario(Method.STV, false);
    final ElectoralScenario oneWinner = scenario.append(Outcome.Winner);
    final ElectoralScenario oneLoser = scenario.append(Outcome.Loser);
    final ElectoralScenario twoOutcomes = oneWinner.append(Outcome.Loser);
    assertEquals (1,twoOutcomes.numberOfWinners());
    assertEquals (1,oneWinner.numberOfWinners());
    assertEquals (0,oneLoser.numberOfWinners());
    assertFalse (oneWinner.equivalentTo(oneLoser));
    assertFalse (scenario.equivalentTo(oneLoser));
    assertTrue (twoOutcomes.equivalentTo(oneLoser.append(Outcome.Winner)));
  }

  @Test
  public void testIsTied() {
    final ElectoralScenario scenario = new ElectoralScenario(Method.STV, false);
    assertFalse (scenario.isTied());
    scenario.addOutcome(Outcome.TiedWinner);
    assertTrue (scenario.isTied());
  }

  @Test
  public void testNumberOfScenarios() {
    assertEquals (ElectoralScenario.totalNumberOfScenarios(2), 
                  ElectoralScenario.numberOfScenarios(1, 1));  
  }

  @Test
  public void testTotalNumberOfScenarios() {
    assertEquals (
      ElectoralScenario.numberOfScenarios(2, 1) + ElectoralScenario.numberOfScenarios(1, 2), 
      ElectoralScenario.totalNumberOfScenarios(3));
  }

}
