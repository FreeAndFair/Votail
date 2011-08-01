package ie.votail.model.factory.test;

import ie.votail.model.ElectoralScenario;
import ie.votail.model.Method;
import ie.votail.model.Outcome;
import ie.votail.model.factory.ScenarioList;
import junit.framework.TestCase;

import org.junit.Test;

public class ScenarioListTest extends TestCase {
  
  
  public void testAddScenario() {
    final ScenarioList scenarioList = new ScenarioList();
    final ElectoralScenario scenario = new ElectoralScenario(Method.STV, false);
    scenarioList.add(scenario);
    scenarioList.add(scenario.canonical());
    final boolean addDuplicate = scenarioList.add(scenario);
    assertFalse(addDuplicate);
    assertTrue(scenarioList.hasScenario(scenario));
    assertTrue(scenario.equivalentTo(scenario.canonical()));
  }
  
  @Test
  public void testGetNumberOfScenarios() {
    final ScenarioList scenarioList = new ScenarioList();
    final ElectoralScenario scenario = new ElectoralScenario(Method.STV, false);
    scenario.addOutcome(Outcome.Winner);
    scenarioList.add(scenario);
    assertEquals(1, scenarioList.getNumberOfScenarios(1));
  }
  
  @Test
  public void testHasScenario() {
    final ScenarioList scenarioList = new ScenarioList();
    final ElectoralScenario scenario = new ElectoralScenario(Method.STV, false);
    assertFalse(scenarioList.hasScenario(scenario));
  }
  
}
