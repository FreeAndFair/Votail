package ie.votail.model.factory.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import ie.votail.model.Method;
import ie.votail.model.Outcome;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.factory.ScenarioList;

import org.junit.Test;

public class ScenarioListTest {
  
  @Test
  public void testAddScenario() {
    ScenarioList scenarioList = new ScenarioList();
    ElectoralScenario scenario = new ElectoralScenario(Method.STV, false);
    scenarioList.add(scenario);
    scenarioList.add(scenario.canonical());
    boolean addDuplicate = scenarioList.add(scenario);
    assertFalse(addDuplicate);
    assertTrue(scenarioList.hasScenario(scenario));
    assertTrue(scenario.equivalentTo(scenario.canonical()));
  }
  
  @Test
  public void testGetNumberOfScenarios() {
    ScenarioList scenarioList = new ScenarioList();
    ElectoralScenario scenario = new ElectoralScenario(Method.STV, false);
    scenario.addOutcome(Outcome.Winner);
    scenarioList.add(scenario);
    assertEquals(1, scenarioList.getNumberOfScenarios(1));
  }
  
  @Test
  public void testHasScenario() {
    ScenarioList scenarioList = new ScenarioList();
    ElectoralScenario scenario = new ElectoralScenario(Method.STV, false);
    assertFalse(scenarioList.hasScenario(scenario));
  }
  
}
