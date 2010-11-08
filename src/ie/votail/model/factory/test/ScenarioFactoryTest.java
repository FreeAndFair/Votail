package ie.votail.model.factory.test;

import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;
import junit.framework.TestCase;

import org.junit.Test;

public class ScenarioFactoryTest extends TestCase {

  @Test
  public void testTwoCandidateScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    ScenarioList twoCandidateScenarios = scenarioFactory.find(2);
    assertEquals (4,twoCandidateScenarios.size());
  }
  
  @Test
  public void testThreeCandidateScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    ScenarioList threeCandidateScenarios = scenarioFactory.find(3);
    assertEquals (29,threeCandidateScenarios.size());
  }

  @Test
  public void testFourCandidateScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    ScenarioList threeCandidateScenarios = scenarioFactory.find(4);
    assertEquals (217,threeCandidateScenarios.size());
  }
  
  @Test
  public void testFiveCandidateScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    ScenarioList threeCandidateScenarios = scenarioFactory.find(5);
    assertEquals (1673,threeCandidateScenarios.size());
  }
}
