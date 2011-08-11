package ie.votail.model.factory.test;

import ie.votail.model.Method;
import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;
import junit.framework.TestCase;

import org.junit.Test;

public class ScenarioFactoryTest extends TestCase {
  
  
  public void testTwoCandidateScenarios() {
    final ScenarioFactory scenarioFactory = new ScenarioFactory();
    final ScenarioList twoCandidateScenarios = scenarioFactory.find(2, 1, Method.STV);
    assertEquals(4, twoCandidateScenarios.size());
    assertEquals(4, twoCandidateScenarios.getNumberOfScenarios(1));
  }
  
  @Test
  public void testThreeCandidateScenarios() {
    final ScenarioFactory scenarioFactory = new ScenarioFactory();
    final ScenarioList threeCandidateScenarios =
        scenarioFactory.find(3, 1, Method.STV);
    assertEquals(52, threeCandidateScenarios.size());
    assertEquals(38, threeCandidateScenarios.getNumberOfScenarios(1));
    assertEquals(14, threeCandidateScenarios.getNumberOfScenarios(2));
  }
  
  @Test
  public void testFourCandidateScenarios() {
    final ScenarioFactory scenarioFactory = new ScenarioFactory();
    ScenarioList candidateScenarios =
        scenarioFactory.find(4, 1, Method.STV);
    assertEquals(367, candidateScenarios.size());
  }
  
  @Test
  public void testFiveCandidateScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    final int numberOfCandidates = 5;
    ScenarioList candidateScenarios =
        scenarioFactory.find(numberOfCandidates, 1, Method.STV);
    assertEquals(1863, candidateScenarios.size());
  }
  
  @Test
  public void testFiveCandidateTwoSeatScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    final int numberOfCandidates = 5;
    ScenarioList candidateScenarios =
        scenarioFactory.find(numberOfCandidates, 2, Method.STV);
    assertEquals(1863, candidateScenarios.size());
    assertEquals(0, candidateScenarios.getNumberOfScenarios(numberOfCandidates));
  }
  
  
}
