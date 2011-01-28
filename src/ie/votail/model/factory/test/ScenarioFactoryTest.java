package ie.votail.model.factory.test;

import ie.votail.model.Method;
import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;
import junit.framework.TestCase;

import org.junit.Test;

public class ScenarioFactoryTest extends TestCase {

  @Test
  public void testTwoCandidateScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    ScenarioList twoCandidateScenarios = scenarioFactory.find(2,1,Method.STV);
    assertEquals (4, twoCandidateScenarios.size());
    assertEquals (4, twoCandidateScenarios.getNumberOfScenarios(1));
  }
  
  @Test
  public void testThreeCandidateScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    final int numberOfOutcomes = 3;
    ScenarioList threeCandidateScenarios = scenarioFactory.find(numberOfOutcomes,1,Method.STV);
    assertEquals (26, threeCandidateScenarios.size());
    assertEquals (12, threeCandidateScenarios.getNumberOfScenarios(1));
    assertEquals (14, threeCandidateScenarios.getNumberOfScenarios(2));
  }

  @Test
  public void testFourCandidateScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    final int numberOfOutcomes = 4;
    ScenarioList candidateScenarios = scenarioFactory.find(numberOfOutcomes,1,Method.STV);
    assertEquals (102, candidateScenarios.size());
  }
  
  @Test
  public void testFiveCandidateScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    final int numberOfOutcomes = 5;
    ScenarioList candidateScenarios = scenarioFactory.find(numberOfOutcomes,1,Method.STV);
    assertEquals (312, candidateScenarios.size());
  }
  
  @Test
  public void testManyCandidateScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    final int numberOfOutcomes = ScenarioList.MAX_PARTITIONS + 1;
    ScenarioList candidateScenarios = scenarioFactory.find(numberOfOutcomes,1,Method.STV);
    assertEquals (1917,candidateScenarios.size());
    assertEquals (154, candidateScenarios.getNumberOfScenarios(numberOfOutcomes));
  }
}
