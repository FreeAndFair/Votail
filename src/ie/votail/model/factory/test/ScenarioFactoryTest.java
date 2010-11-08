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
    assertEquals (4, twoCandidateScenarios.size());
    assertEquals (4, twoCandidateScenarios.getNumberOfScenarios(1));
  }
  
  @Test
  public void testThreeCandidateScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    final int numberOfOutcomes = 3;
    ScenarioList threeCandidateScenarios = scenarioFactory.find(numberOfOutcomes);
    assertEquals (29, threeCandidateScenarios.size());
    assertEquals (15, threeCandidateScenarios.getNumberOfScenarios(1));
    assertEquals (14, threeCandidateScenarios.getNumberOfScenarios(2));
  }

  @Test
  public void testFourCandidateScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    final int numberOfOutcomes = 4;
    ScenarioList candidateScenarios = scenarioFactory.find(numberOfOutcomes);
    assertEquals (217, candidateScenarios.size());
  }
  
  @Test
  public void testFiveCandidateScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    final int numberOfOutcomes = 5;
    ScenarioList candidateScenarios = scenarioFactory.find(numberOfOutcomes);
    assertEquals (1673, candidateScenarios.size());
  }
  
  @Test
  public void testManyCandidateScenarios() {
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    final int numberOfOutcomes = ScenarioList.MAX_PARTITIONS + 1;
    ScenarioList candidateScenarios = scenarioFactory.find(numberOfOutcomes);
    assertEquals (107369,candidateScenarios.size());
    assertEquals (0, candidateScenarios.getNumberOfScenarios(numberOfOutcomes));
  }
}
