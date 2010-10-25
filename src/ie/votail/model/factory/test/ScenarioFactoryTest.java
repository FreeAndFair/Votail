package ie.votail.model.factory.test;

import static org.junit.Assert.*;
import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;

import org.junit.Test;

public class ScenarioFactoryTest {

  @Test
  public void testTwoCandidateScenarios() {
    ScenarioList twoCandidateScenarios = ScenarioFactory.find(2);
    assertEquals (twoCandidateScenarios.size(),4);
  }
  
  @Test
  public void testThreeCandidateScenarios() {
    ScenarioList threeCandidateScenarios = ScenarioFactory.find(3);
    assertEquals (threeCandidateScenarios.size(),26);
  }

}
