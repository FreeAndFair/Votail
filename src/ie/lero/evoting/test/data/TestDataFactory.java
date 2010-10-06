package ie.lero.evoting.test.data;

public class TestDataFactory {
  public ScenarioGenerator scenarioGenerator;
  public BallotBoxGenerator ballotBoxGenerator;
  public int numberOfWinners;
  public int numberOfCandidates;
  public String log_filename;
  public String model_filename;

  public TestDataFactory() {
    numberOfWinners = 3;
    numberOfCandidates = 30;
    scenarioGenerator = new ScenarioGenerator(
    numberOfWinners, 
    numberOfCandidates - numberOfWinners);
    model_filename = "models/voting.als";
    log_filename = "BallotBox.log." + System.currentTimeMillis();
    ballotBoxGenerator = new BallotBoxGenerator(model_filename, log_filename);
  }
}