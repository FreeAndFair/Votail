package ie.lero.evoting.test.data;

public class Scenario {
  public static int EFFECTIVE_CANDIDATES = 5;
  Outcome[] outcomes;
  private int length;

  public Scenario (int numberOfCandidates) {
    outcomes = new Outcome[numberOfCandidates];
    length = numberOfCandidates;
  }
  
  public void generate (int seed) {
    int base = 1;
    for (int i=0;i < length; i++) {
      outcomes[i] = new Outcome ((seed % (Outcome.Radix * base)) / base); 
      base *= Outcome.Radix;
    }
  }
}
