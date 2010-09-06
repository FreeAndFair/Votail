package ie.lero.evoting.test.data;

public class Outcome {
  
  // Distinct outcomes for each Candidate
  public static int SORE_LOSER = 0;
  public static int TIED_SORE_LOSER = 1;
  public static int EARLY_LOSER = 2;
  public static int TIED_EARLY_LOSER = 3;
  public static int LOSER = 4;
  public static int TIED_LOSER = 5;
  public static int TIED_WINNER = 6;
  public static int COMPROMISE_WINNER = 7;
  public static int QUOTA_WINNER = 8;
  public static int WINNER = 9;
  
  // Number of distinct outcomes
  public static int Radix = WINNER + 1;

  
  private int value;

  // Convert any integer into an outcome
  public Outcome (int outcome) {
    value = outcome % Radix;
  }
  
  public Outcome() {
    value = WINNER;
  }
  
  /**
   * Generate an outcome within a restricted range
   * 
   * @param base The seed value
   * @param minimum The minimum outcome
   * @param maximum The maximum outcome
   */
  /*
   * requires minimum < maximum;
   * requires SORE_LOSER <= minimum;
   * requires maximum <= WINNER;
   */
  
  public Outcome(int base, int minimum, int maximum) {
    value = minimum + base % (1 + maximum - minimum);
  }

  public int getValue() {
    return value;
  }
}
