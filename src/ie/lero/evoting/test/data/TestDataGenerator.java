package ie.lero.evoting.test.data;

import election.tally.AbstractBallotCounting;
import election.tally.AbstractCountStatus;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Constituency;
import election.tally.Decision;

public class TestDataGenerator {
 
  // Singletons
  private static final Decision DECISION = new Decision();
  private static final Constituency CONSTITUENCY = new Constituency();
  private static final Candidate CANDIDATE = new Candidate();
  private static final BallotCounting BALLOT_COUNTING = new BallotCounting();
  private static final BallotBox BALLOT_BOX = new BallotBox();

  public static AbstractBallotCounting getAbstractBallotCounting(int n) {
    return BALLOT_COUNTING;
  }

  public static byte[] getByteArray() {
    return new byte[0];
  }

  public static Constituency getConstituency(int n) {
    return CONSTITUENCY;
  }

  public static Ballot getBallot(int preferenceID) {
    int[] list = new int[1];
    list[0] = preferenceID;
    return new Ballot(list);
  }

  public static Candidate getCandidate(int n) {
    
    return CANDIDATE;
  }

  public static BallotBox getBallotBox(int n) {
    return BALLOT_BOX;
  }

  public static int[] getIntArray() {
    return new int[0];
  }

  public static long[] getLongArray() {
    return new long[0];
  }

  public static Decision getDecision(int n) {
    return DECISION;
  }

  public static BallotCounting getBallotCounting(int n) {
    return BALLOT_COUNTING;
  }

  public static Object[] getIntArrayAsObject() {
    final Object[] intArray = new Object[0];
    return intArray;
  }

  public static AbstractCountStatus getAbstractCountStatus(int n) {
    return BALLOT_COUNTING.getCountStatus();
  }
}
