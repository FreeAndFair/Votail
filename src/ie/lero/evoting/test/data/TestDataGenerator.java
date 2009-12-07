package ie.lero.evoting.test.data;

// December 2009
// Dermot Cochran and Joseph R. Kiniry
// Lero Graduate School of Software Engineering, Ireland
// CASL, University College Dublin, Ireland
// IT University of Copenhagen, Denmark

import election.tally.AbstractBallotCounting;
import election.tally.AbstractCountStatus;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Constituency;
import election.tally.Decision;

public class TestDataGenerator {
 
  private static int abstractBallotCounting_count = 0;
  private static int abstractCountStatus_count = 0;
  private static int ballot_count = 0;
  private static int ballotBox_count = 0;
  private static int ballotCounting_count = 0;
  private static int candidate_count = 0;
  private static int constituency_count = 0;
  private static int decision_count = 0;

  //@ requires 0 <= n;
  public static AbstractBallotCounting getAbstractBallotCounting(int n) {
    if (abstractBallotCounting_count == 0 || n == 0) {
      abstractBallotCounting_count++;
      return new BallotCounting();
    } else throw new java.util.NoSuchElementException();
  }

  public static byte[] getByteArray() {
    return new byte[0];
  }

  //@ requires 0 <= n;
  public static Constituency getConstituency(int n) {
    if (constituency_count == 0 | n == 0) {
      constituency_count++;
      return new Constituency();
    } else throw new java.util.NoSuchElementException();
  }

  //@ requires 0 <= n;
  public static Ballot getBallot(int n) {
    if (ballot_count == 0 || n == 0) {
      ballot_count++;
      int[] list = new int[1];
      list[0] = n;
      return new Ballot(list);
    } else throw new java.util.NoSuchElementException();
  }

  //@ requires 0 <= n;
  public static Candidate getCandidate(int n) {
    if (candidate_count == 0 || n == 0) {
      candidate_count++;
      return new Candidate();
    } else throw new java.util.NoSuchElementException();
  }

  //@ requires 0 <= n;
  public static BallotBox getBallotBox(int n) {
    if (ballotBox_count == 0 || n == 0) {
      ballotBox_count++;
      return new BallotBox();
    } else throw new java.util.NoSuchElementException();
  }

  public static int[] getIntArray() {
    return new int[0];
  }

  public static long[] getLongArray() {
    return new long[0];
  }

  //@ requires 0 <= n;
  public static Decision getDecision(int n) {
    if (decision_count == 0 || n == 0) {
      decision_count++;
      return new Decision();
    } else throw new java.util.NoSuchElementException();
  }

  //@ requires 0 <= n;
  public static BallotCounting getBallotCounting(int n) {
    if (ballotCounting_count == 0 || n == 0) {
      ballotCounting_count++;
      return new BallotCounting();
    } else throw new java.util.NoSuchElementException();
  }

  //@ requires 0 <= n;
  public static Object[] getIntArrayAsObject() {
    final Object[] intArray = new Object[0];
    return intArray;
  }

  //@ requires 0 <= n;
  public static AbstractCountStatus getAbstractCountStatus(int n) {
    if (abstractCountStatus_count == 0 || n == 0) {
      abstractCountStatus_count++;
      BallotCounting ballotCounting = new BallotCounting();
      return ballotCounting.getCountStatus();
    } else throw new java.util.NoSuchElementException();
  }
}
