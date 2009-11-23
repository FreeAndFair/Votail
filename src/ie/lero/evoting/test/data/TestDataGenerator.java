package ie.lero.evoting.test.data;

import java.util.ArrayList;

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
  private static final BallotCounting BALLOT_COUNTING = new BallotCounting();
  private static final BallotBox BALLOT_BOX = new BallotBox();
  
  // Dynamic Arrays
  static ArrayList<Candidate> candidateList = new ArrayList<Candidate>();

  public static AbstractBallotCounting getAbstractBallotCounting(int n) {
    return BALLOT_COUNTING;
  }

  public static byte[] getByteArray() {
    return new byte[0];
  }

  public static Constituency getConstituency(int n) {
    return new Constituency();
  }

  public static Ballot getBallot(int preferenceID) {
    int[] list = new int[1];
    list[0] = preferenceID;
    return new Ballot(list);
  }

  public static Candidate getCandidate(int n) {
    while (candidateList.size() < n) {
      candidateList.add(new Candidate());
    }
    return candidateList.get(n);
  }

  public static BallotBox getBallotBox(int n) {
    // default
    return BALLOT_BOX;
  }

  public static int[] getIntArray() {
    return new int[0];
  }

  public static long[] getLongArray() {
    return new long[0];
  }

  public static Decision getDecision(int n) {
    final Decision decision = new Decision();
    switch (n) {
      case 1: decision.setDecisionType(Decision.DEEM_ELECTED); 
      case 2: decision.setDecisionType(Decision.EXCLUDE); break;
      default: decision.setDecisionType(Decision.NO_DECISION);
    }
    decision.setCountNumber(n);
    decision.setCandidate(getCandidate(n).getCandidateID());
    return decision;
  }

  public static BallotCounting getBallotCounting(int n) {
    // default
    return BALLOT_COUNTING;
  }

  public static Object[] getIntArrayAsObject() {
    final Object[] intArray = new Object[0];
    return intArray;
  }

  public static AbstractCountStatus getAbstractCountStatus(int n) {
    // default
    return BALLOT_COUNTING.getCountStatus();
  }
}
