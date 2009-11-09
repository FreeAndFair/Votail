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
 
  public static AbstractBallotCounting getAbstractBallotCounting(int n) {
    // TODO Auto-generated method stub
    return new BallotCounting();
  }

  public static byte[] getByteArray() {
    // TODO Auto-generated method stub
    return new byte[0];
  }

  public static Constituency getConstituency(int n) {
    // TODO Auto-generated method stub
    return new Constituency();
  }

  public static Ballot getBallot(int preferenceID) {
    // TODO Auto-generated method stub
    int[] list = new int[1];
    list[0] = preferenceID;
    return new Ballot(list);
  }

  public static Candidate getCandidate(int n) {
    // TODO Auto-generated method stub
    return new Candidate();
  }

  public static BallotBox getBallotBox(int n) {
    // TODO Auto-generated method stub
    return new BallotBox();
  }

  public static int[] getIntArray() {
    // TODO Auto-generated method stub
    return new int[0];
  }

  public static long[] getLongArray() {
    // TODO Auto-generated method stub
    return new long[0];
  }

  public static Decision getDecision(int n) {
    // TODO Auto-generated method stub
    return new Decision();
  }

  public static BallotCounting getBallotCounting(int n) {
    // TODO Auto-generated method stub
    return new BallotCounting();
  }

  public static Object[] getIntArrayAsObject() {
    // TODO Auto-generated method stub
    return new Object[0];
  }

  public static AbstractCountStatus getAbstractCountStatus(int n) {
    // TODO Auto-generated method stub
    BallotCounting ballotCounting = new BallotCounting();
    return ballotCounting.getCountStatus();
  }

}
