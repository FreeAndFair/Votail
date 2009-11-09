package ie.lero.evoting.test.data;

import election.tally.AbstractBallotCounting;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Constituency;

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

}
