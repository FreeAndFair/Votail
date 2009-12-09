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
import election.tally.CandidateStatus;
import election.tally.Constituency;
import election.tally.CountConfiguration;
import election.tally.Decision;
import election.tally.DecisionStatus;
import election.tally.ElectionStatus;

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
      final BallotCounting ballotCounting = new BallotCounting();
      return ballotCounting;
    }
    throw new java.util.NoSuchElementException();
  }

  public static byte[] getByteArray() {
    final byte[] bytes = {
      DecisionStatus.DEEM_ELECTED,
      DecisionStatus.EXCLUDE,
      DecisionStatus.NO_DECISION,
      ElectionStatus.COUNTING,
      ElectionStatus.EMPTY,
      ElectionStatus.FINISHED,
      ElectionStatus.LOADING,
      ElectionStatus.PRECOUNT,
      ElectionStatus.PRELOAD,
      ElectionStatus.SETTING_UP,
      AbstractCountStatus.ALL_SEATS_FILLED,
      AbstractCountStatus.CANDIDATE_ELECTED,
      AbstractCountStatus.CANDIDATE_EXCLUDED,
      AbstractCountStatus.CANDIDATES_HAVE_QUOTA,
      AbstractCountStatus.END_OF_COUNT,
      AbstractCountStatus.LAST_SEAT_BEING_FILLED,
      AbstractCountStatus.MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS,
      AbstractCountStatus.NO_SEATS_FILLED_YET,
      AbstractCountStatus.NO_SURPLUS_AVAILABLE,
      AbstractCountStatus.ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT,
      AbstractCountStatus.ONE_OR_MORE_SEATS_REMAINING,
      AbstractCountStatus.READY_FOR_NEXT_ROUND_OF_COUNTING,
      AbstractCountStatus.READY_TO_COUNT,
      AbstractCountStatus.READY_TO_MOVE_BALLOTS,
      AbstractCountStatus.SURPLUS_AVAILABLE,
      CandidateStatus.CONTINUING,
      CandidateStatus.ELECTED,
      CandidateStatus.ELIMINATED
      };
    return bytes;
  }

  //@ requires 0 <= n;
  public static Constituency getConstituency(int n) {
    if (constituency_count == 0 | n == 0) {
      constituency_count++;
      return new Constituency();
    }
    throw new java.util.NoSuchElementException();
  }

  //@ requires 0 <= n;
  public static Ballot getBallot(int n) {
    if (ballot_count == 0 || n == 0) {
      ballot_count++;
      int[] list = new int[0];
      return new Ballot(list);
    } else  if (n == 1) {
      int[] list = new int[1];
      list[0] = new Candidate().getCandidateID();
      return new Ballot(list);
    } else if (n < CountConfiguration.MAXCOUNT) {
      int[] list = new int[n];
      for (int preference = 0; preference < n; preference++) {
        list[preference] = new Candidate().getCandidateID();
      }
      return new Ballot(list);
    }
      
      
      throw new java.util.NoSuchElementException();
  }

  //@ requires 0 <= n;
  public static Candidate getCandidate(int n) {
    if (candidate_count == 0 || n == 0) {
      candidate_count++;
      return new Candidate();
    }
    throw new java.util.NoSuchElementException();
  }

  //@ requires 0 <= n;
  public static BallotBox getBallotBox(int n) {
    if (ballotBox_count == 0 || n == 0) {
      ballotBox_count++;
      final BallotBox emptyBallotBox = new BallotBox();
      return emptyBallotBox;
    } else if (n == 1) {
      final BallotBox oneBallotInBox = new BallotBox();
      Candidate firstCandidate = new Candidate();
      int[] list = new int[1];
      list[0] = firstCandidate.getCandidateID();
      oneBallotInBox.accept(list);
      return oneBallotInBox;
    } else if (n == 2) {
      final BallotBox twoBallotsInBox = new BallotBox();
      Candidate firstCandidate = new Candidate();
      Candidate secondCandidate = new Candidate();
      int[] list = new int[2];
      list[0] = firstCandidate.getCandidateID();
      list[1] = secondCandidate.getCandidateID();
      twoBallotsInBox.accept(list);
      list[0] = secondCandidate.getCandidateID();
      list[1] = firstCandidate.getCandidateID();
      twoBallotsInBox.accept(list);
      return twoBallotsInBox;
    }

      throw new java.util.NoSuchElementException();
  }

  public static int[] getIntArray() {
    final int[] integers = {
      AbstractBallotCounting.NONE_FOUND_YET,
      Ballot.MAX_BALLOTS,
      Ballot.NONTRANSFERABLE,
      Candidate.MAX_CANDIDATES,
      Candidate.NO_CANDIDATE,
      CountConfiguration.MAXCOUNT,
      CountConfiguration.MAXVOTES,
      Decision.MAX_DECISIONS
    };
    return integers;
  }

  public static long[] getLongArray() {
    return new long[0];
  }

  //@ requires 0 <= n;
  public static Decision getDecision(int n) {
    if (decision_count == 0 || n == 0) {
      decision_count++;
      return new Decision();
    }
    throw new java.util.NoSuchElementException();
  }

  //@ requires 0 <= n;
  public static BallotCounting getBallotCounting(int n) {
    if (ballotCounting_count == 0 || n == 0) {
      ballotCounting_count++;
      return new BallotCounting();
    }
    throw new java.util.NoSuchElementException();
  }

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
    }
    throw new java.util.NoSuchElementException();
  }
}
