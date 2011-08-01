package ie.lero.evoting.test.data;

// (c) Copyright 2009, LGSSE and University College Dublin, Ireland
// (c) Copyright 2010, IT University of Copenhagen, Denmark
// (c) Copyright 2009-2010 Dermot Cochran and Joseph R. Kiniry
// (c) Dermot Cochran, 2010-2011, IT University of Copenhagen

import election.tally.AbstractBallotCounting;
import election.tally.AbstractCountStatus;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.CandidateStatus;
import election.tally.Constituency;
import election.tally.CountConfiguration;
import election.tally.ElectionStatus;

public final class TestDataGenerator {

  /**
   * 
   */
  private TestDataGenerator() {
    super();
  }

  // Maximum number of ballot boxes that can be held in memory
  private static final int MEMORY_LIMIT = 1000000000;
  
  private static int abstractBallotCounting_count = 0;
  private static int abstractCountStatus_count = 0;
  private static int ballot_count = 0;
  private static int ballotBox_count = 0;
  private static int ballotCounting_count = 0;
  private static int candidate_count = 0;
  private static int constituency_count = 0;

  /**
   * AbstractBallotCounting is a top level class; it is extended by
   * BallotCouting but is neither used as a field nor a formal parameter in any
   * other class.
   */
  //@ requires 0 <= number;
  public static AbstractBallotCounting getAbstractBallotCounting(final int number) 
    throws java.util.NoSuchElementException {
    if (abstractBallotCounting_count == 0 || number == 0) {
      abstractBallotCounting_count++;
      return new BallotCounting();
    }
    throw new java.util.NoSuchElementException();
  }

  public static byte[] getByteArray() {
    final byte[] bytes =
                         {
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
                          CandidateStatus.CONTINUING, CandidateStatus.ELECTED,
                          CandidateStatus.ELIMINATED };
    return bytes;
  }

  //@ requires 0 <= number;
  public static Constituency getConstituency(final int number) {
    if (constituency_count == 0 || number == 0) {
      constituency_count++;
      final Constituency constituency = new Constituency();
      constituency.setNumberOfSeats(1, 5);
      constituency.setNumberOfCandidates(3);
      return constituency;
    } else if (number <= 3) {
      final Constituency constituency = new Constituency();
      constituency.setNumberOfSeats(number, 3);
      constituency.setNumberOfCandidates(number + 2);
      return constituency;
    } else if (number <= 5) {
      final Constituency constituency = new Constituency();
      constituency.setNumberOfSeats(number, 5);
      constituency.setNumberOfCandidates(number + 1);
      return constituency;
    } else if (number == 6) {
      final Constituency constituency = new Constituency();
      constituency.setNumberOfSeats(1, 4);
      constituency.setNumberOfCandidates(number);
      return constituency;
    } else if (number == 7) {
      final Constituency constituency = new Constituency();
      constituency.setNumberOfSeats(2, 4);
      constituency.setNumberOfCandidates(number);
      return constituency;
    } else if (number == 8) {
      final Constituency constituency = new Constituency();
      constituency.setNumberOfSeats(3, 4);
      constituency.setNumberOfCandidates(number);
      return constituency;
    } else if (number == 9) {
      final Constituency constituency = new Constituency();
      constituency.setNumberOfSeats(4, 4);
      constituency.setNumberOfCandidates(number);
      return constituency;
    } else if (number == 10) {
      final Constituency constituency = new Constituency();
      constituency.setNumberOfSeats(2, 5);
      constituency.setNumberOfCandidates(number);
      return constituency;
    } else if (number == 11) {
      final Constituency constituency = new Constituency();
      constituency.setNumberOfSeats(3, 5);
      constituency.setNumberOfCandidates(number);
      return constituency;
    } else if (number == 12) {
      final Constituency constituency = new Constituency();
      constituency.setNumberOfSeats(5, 5);
      constituency.setNumberOfCandidates(Candidate.MAX_CANDIDATES);
      return constituency;
    } else if (number == 13) {
      final Constituency constituency = new Constituency();
      constituency.setNumberOfSeats(4, 4);
      constituency.setNumberOfCandidates(Candidate.MAX_CANDIDATES - 1);
      return constituency;
    }
    throw new java.util.NoSuchElementException();
  }

  //@ requires 0 <= number;
  public static Ballot getBallot(final int number) {
    if (ballot_count == 0 || number == 0) {
      ballot_count++;
      return new Ballot(new int[0]);
    } else if (number < Candidate.MAX_CANDIDATES) {
      int[] list = new int[number];
      for (int i=0; i<number; i++) {
        list[i] = new Candidate().getCandidateID();
      }
      return new Ballot(list);
    }
    throw new java.util.NoSuchElementException();
  }

  //@ requires 0 <= number;
  public static Candidate getCandidate(final int number) {
    if (candidate_count == 0 || number == 0) {
      candidate_count++;
      return new Candidate();
    }
    throw new java.util.NoSuchElementException();
  }

  //@ requires 0 <= number;
  public static BallotBox getBallotBox (final int number) {
    if (ballotBox_count < MEMORY_LIMIT) {
      ballotBox_count++;
      if (number == 0) {
        return new BallotBox();
      } else if (number == 1) {
        final BallotBox oneBallotInBox = new BallotBox();
        final Candidate firstCandidate = new Candidate();
        int[] list = new int[1];
        list[0] = firstCandidate.getCandidateID();
        oneBallotInBox.accept(list);
        return oneBallotInBox;
      } else if (number == 2) {
        final BallotBox twoBallotsInBox = new BallotBox();
        final Candidate firstCandidate = new Candidate();
        final Candidate secondCandidate = new Candidate();
        int[] list = new int[2];
        list[0] = firstCandidate.getCandidateID();
        list[1] = secondCandidate.getCandidateID();
        twoBallotsInBox.accept(list);
        list[0] = secondCandidate.getCandidateID();
        list[1] = firstCandidate.getCandidateID();
        twoBallotsInBox.accept(list);
        return twoBallotsInBox;
      }
      // Two way ties
      else if (number == 3) {
        final BallotBox ballotBox = new BallotBox();
        final Candidate candidate1 = new Candidate();
        final Candidate candidate2 = new Candidate();
        final Candidate candidate3 = new Candidate();
        int[] list = new int[3];

        // First ballot
        list[0] = candidate1.getCandidateID();
        list[1] = candidate2.getCandidateID();
         ballotBox.accept(list);

        // Second ballot
        list[0] = candidate3.getCandidateID();
        list[1] = candidate2.getCandidateID();
         ballotBox.accept(list);
        return ballotBox;
      }
      // Three way ties
      else if (number == 4) {
        final BallotBox ballotBox = new BallotBox();
        final Candidate candidate1 = new Candidate();
        Candidate candidate2 = new Candidate();
        Candidate candidate3 = new Candidate();
        int[] list = new int[4];

        // First ballot
        list[0] = candidate1.getCandidateID();
        list[1] = candidate2.getCandidateID();
        list[2] = candidate3.getCandidateID();
        ballotBox.accept(list);

        // Second ballot
        list[0] = candidate2.getCandidateID();
        list[1] = candidate3.getCandidateID();
        ballotBox.accept(list);

        // Last ballot
        list[0] = candidate3.getCandidateID();
        ballotBox.accept(list);

        return ballotBox;
      }
    }
    throw new java.util.NoSuchElementException();
  }

  public static int[] getIntArray() {
    final int[] integers =
                           { AbstractBallotCounting.NONE_FOUND_YET,
                            Ballot.MAX_BALLOTS, Ballot.NONTRANSFERABLE,
                            Candidate.MAX_CANDIDATES, Candidate.NO_CANDIDATE,
                            CountConfiguration.MAXCOUNT,
                            CountConfiguration.MAXVOTES };
    return integers;
  }

  public static long[] getLongArray() {
    return new long[0];
  }

  /**
   * BallotCounting is the top level object in the system; it is neither a field
   * nor a formal parameter for any other object.
   * 
   * @param number
   * @return A Ballot Counting object
   */
  //@ requires 0 <= n;
  public static BallotCounting getBallotCounting(final int number) {
    if (ballotCounting_count == 0 || number == 0) {
      ballotCounting_count++;
      return new BallotCounting();
    }
    throw new java.util.NoSuchElementException();
  }

  public static Object[] getIntArrayAsObject() {
    return new Object[0];
  }

  //@ requires 0 <= number;
  public static AbstractCountStatus getAbstractCountStatus(int number) {
    if (abstractCountStatus_count == 0 || number == 0) {
      abstractCountStatus_count++;
      BallotCounting ballotCounting = new BallotCounting();
      return ballotCounting.getCountStatus();
    }
    throw new java.util.NoSuchElementException();
  }
}
