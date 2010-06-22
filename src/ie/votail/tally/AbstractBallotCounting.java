package ie.votail.tally;

//@ refine "AbstractBallotCounting.jml";

/**
 * Ballot counting algorithm for elections to Oireachtas Eireann - the National
 * Parliament of Ireland.
 * 
 * @author Dermot Cochran
 * (c) 2005-2009 Dermot Cochran
 * Permission is hereby granted, free of charge, to any person obtaining
 *          a copy of this software and associated documentation files (the
 *          "Software"), to deal in the Software without restriction, including
 *          without limitation the rights to use, copy, modify, merge, publish,
 *          distribute, sublicense, and/or sell copies of the Software, and to
 *          permit persons to whom the Software is furnished to do so, subject
 *          to the following conditions: The above copyright notice and this
 *          permission notice shall be included in all copies or substantial
 *          portions of the Software. THE SOFTWARE IS PROVIDED "AS IS", WITHOUT
 *          WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
 *          TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR
 *          PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 *          COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 *          LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
 *          ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE
 *          OR OTHER DEALINGS IN THE SOFTWARE.
 * This work was supported, in part, by Science Foundation Ireland
 *           grant 03/CE2/I303_1 to Lero - the Irish Software Engineering
 *           Research Centre (www.lero.ie) and, in part, by the European Project
 *           Mobius IST 15909 within the IST 6th Framework. This software
 *           reflects only the authors' views and the European Community is not
 *           liable for any use that may be made of the information contained
 *           therein.
 * @see <a href="http://www.irishstatuebook.ie/1992_23.html">Part XIX of the
 *      Electoral Act, 1992</a>
 * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_2.pdf">Department of
 *      Environment and Local Government: Count Requirements and Commentary on
 *      Count Rules, sections 3-16</a>
 * @see <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 *      Formal Verification of Voting</a>
 * @see <a href="http://www.jmlspecs.org/">JML Homepage</a>
 */
public abstract class AbstractBallotCounting extends ElectionStatus {

  public static final int                         NONE_FOUND_YET = -1;

  /** List of candidates for election */
  protected transient/*@ spec_public @*/ Candidate[] candidates = new Candidate[0];
  //@ protected represents candidateList <- candidates;

  /** List of contents of each ballot paper that will be counted. */
  protected transient /*@ spec_public @*/ Ballot[] ballots = new Ballot[0];
  // TODO public invariant ballots.owner == this;
  //@ protected represents ballotsToCount <- ballots;

  /** Total number of candidates for election */
  protected transient/*@ spec_public @*/ int totalNumberOfCandidates;
  //@ public represents totalCandidates <- totalNumberOfCandidates;

  /** Number of candidates elected so far */
  protected transient/*@ spec_public @*/ int numberOfCandidatesElected;
  //@ public represents numberElected <- numberOfCandidatesElected;

  /** Number of candidates excluded from election so far */
  protected transient/*@ spec_public @*/ int numberOfCandidatesEliminated;
  //@ public represents numberEliminated <- numberOfCandidatesEliminated;

  /** Number of seats in this election */
  protected transient/*@ spec_public @*/ int numberOfSeats;
  //@ public represents seats <- numberOfSeats;

  /** Number of seats in this constituency */
  protected transient int totalNumberOfSeats;
  //@ protected represents totalSeats <- totalNumberOfSeats;

  /** Total number of valid ballot papers */
  protected/*@ spec_public @*/transient int         totalNumberOfVotes;
  //@ protected represents totalVotes <- totalNumberOfVotes;

  /** Number of votes needed to save deposit unless elected */
  protected transient/*@ spec_public @*/int         savingThreshold;
  //@ protected represents depositSavingThreshold <- savingThreshold;

  /** Number of rounds of counting so far. */
  protected transient/*@ spec_public @*/int         countNumberValue;
  //@ protected represents countNumber <- countNumberValue;

  /** Number of seats remaining to be filled */
  protected transient/*@ spec_public @*/int         totalRemainingSeats;
  /*@ protected represents remainingSeats <- 
    @           numberOfSeats - numberOfCandidatesElected;
    @*/

  /**
   * Default Constructor.
   */
  /*@ also
    @   public normal_behavior
    @     assignable state, countNumber, numberElected, numberEliminated,
    @       countNumberValue, numberOfCandidatesElected, seats, numberOfSeats,
    @       totalVotes, numberOfCandidatesEliminated, totalNumberOfVotes;
    @     ensures state == ElectionStatus.EMPTY;
    @     ensures countNumber == 0;
    @     ensures numberElected == 0;
    @*/
  public AbstractBallotCounting() {
    super();
    status = ElectionStatus.EMPTY;
    countNumberValue = 0;
    numberOfCandidatesElected = 0;
    numberOfCandidatesEliminated = 0;
    totalNumberOfVotes = 0;
    numberOfSeats = 0;
  }

  /**
   * Determine if the candidate has enough votes to be elected.
   * 
   * @param candidate
   *        The candidate in question
   * @return True if the candidate has at least a quota of votes
   * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_1.pdf"> CEV guidelines,
   *      page 79, paragraph 120(2)</a> <BON>query
   *      "Has the candidate at least a quota of votes?"</BON>
   */
  /*@ also
    @   public normal_behavior
    @     requires 0 <= countNumber;
    @     requires \nonnullelements (candidateList);
    @     requires \nonnullelements (ballotsToCount);
    @     ensures \result <==> 
    @       (countBallotsFor(candidate.getCandidateID()) >= getQuota());
    @*/
  public/*@ pure @*/boolean hasQuota(final/*@ non_null @*/Candidate candidate) {
    // TODO 2009.10.14 ESC precondition violation warning
    return (countBallotsFor(candidate.getCandidateID()) >= getQuota()); //@ nowarn;
  }

  /**
   * Determine if the candidate was elected in any previous round <BON>query
   * "Has the candidate been elected?"</BON>
   * 
   * @param candidate
   *        The candidate
   * @return True if the candidate has already been elected
   */
  /*@ also
    @   protected normal_behavior
    @     requires candidate != null;
    @     ensures (\result == true) <==>
    @       (candidate.getStatus() == Candidate.ELECTED || hasQuota(candidate));
    @*/
  public/*@ pure @*/boolean isElected(final Candidate candidate) {
    return ((candidate.getStatus() == CandidateStatus.ELECTED) || hasQuota(candidate));
  }

  /**
   * Determine how many surplus votes a candidate has. <BON>query
   * "How many surplus votes does this candidate have?"</BON>
   * 
   * <p> The surplus is the maximum number of votes available for transfer
   * @param candidate
   *        The candidate record
   * @return The undistributed surplus for that candidate, or zero if the
   *         candidate has less than a quota of votes
   * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_1.pdf">CEV guidelines,
   *      page 79, paragraph 120(2)</a>
   */
  /*@ also
    @   public normal_behavior
    @     requires 0 <= countNumber;
    @     requires PRECOUNT <= state;
    @     requires \nonnullelements (ballotsToCount);
    @     ensures (hasQuota(candidate) == true) ==> \result ==
    @       (countBallotsFor(candidate.getCandidateID()) - getQuota());
    @     ensures (hasQuota(candidate) == false) ==> \result == 0;
    @     ensures 0 <= \result;
    @*/
  public/*@ pure @*/int getSurplus(final/*@ non_null @*/Candidate candidate) {
    // TODO 2009.10.14 ESC precondition violation warning
    final int surplus = countBallotsFor(candidate.getCandidateID()) - getQuota(); //@ nowarn;
    if (surplus < 0) {
      return 0;
    }
    return surplus;
  }

  /**
   * How many surplus votes are available for distribution?
   * 
   * @return The total number of surplus votes for all candidates.
   */
  public final/*@ pure @*/int getTotalSumOfSurpluses() {
    int sumOfSurpluses = 0;

    for (int c = 0; c < totalNumberOfCandidates; c++) {
      final int surplus = getSurplus(candidates[c]);
      if (surplus > 0) {
        sumOfSurpluses += surplus;
      }
    }
    return sumOfSurpluses;
  }

  /**
   * Determine if the candidate has enough votes to save his or her deposit.
   * <BON>query "Has this candidate saved his or her deposit?"</BON>
   * 
   * <p> The deposit saving threshold is one plus one quarter of the full
   *         quota
   * <p> This needs to be checked just before the candidate is eliminated to
   *         include all transfers received before the candidate was either
   *         elected or eliminated
   * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_2.pdf">CEV commentary on
   *      count rules, section 3 page 13, section 4 page 17 and section 14</a>
   * @param index
   *        The candidate for which to check
   * @return true if candidate has enough votes to save deposit
   */
  /*@ also
    @     requires (state == COUNTING) || (state == FINISHED);
    @     requires \nonnullelements (candidateList);
    @     requires 0 <= index;
    @     requires index < totalNumberOfCandidates;
    @     requires index < candidateList.length;
    @     ensures \result <==> 
    @       (candidateList[index].getOriginalVote() >= depositSavingThreshold) ||
    @       (isElected (candidateList[index]) == true);
    @*/
  public/*@ pure @*/boolean isDepositSaved(final int index) {
    // TODO 2009.10.14 ESC negative index warning
    final Candidate candidate = candidates[index]; //@ nowarn;
    // TODO 2009.10.14 ESC precondition warning
    final int originalVote = candidate.getOriginalVote(); //@ nowarn;
    final boolean elected = isElected(candidate);
    return ((originalVote >= savingThreshold) || elected);
  }

  /**
   * Redistribute ballots from the highest available surplus.
   * 
   * @param candidateWithSurplus
   *        The elected candidate with highest surplus
   * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_2.pdf"> CEV Commentary on
   *      Count Rules, section 12, page 47</a>
   */
  /*@ also
    @   protected normal_behavior
    @   requires getSurplus (candidateList[candidateWithSurplus]) > 0;
    @   requires state == COUNTING;
    @   requires getNumberContinuing() > remainingSeats;
    @   assignable candidates;
    @   ensures getSurplus (candidateList[candidateWithSurplus]) == 0;
    @*/
  public abstract void distributeSurplus(int candidateWithSurplus);

  /**
   * Load candidate details and number of seats.
   * 
   * @param constituency
   *        The candidate details and number of seats
   */
  /*@ also
    @   protected normal_behavior
    @     requires state == EMPTY;
    @     requires 0 <= constituency.getNumberOfCandidates();
    @     assignable status; 
    @     assignable totalNumberOfCandidates;
    @     assignable numberOfSeats, totalRemainingSeats;
    @     assignable totalNumberOfSeats;
    @     assignable candidates;
    @     ensures state == PRELOAD;
    @     ensures totalCandidates == constituency.getNumberOfCandidates();
    @     ensures seats == constituency.getNumberOfSeatsInThisElection();
    @     ensures totalSeats == constituency.getTotalNumberOfSeats();
    @     ensures totalCandidates == candidateList.length;
    @     ensures \nonnullelements (candidateList);
    @*/
  public void setup(final/*@ non_null @*/ Constituency constituency) {
    this.totalNumberOfCandidates = constituency.getNumberOfCandidates();
    this.numberOfSeats = constituency.getNumberOfSeatsInThisElection();
    this.totalNumberOfSeats = constituency.getTotalNumberOfSeats();
    this.status = PRELOAD;
    candidates = new Candidate[this.totalNumberOfCandidates];
    for (int i = 0; i < candidates.length; i++) {
      // TODO 2009.10.14 ESC precondition
      this.candidates[i] = constituency.getCandidate(i); //@ nowarn;
    }
    this.totalRemainingSeats = this.numberOfSeats;
    // TODO 2009.10.14 ESC postcondition
  } //@ nowarn;

  /**
   * Open the ballot box for counting.
   * 
   * @param ballotBox
   *        The ballots to be counted, already "shuffled and mixed".
   */
  /*@ also
    @   protected normal_behavior
    @     requires state == PRELOAD;
    @     assignable state, totalVotes, ballotsToCount, ballots;
    @     assignable totalNumberOfVotes;
    @     ensures state == PRECOUNT;
    @     ensures totalVotes == ballotBox.numberOfBallots;
    @     ensures totalVotes == ballotsToCount.length;
    @*/
  public void load(final/*@ non_null @*/BallotBox ballotBox) {
    totalNumberOfVotes = ballotBox.size();
    ballots = new Ballot[totalNumberOfVotes];
    int index = 0;
    // TODO 2009.10.14 ESC invariant violation
    while (ballotBox.isNextBallot()) { //@ nowarn;
      // TODO 2009.10.14 ESC precondition warning
      ballots[index++] = ballotBox.getNextBallot(); //@ nowarn;
    }
    status = PRECOUNT;

    // Number of first preferences for each candidate
    // TODO 2009.10.15 ESC precondition warning
    calculateFirstPreferences(); //@ nowarn;
    // TODO 2009.10.15 ESC postcondition warning
  } //@ nowarn;

  /**
   * Droop quota; number of votes needed to guarantee election.
   * 
   * @return Number of votes required to ensure election
   */
  public/*@ pure @*/int getQuota() {
    return 1 + (totalNumberOfVotes / (1 + numberOfSeats));
  }

  /**
   * Calculate the first preference counts for each candidate.
   */
  //@ requires PRECOUNT <= state;
  //@ requires \nonnullelements (candidateList);
  //@ requires \nonnullelements (ballotsToCount);
  //@ assignable candidates[*];
  protected void calculateFirstPreferences() {
    for (int c = 0; c < candidates.length; c++) {
        final int candidateID = candidates[c].getCandidateID();
        final int numberOfBallotsInPile = countFirstPreferences(candidateID);
        if (0 < numberOfBallotsInPile) {
          // TODO 2009.10.14 ESC warning
          candidates[c].addVote(numberOfBallotsInPile, countNumberValue); //@ nowarn;
        }
      
    }
  }

  /**
   * Count the number of ballots in the pile for this candidate.
   * 
   * @param candidateID
   *        The internal identifier of this candidate
   * @return The number of ballots in this candidate's pile
   */
  //@ also requires \nonnullelements (ballotsToCount);
  public/*@ pure @*/int countBallotsFor(final int candidateID) {
    int numberOfBallots = 0;
    for (int b = 0; b < ballots.length; b++) {
      //@ assert ballots[b] != null;
      if (ballots[b].isAssignedTo(candidateID)) {
        numberOfBallots++;
      }
    }
    return numberOfBallots;
  }

  /**
   * Count the number of first preferences for this candidate.
   * 
   * @param candidateID
   *        The internal identifier of this candidate
   * @return The number of ballots in this candidate's pile
   */
  /*@ requires PRECOUNT <= state;
    @ requires \nonnullelements (ballotsToCount);
    @ ensures 0 <= \result;
    @ ensures \result <= ballotsToCount.length;
    @*/
  public/*@ pure @*/int countFirstPreferences(final int candidateID) {
    int numberOfBallots = 0;
    for (int b = 0; b < ballots.length; b++) {
      //@ assert ballots[b] != null;
      if (ballots[b].isFirstPreference(candidateID)) {
        numberOfBallots++;
      }
    }
    return numberOfBallots;
  }

  /**
   * Gets the potential number of transfers from one candidate to another.
   * 
   * <p> This method is needed to get the proportions to use when
   *         transferring surplus votes
   * @param fromCandidate
   *        Candidate from which to check the transfers
   * @param toCandidateID
   *        Candidate ID to check for receipt of transferred votes
   * @return Number of votes potentially transferable from this candidate to
   *         that candidate
   */
  /*@ also
    @   requires \nonnullelements (ballotsToCount);
    @   ensures \result== (\num_of int j; 0 <= j && j < totalVotes;
    @     (ballotsToCount[j].isAssignedTo(fromCandidate.getCandidateID())) &&
    @     (getNextContinuingPreference(ballotsToCount[j]) == toCandidateID));
    @*/
  protected/*@ pure spec_public @*/int getPotentialTransfers(
                                                              final Candidate fromCandidate,
                                                              final int toCandidateID) {
    int numberOfBallots = 0;
    // TODO 2009.10.14 ESC null reference warnings
    for (int j = 0; j < ballots.length; j++) { //@ nowarn;
      if (ballots[j].isAssignedTo(fromCandidate.getCandidateID()) //@ nowarn;
          && (getNextContinuingPreference(ballots[j]) == toCandidateID)) {
        numberOfBallots++;
      }

    }
    return numberOfBallots;
    // TODO 2009.10.15 ESC postcondition warning
  } //@ nowarn;

  /**
   * Gets the status of the algorithm in progress.
   * 
   * @return The state variable value {@link #EMPTY}, {@link #SETTING_UP},
   *         {@link #PRELOAD}, {@link #LOADING}, {@link #PRECOUNT},
   *         {@link #COUNTING}, {@link #FINISHED}
   */
  /*@ also
    @   protected normal_behavior
    @   ensures \result == state;
    @*/
  public /*@ pure @*/ byte getStatus() {
    return status;
  }

  /**
   * Gets the next preference continuing candidate.
   * 
   * @param ballot
   *        Ballot paper from which to get the next preference
   * @return Internal ID of next continuing candidate or
   *         <code>NONTRANSFERABLE</code>
   */
  protected/*@ pure spec_public @*/int getNextContinuingPreference(
                                                                    final/*@ non_null @*/Ballot ballot) {

    for (int i = 1; i <= ballot.remainingPreferences(); i++) {
      final int nextPreference = ballot.getNextPreference(i);
      if (isContinuingCandidateID(nextPreference)) {
        return nextPreference;
      }
    }

    return Ballot.NONTRANSFERABLE;
  }

  /**
   * Determine if a candidate ID belongs to a continuing candidate.
   * 
   * @param candidateID
   *        The ID of candidate for which to check the status
   * @return <code>true</code> if this candidate ID matches that of a continuing
   *         candidate
   */
  /*@ also
    @   requires \nonnullelements (candidateList);
    @   ensures \result == (\exists int i;
    @     0 <= i && i < candidateList.length;
    @     candidateID == candidateList[i].getCandidateID() &&
    @     candidateList[i].getStatus() == CandidateStatus.CONTINUING);
    @*/
  public/*@ pure @*/boolean isContinuingCandidateID(final int candidateID) {
    for (int i = 0; i < candidates.length; i++) {
      if (candidateID == candidates[i].getCandidateID()) {
        return candidates[i].getStatus() == CandidateStatus.CONTINUING;
      }
    }
    return false; // not a candidate
    // TODO 2009.10.14 ESC postcondition
  } //@ nowarn;

  /**
   * Determine actual number of votes to transfer to this candidate
   * 
   * <p> The number of votes in a surplus transferred is in proportion to
   *         the number of transfers available throughout the candidate's ballot
   *         stack
   * @param fromCandidate
   *        Candidate from which to count the transfers
   * @param toCandidate
   *        Continuing candidate eligible to receive votes
   * @return Number of votes available for transfer
   */
  /*@ also
    @   protected normal_behavior
    @   requires state == COUNTING;
    @   requires isElected (fromCandidate) || 
    @            (fromCandidate.getStatus() == CandidateStatus.ELIMINATED);
    @   requires toCandidate.getStatus() == CandidateStatus.CONTINUING;
    @   requires ballotsToCount != null;
    @     requires (\forall int b; 0 <= b && b < totalVotes; 
    @         ballotsToCount[b] != null);
    @   ensures (isElected (fromCandidate) &&
    @     (getSurplus(fromCandidate) < getTotalTransferableVotes(fromCandidate)))
    @     ==>
    @       (\result == 
    @       (getSurplus (fromCandidate) *
    @         getPotentialTransfers (fromCandidate,
    @         toCandidate.getCandidateID()) /
    @         getTotalTransferableVotes (fromCandidate)));
    @   ensures ((fromCandidate.getStatus() == Candidate.ELIMINATED) ||
    @     (getTotalTransferableVotes(fromCandidate) <= getSurplus(fromCandidate)))
    @     ==>
    @       (\result == 
    @       (\num_of int j; 0 <= j && j < totalVotes;
    @         ballotsToCount[j].isAssignedTo(fromCandidate.getCandidateID()) &&
    @         getNextContinuingPreference(ballotsToCount[j]) ==
    @         toCandidate.getCandidateID()));
    @*/
  protected/*@ pure spec_public @*/int getActualTransfers(
    final/*@ non_null @*/Candidate fromCandidate,
    final/*@ non_null @*/Candidate toCandidate) {
    int numberOfVotes = getPotentialTransfers(fromCandidate,
                                              toCandidate.getCandidateID());
    final int surplus = getSurplus(fromCandidate);
    final int totalTransferableVotes = getTotalTransferableVotes(fromCandidate);
    if (isElected(fromCandidate) && surplus < totalTransferableVotes && 0 < totalTransferableVotes) {
      numberOfVotes *= surplus;
      numberOfVotes /= totalTransferableVotes;
    }

    return numberOfVotes;
    // TODO 2009.10.14 ESC postcondition
  } //@ nowarn;

  /**
   * Determine the rounded value of a fractional transfer.
   * 
   * <p> This depends on the shortfall and the relative size of the other
   *         fractional transfers.
   * @param fromCandidate
   *        Elected candidate from which to distribute surplus
   * @param toCandidate
   *        Continuing candidate potentially eligble to recieve transfers
   * @return <code>1</code> if the fractional vote is to be rounded up
   *         <code>0</code> if the fractional vote is to be rounded down
   */
  /*@ also 
    @   protected normal_behavior
    @   requires state == COUNTING;
    @   requires isElected (fromCandidate);
    @   requires toCandidate.getStatus() == CandidateStatus.CONTINUING;
    @   requires getSurplus(fromCandidate) < 
    @            getTotalTransferableVotes(fromCandidate);
    @   requires 0 <= getTransferShortfall (fromCandidate);
    @*/
  protected/*@ pure spec_public @*/int getRoundedFractionalValue(
    final/*@ non_null @*/Candidate fromCandidate,
    final/*@ non_null @*/Candidate toCandidate) {
    if (getOrder(fromCandidate, toCandidate) <= getTransferShortfall(fromCandidate)) {
      return 1;
    }
    return 0;
  }

  /**
   * Determine shortfall between sum of transfers rounded down and the size of
   * surplus
   * 
   * @param fromCandidate
   *        Elected candidate from which to distribute surplus
   * @return The shortfall between the sum of the transfers and the size of surplus
   */
  /*@ also 
    @   requires \nonnullelements (candidateList);
    @   requires state == COUNTING;
    @   requires (fromCandidate.getStatus() == CandidateStatus.ELECTED) ||
    @            (fromCandidate.getStatus() == CandidateStatus.ELIMINATED);
    @*/
  protected/*@ pure spec_public @*/int getTransferShortfall(
     final/*@ non_null @*/Candidate fromCandidate) {
    int shortfall = 0;
    for (int i = 0; i < totalNumberOfCandidates; i++) {
      if (candidates[i].getStatus() == CandidateStatus.CONTINUING) {
        shortfall += getActualTransfers(fromCandidate, candidates[i]);
      }
    }
    return shortfall - getSurplus(fromCandidate);
  }

  /**
   * Simulate random selection between two candidates.
   * 
   * <p> This needs to be random but consistent, so that same result is
   *         always given for the same pair of candidates.
   * @param firstCandidate
   *        The first of the candidates to be selected from
   * @param secondCandidate
   *        The second of the candidates to be selected from
   * @return The candidate ID of the chosen candidate
   */
  public/*@ pure @*/int randomSelection(
                                         final/*@ non_null @*/Candidate firstCandidate,
                                         final/*@ non_null @*/Candidate secondCandidate) {

    if (firstCandidate.isAfter(secondCandidate)
        || firstCandidate.sameAs(secondCandidate)) {
      return firstCandidate.getCandidateID();
    }
    return secondCandidate.getCandidateID();
  }

  /**
   * Determine the individuals remainder after integer division by the transfer
   * factor for surpluses.
   * 
   * <p> This can all be done with integer arithmetic; no need to use
   *         floating point numbers, which could introduce rounding errors.
   * @param fromCandidate
   *        Elected candidate from which to count to transfers
   * @param toCandidate
   *        Continuing candidate eligible to receive votes
   * @return The size of the quotient remainder
   */
  /*@ also
    @   protected normal_behavior
    @     requires \nonnullelements (candidateList);
    @     requires state == COUNTING;
    @     requires isElected (fromCandidate);
    @     requires toCandidate.getStatus() == CandidateStatus.CONTINUING;
    @     requires getSurplus(fromCandidate) < getTotalTransferableVotes(fromCandidate);
    @     requires 0 <= getTransferShortfall (fromCandidate);
    @     requires 0 < getSurplus(fromCandidate);
    @*/
  protected/*@ pure spec_public @*/int getTransferRemainder(
    final/*@ non_null @*/Candidate fromCandidate,
    final/*@ non_null @*/Candidate toCandidate) {
    return getPotentialTransfers(fromCandidate, toCandidate.getCandidateID())
      - getActualTransfers(fromCandidate, toCandidate);
  }

  /**
   * Determine if one continuing candidate is higher than another, for the
   * purpose of resolving remainders of transfer quotients.
   * 
   * <p> This is determined by finding the earliest round of counting in
   *         which these candidates had unequal votes. If both candidates are
   *         equal at all counts then random numbers are used to draw lots.
   * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_2.pdf">Department of
   *      Environment and Local Government, Count Requirements and Commentary on
   *      Count Rules, section 7, page 25</a>
   * @param firstCandidate
   *        The first of the candidates to be compared
   * @param secondCandidate
   *        The second of the candidates to be compared
   * @return <code>true</code> if the first candidate is deemed to have receIved
   *         more votes than the second
   */
  /*@ also
    @   protected normal_behavior
    @     requires countNumberValue < CountConfiguration.MAXCOUNT;
    @     requires firstCandidate.getStatus() == Candidate.CONTINUING;
    @     requires secondCandidate.getStatus() == Candidate.CONTINUING;
    @*/
  protected/*@ pure spec_public @*/boolean isHigherThan(
    final/*@ non_null @*/Candidate firstCandidate,
    final/*@ non_null @*/Candidate secondCandidate) {

    int firstNumberOfVotes;
    int secondNumberOfVotes;
    int count = countNumberValue;
    while (0 <= count) {

      // TODO 2009.10.14 ESC precondition warning
      firstNumberOfVotes = firstCandidate.getTotalAtCount(count); //@ nowarn;
      secondNumberOfVotes = secondCandidate.getTotalAtCount(count);
      if (firstNumberOfVotes > secondNumberOfVotes) {
        return true;
      } else if (secondNumberOfVotes > firstNumberOfVotes) {
        return false;
      }
      count--;
    }

    return secondCandidate.isAfter(firstCandidate);
    // TODO 2009.10.14 ESC postcondition warning
  } //@ nowarn;

  /**
   * Determine the number of continuing candidates with a higher remainder in
   * their transfer quotient, or deemed to have a higher remainder.
   * 
   * <p> There must be a strict ordering of candidates for the purpose of
   *         allocating the transfer shortfall. If two or more candidates have
   *         equal remainders then use the number of transfers they are about to
   *         receive and if the number of transfers are equal then look at the
   *         number of votes all ready received.
   * @param fromCandidate
   *        Candidate, already elected, with surplus votes to donate
   * @param toCandidate
   *        Continuing candidate eligible to receive vote transfer
   * @return The number of continuing candidates with a higher quotient remainder
   *         than this candidate
   */
  /*@ also
    @   protected normal_behavior
    @     requires state == COUNTING;
    @     requires isElected (fromCandidate);
    @     requires toCandidate.getStatus() == 
    @       election.tally.Candidate.CONTINUING;
    @     requires getSurplus(fromCandidate) < 
    @       getTotalTransferableVotes(fromCandidate);
    @     requires 0 <= getTransferShortfall (fromCandidate);
    @     requires 0 <= getSurplus(fromCandidate);
    @     ensures \result == getCandidateRanking (fromCandidate, toCandidate);
    @*/
  protected/*@ pure spec_public @*/int getOrder(
    final/*@ non_null @*/Candidate fromCandidate,
    final/*@ non_null @*/Candidate toCandidate) {
    int numberHigherThan = 0;
    final int actualTransfers = getActualTransfers(fromCandidate, toCandidate);
    // TODO 2009.10.14 ESC precondition warning
    final int transferRemainder 
      = getTransferRemainder(fromCandidate, toCandidate); //@ nowarn;

    for (int i = 0; i < totalNumberOfCandidates; i++) {
      if (candidates[i].getCandidateID() != toCandidate.getCandidateID()
        && candidates[i].getStatus() == CandidateStatus.CONTINUING) {
        // TODO 2009.10.14 ESC precondition warning
        numberHigherThan += compareCandidates(fromCandidate, toCandidate, //@ nowarn;
          actualTransfers, transferRemainder, candidates[i]);
      }
    }
    return numberHigherThan;
    // TODO 2009.10.14 ESC postcondition warning
  } //@ nowarn;

  /*@ protected normal_behavior
    @   requires state == COUNTING;
    @   requires isElected (fromCandidate);
    @   requires getSurplus(fromCandidate) < getTotalTransferableVotes(fromCandidate);
    @   requires 0 <= getTransferShortfall (fromCandidate);
    @   requires 0 <= getSurplus(fromCandidate);
    @*/
  protected /*@ pure @*/ int compareCandidates(
    final /*@ non_null @*/ Candidate fromCandidate,
    final /*@ non_null @*/ Candidate firstCandidate,
    final int transfersToFirst,
    final int firstTransferRemainder,
    final /*@ non_null @*/ Candidate secondCandidate) {
    
    // TODO 2009.10.14 ESC warning
    final int secondTransferRemainder 
      = getTransferRemainder(fromCandidate, secondCandidate); //@ nowarn;
    if (secondTransferRemainder > firstTransferRemainder) {
      return 1;
    }

    final int transfersToSecond = getActualTransfers(fromCandidate,
                                                    secondCandidate);
    if (secondTransferRemainder == firstTransferRemainder 
        && transfersToSecond > transfersToFirst) {
      return 1;
    } else if (secondTransferRemainder == firstTransferRemainder 
        && transfersToSecond == transfersToFirst
               // TODO 2009.10.14 ESC precondition warning
               && isHigherThan(secondCandidate, firstCandidate)) { //@ nowarn;
      return 1;
    }

    return 0;
  }

  /**
   * Get the maximum number of votes transferable to continuing candidates.
   * 
   * @param fromCandidate
   *        Candidate ID from which to check the transfers
   * @return Number of votes potentially transferable from this candidate
   */
  /*@ also
    @   protected normal_behavior
    @     requires state == COUNTING;
    @     requires \nonnullelements (candidateList);
    @     requires isElected (fromCandidate) ||
    @       (fromCandidate.getStatus() == CandidateStatus.ELIMINATED);
    @     ensures \result == numberTransferable (fromCandidate);
    @     ensures 0 <= \result;
    @*/
  protected /*@ pure spec_public @*/ int getTotalTransferableVotes(
    final /*@ non_null @*/ Candidate fromCandidate) {
    int numberOfTransfers = 0;
    for (int i = 0; i < totalNumberOfCandidates; i++) {
      if (candidates[i].getStatus() == CandidateStatus.CONTINUING) {
        numberOfTransfers +=
         getPotentialTransfers(fromCandidate, candidates[i].getCandidateID());
      }
    }
    return numberOfTransfers;
    // TODO 2009.10.14 ESC postcondition
  } //@ nowarn Post;

  /**
   * Transfer votes from one candidate to another.
   * 
   * @param fromCandidate
   *        Elected or excluded candidate
   * @param toCandidate
   *        Continuing candidate
   * @param numberOfVotes
   *        Number of votes to be transferred <BON>command</BON>
   */
  /*@ also
    @   protected normal_behavior
    @     requires fromCandidate.getStatus() != Candidate.CONTINUING;
    @     requires toCandidate.getStatus() == Candidate.CONTINUING;
    @     assignable ballotsToCount;
    @*/
  public abstract void transferVotes(
                                     final/*@ non_null @*/Candidate fromCandidate,
                                     final/*@ non_null @*/Candidate toCandidate,
                                     final int numberOfVotes);

  /**
   * Who is the highest continuing candidate, not yet elected?
   * 
   * @return The continuing candidate with the most votes
   */
  /*@ requires 1 <= getNumberContinuing();
    @ requires \nonnullelements (ballotsToCount);
    @ ensures \result == -AbstractBallotCounting.NONE_FOUND_YET ||
    @   (\max int i; 0 <= i && i < totalCandidates && 
    @   candidateList[i].getStatus() == Candidate.CONTINUING;
    @   countBallotsFor(candidateList[i].getCandidateID())) 
    @   == countBallotsFor(candidateList[\result].getCandidateID());
    @ ensures \result == AbstractBallotCounting.NONE_FOUND_YET || (\exists int i; 0 <= i && i < totalCandidates && 
    @   candidates[i].getStatus() == Candidate.CONTINUING; i == \result);
    @ ensures 0 <= \result && \result < totalCandidates;
    @ ensures candidateList[\result] != null;
    @*/
  public/*@ pure @*/int findHighestCandidate() {

    int highestCandidate = AbstractBallotCounting.NONE_FOUND_YET;
    long mostVotes = 0;

    for (int i = 0; i < totalNumberOfCandidates; i++) {
      if (candidates[i].getStatus() == CandidateStatus.CONTINUING) {
        final int votes = countBallotsFor(candidates[i].getCandidateID());
        if (votes > mostVotes) {
          mostVotes = votes;
          highestCandidate = i;
        } else if (0 <= highestCandidate && votes == mostVotes
                   && isHigherThan(candidates[i], candidates[highestCandidate])) {
          highestCandidate = i; // TODO test coverage
        }
      }
    }

    return highestCandidate;
    // TODO 2009.10.14 ESC postcondition
  } //@ nowarn Post;

  /**
   * Who is the lowest continuing candidate?
   * 
   * @return The continuing candidate with the least votes
   */
  /*@ requires 1 <= totalCandidates;
    @ requires \nonnullelements (ballotsToCount);
    @ ensures AbstractBallotCounting.NONE_FOUND_YET == \result 
    @   || (\forall int i; 0 <= i && i < totalCandidates && i != \result &&
    @   candidateList[i].getStatus() == CandidateStatus.CONTINUING;
    @   countBallotsFor(candidateList[i].getCandidateID()) >= 
    @   countBallotsFor(candidateList[\result].getCandidateID()));
    @ ensures AbstractBallotCounting.NONE_FOUND_YET == \result 
    @   || (\exists int i; 0 <= i && i < totalCandidates && 
    @   candidateList[i].getStatus() == CandidateStatus.CONTINUING;
    @   i == \result);
    @*/
  public/*@ pure @*/int findLowestCandidate() {

    long leastVotes = CountConfiguration.MAXVOTES;
    int lowest = AbstractBallotCounting.NONE_FOUND_YET;

    for (int i = 0; i < totalNumberOfCandidates; i++) {
      if (candidates[i].getStatus() == CandidateStatus.CONTINUING) {
        final int votes = countBallotsFor(candidates[i].getCandidateID());
        if (votes < leastVotes) {
          leastVotes = votes;
          lowest = i;
        } else if (0 <= lowest && votes == leastVotes
                   && isHigherThan(candidates[lowest], candidates[i])) {
          lowest = i;
        }
      }
    }

    return lowest;
  }

  /**
   * Exclude one candidate from the election.
   * 
   * @param loser
   *        The candidate to be excluded
   */
  /*@ requires 0 <= loser && loser < candidates.length;
    @ requires remainingSeats < getNumberContinuing();
    @ requires (state == COUNTING);
    @ requires loser < totalCandidates;
    @ requires loser == findLowestCandidate();
    @ requires candidateList[loser].getCandidateID() != Ballot.NONTRANSFERABLE;
    @ requires countNumber < CountConfiguration.MAXCOUNT;
    @ requires \nonnullelements (ballotsToCount);
    @ requires \nonnullelements (candidateList);
    @ requires candidateList[loser].getStatus() == Candidate.CONTINUING;
    @ requires hasQuota (candidateList[loser]) == false;
    @ assignable candidateList;
    @ assignable candidateList[loser], candidateList[*];
    @ assignable numberOfCandidatesEliminated;
    @ assignable candidateList[loser].state, ballotsToCount, ballots;
    @ ensures remainingSeats <= getNumberContinuing();
    @ ensures numberElected <= seats;
    @ ensures candidateList[loser].getStatus() == Candidate.ELIMINATED;
    @ ensures (\forall int b; 0 <= b && b < ballotsToCount.length;
    @   ballotsToCount[b].getCandidateID() != candidateList[loser].getCandidateID());
    @*/
  public void eliminateCandidate(final int loser) {
    candidates[loser].declareEliminated();
    redistributeBallots(candidates[loser].getCandidateID());
    numberOfCandidatesEliminated++;
  }

  /**
   * Redistribute the transferable ballots of an excluded candidate.
   * 
   * @param candidateID The unique identifier for the excluded candidate
   */
  /*@ requires candidateID != Ballot.NONTRANSFERABLE;
    @ requires countNumberValue < CountConfiguration.MAXCOUNT;
    @ requires \nonnullelements (ballotsToCount);
    @ assignable ballots;
    @*/
  protected void redistributeBallots(final int candidateID) {

    for (int b = 0; b < ballots.length; b++) {
      if (ballots[b].getCandidateID() == candidateID) {

        // TODO 2009.10.14 ESC precondition
        transferBallot(ballots[b]); //@ nowarn;
      }
    }
  }

  /**
   * Transfer the ballot to the next preference continuing candidate unless non-transferable.
   * 
   * @param ballot The ballot
   */
  /*@ assignable ballot.positionInList;
    @ ensures ballot.getCandidateID() == Ballot.NONTRANSFERABLE
    @   || (isContinuingCandidateID (ballot.getCandidateID()) 
    @   && \old(ballot).getCandidateID() != ballot.getCandidateID());
    @*/
  public void transferBallot(final /*@ non_null @*/ Ballot ballot) {

    while ((ballot.getCandidateID() != Ballot.NONTRANSFERABLE)
           && (!isContinuingCandidateID(ballot.getCandidateID()))) {
      ballot.transfer();
    }
    /*@ assert ballot.getCandidateID() == Ballot.NONTRANSFERABLE
      @   || isContinuingCandidateID (ballot.getCandidateID());
      @*/
    // TODO 2009.10.14 ESC postcondition
  } //@ nowarn;

  /**
   * Main count algorithm.
   */
  public abstract void count();

  /**
   * Elect this winning candidate.
   * 
   * @param winner
   *        The candidate with enough votes to win
   */
  //@ requires 0 <= winner && winner < totalCandidates;
  //@ requires candidateList[winner].getStatus() == Candidate.CONTINUING;
  //@ requires numberElected < seats;
  //@ requires 0 < remainingSeats;
  //@ requires candidates[winner] != null;
  /*@ requires (hasQuota(candidateList[winner])) 
    @   || (winner == findHighestCandidate())
    @   || (getNumberContinuing() == totalRemainingSeats);
    @ requires candidates[winner].getCandidateID() != Candidate.NO_CANDIDATE;
    @*/
  //@ requires state == ElectionStatus.COUNTING;
  //@ requires 0 < candidateList[winner].getCandidateID();
  //@ assignable candidates, numberOfCandidatesElected;
  //@ assignable totalRemainingSeats;
  //@ assignable candidates[winner], candidates[winner].state;
  //@ ensures isElected (candidateList[winner]);
  public void electCandidate(final int winner) {
    //@ assert candidates != null && candidates[winner] != null;
    candidates[winner].declareElected();
    numberOfCandidatesElected++;
    totalRemainingSeats--;
    // TODO 2009.10.14 ESC precondition
  } //@ nowarn;

  /**
   * Get the number of continuing candidates, neither elected nor eliminated
   * yet.
   * 
   * @return The number of continuing candidates.
   */
  public/*@ pure @*/int getNumberContinuing() {
    return totalNumberOfCandidates
           - (numberOfCandidatesElected + numberOfCandidatesEliminated);
  }

}