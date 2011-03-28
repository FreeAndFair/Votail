/*
 * All Rights Reserved.
 *
 *
 * Created on: Aug 28, 2005
 * Package: election
 * File: Election.java
 * Author: Lorcan Coyle and Dónal Doyle
 */
package coyle_doyle_election;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;
import tools.Tools;

/**
 * This is the main class that implements Irish Elections
 * 
 * @author Lorcan Coyle and Dónal Doyle
 */
public class Election {

	/**
	 * Used to indicate that a candidate is still electable in this election
	 */
	private static final int	CONTINUING					= 0;

	/**
	 * Used to indicate that a candidate is elected in this election
	 */
	private static final int	ELECTED						= 1;

	/**
	 * Used to indicate that a candidate is excluded from this election, i.e.
	 * that they are no longer electable
	 */
	private static final int	EXCLUDED						= -1;

	/**
	 * This is the list of Candidate names
	 */
	private String[]				candidates;

	/**
	 * The count number that each candidate was elected in.
	 */
	private int[]					countElected;

	/**
	 * The current count number
	 */
	private int						countNumber;

	/**
	 * <code>true</code> if this election contained a situation that required
	 * a tie-break at any point in the counting process
	 */
	private boolean				electionContainedTies	= false;

	/**
	 * The type of election
	 */
	private int						electionType;

	/**
	 * The number of candidates in the current election
	 */
	private int						numberOfCandidates;

	/**
	 * The number of candidates still elegable for the current election
	 */
	private int						numberOfContinuingCandidates;

	/**
	 * The number of seats remaining in the current election
	 */
	private int						numberOfRemainingSeats;

	/**
	 * The total number of seats in the current election
	 */
	private int						numberOfSeats;

	/**
	 * <code>true</code> if this election contained the scenario that caused
	 * the old version of IES to fail.
	 */
	private boolean				oldRoundingError			= false;

	/**
	 * <code>true</code> if verbose output is to be printed
	 */
	private boolean				print							= true;

	/**
	 * the number of votes required for a candidate to be deemed elected
	 */
	private int						quota;

	/**
	 * the number of votes required for a candidate to recoup their election fee
	 */
	private int						recoupQuota;

	/**
	 * The result of this election. The candidate IDs are stored in this array
	 * in the order that they were elected
	 */
	private int[]					result;

	/**
	 * A List of <code>CandidateStats</code> storing information regarding at
	 * which count each ballot paper was allocated to each candidate
	 */
	private List					stats;

	/**
	 * An array containing the current status of each candidate in this
	 * election;
	 * <code>CONTINUING<code>, <code>EXCLUDED</code> or <code>ELECTED</code>
	 */
	private int[]					status;

	/**
	 * An array of <code>List</code> s of ballot papers that is used to hold
	 * them for surplus distribution.
	 */
	private List[]					surplusVotes;

	/**
	 * Used to store the ordering in tie breakers e.g 3 people tied int[3,1,2]
	 */
	private List					tieBreakers					= new ArrayList();

	/**
	 * Used to store the ordering in tie breakers for surplus distributions (these carry in the case of three-way ties for example)
	 */
	private int[]					surplusTies					= new int[0];

	/**
	 * Used to store the actual candidate number ordering in tie breakers
	 */
	private List					actualTieBreakers			= new ArrayList();

	/**
	 * <code>true</code> if the user is asked who to choose in the case of a
	 * complete tie. In reality, a coin toss is used to decide in these
	 * circumstances.
	 */
	private boolean				userAssistedTies			= false;

	/**
	 * the number of ties that have occured so far in the count
	 */
	private int						numberOfTies;

	/*
	 * @ requires numberOfSeats > 0; @ requires candidates.length > 0; @
	 * requires candidates.length >= numberOfSeats; @ requires (\forall int i; 0 <=
	 * i && i < candidates.length; candidates[i] != null); @ requires
	 * electionType == ElectionTypes.DAIL_BYE_ELECTION @ || electionType ==
	 * ElectionTypes.EUROPEAN_ELECTION @ || electionType ==
	 * ElectionTypes.GENERAL_ELECTION @ || electionType ==
	 * ElectionTypes.LOCAL_ELECTION; @
	 */
	/*
	 * ensures status != null; ensures status.length == candidates.length;
	 * ensures (\forall int i; 0 <= i && i < status.size(); status[i] ==
	 * CONTINUING); ensures result != null; ensures result.length ==
	 * candidates.length; ensures (\forall int i; 0 <= i && i < result.size();
	 * result[i] == -1); ensures numberOfRemainingSeats == numberOfSeats;
	 * ensures numberOfCandidates == candidates.length;
	 */
	/**
	 * Constructs a new Election
	 * 
	 * @param candidates
	 *            the list of candidate names for the current election
	 * @param numberOfSeats
	 *            the number of candidates in the current election
	 * @param electionType
	 *            the current election type
	 */
	public Election(String[] candidates, int numberOfSeats, int electionType) {
		this.candidates = candidates;
		stats = new ArrayList();
		actualTieBreakers = new ArrayList();
		tieBreakers = new ArrayList();
		numberOfCandidates = candidates.length;
		numberOfContinuingCandidates = numberOfCandidates;
		this.numberOfSeats = numberOfSeats;
		this.electionType = electionType;
		numberOfRemainingSeats = numberOfSeats;
		status = new int[numberOfCandidates];
		for (int i = 0; i < numberOfCandidates; i++) {
			status[i] = CONTINUING;
		}
		result = new int[numberOfSeats];
		for (int i = 0; i < result.length; i++) {
			result[i] = -1;
		}
	}

	/*
	 * @ @ requires ballotStacks != null; @ requires n == 2; @ requires
	 * potential >= 0;
	 */
	/**
	 * Here we attempt eliminate as many candidates as allowable. Channel One is
	 * the name of a process specified in the election algorithm.
	 * 
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 * @param potential
	 *            The number of ballot papers available for transfer (so far).
	 *            This may include surplus ballot papers and ballot papers from
	 *            prior elimination.
	 * @param n
	 *            <code>channelOne</code> parameter. This is always
	 *            <code>2</code>
	 */
	private void channelOne(BallotStacks ballotStacks, int potential, int n) {
		int[] order = getOrdering(ballotStacks);
		int finalN = 1;
		while (n < numberOfContinuingCandidates) {
			int nPotential = potential;
			int nCandidate = order[numberOfContinuingCandidates - n];
			potential += ballotStacks.getCandidateNumberOfBallotPapers(nCandidate);
			int nPlus1Candidate = order[numberOfContinuingCandidates - (n + 1)];
			int nPlus1CandidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(nPlus1Candidate);
			// boolean excludingTogether = false;
			if (numberOfSeats == numberOfContinuingCandidates - n) {
				if (potential < nPlus1CandidateNumberOfVotes) {
					endElection(ballotStacks);
				} else {
					eliminateNCandidates(ballotStacks, finalN);
				}
				return;
			} else if (potential < nPlus1CandidateNumberOfVotes) {
				finalN = n;
			}
			if (nPlus1CandidateNumberOfVotes > recoupQuota) {
				channelThree(ballotStacks, nPotential, n);
				return;
			} else {
				if (potential > (nPlus1CandidateNumberOfVotes - recoupQuota)) {
					eliminateNCandidates(ballotStacks, finalN);
					return;
				}
				n++;
			}
		}
		printlnAlways("PROBLEM IN CHANNEL1");
	}

	/*
	 * @ @ requires ballotStacks != null; @ requires potential >= 0; @
	 */
	/**
	 * Here we attempt eliminate as many candidates as allowable. Channel One is
	 * the name of a process specified in the election algorithm.
	 * 
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 * @param potential
	 *            The number of ballot papers available for transfer (so far).
	 *            This may include surplus ballot papers and ballot papers from
	 *            prior elimination.
	 */
	private void channelOneStart(BallotStacks ballotStacks, int potential) {
		int[] order = getOrdering(ballotStacks);
		if (numberOfRemainingSeats == 1 && numberOfContinuingCandidates == 2) {
			endElection(ballotStacks);
		}
		int lastCandidate = order[numberOfContinuingCandidates - 1];
		int lastCandidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(lastCandidate);
		int secondLowestCandidate = order[numberOfContinuingCandidates - 2];
		int secondLowestCandidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(secondLowestCandidate);
		potential += lastCandidateNumberOfVotes;
		if (secondLowestCandidateNumberOfVotes > recoupQuota) {
			channelTwo(ballotStacks, potential, 1);
		} else if (secondLowestCandidateNumberOfVotes < recoupQuota && potential >= (recoupQuota - secondLowestCandidateNumberOfVotes)) {
			eliminateNCandidates(ballotStacks, 1);
		} else {
			channelOne(ballotStacks, potential, 2);
		}
	}

	/*
	 * @ @ requires ballotStacks != null; @ requires potential >= 0; @ requires
	 * n >= 2; @
	 */
	/**
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 * @param potential
	 *            The number of ballot papers available for transfer (so far).
	 *            This may include surplus ballot papers and ballot papers from
	 *            prior elimination.
	 * @param n
	 *            <code>channelThree</code> parameter
	 */
	private void channelThree(BallotStacks ballotStacks, int potential, int n) {
		int[] order = getOrdering(ballotStacks);
		int finalN = 1;
		while (n < numberOfContinuingCandidates) {
			int nCandidate = order[numberOfContinuingCandidates - n];
			potential += ballotStacks.getCandidateNumberOfBallotPapers(nCandidate);
			int nPlus1Candidate = order[numberOfContinuingCandidates - (n + 1)];
			int nPlus1CandidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(nPlus1Candidate);
			if (numberOfRemainingSeats == numberOfContinuingCandidates - n) {
				if (potential < nPlus1CandidateNumberOfVotes) {
					endElection(ballotStacks);
				} else {
					eliminateNCandidates(ballotStacks, finalN);
				}
				return;
			} else if (potential < nPlus1CandidateNumberOfVotes) {
				finalN = n;
			}
			n++;
		}
		printlnAlways("PROBLEM IN CHANNEL3");
	}

	/*
	 * @ @ requires ballotStacks != null; @ requires potential >= 0; @ requires
	 * n == 1; @
	 */
	/**
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 * @param potential
	 *            The number of ballot papers available for transfer (so far).
	 *            This may include surplus ballot papers and ballot papers from
	 *            prior elimination.
	 * @param n
	 *            <code>channelTwo</code> parameter. This is always
	 *            <code>1</code>
	 */
	private void channelTwo(BallotStacks ballotStacks, int potential, int n) {
		int[] order = getOrdering(ballotStacks);
		int finalN = 1;
		potential = 0;
		while (n < numberOfContinuingCandidates) {
			int nCandidate = order[numberOfContinuingCandidates - n];
			potential += ballotStacks.getCandidateNumberOfBallotPapers(nCandidate);
			int nPlus1Candidate = order[numberOfContinuingCandidates - (n + 1)];
			int nPlus1CandidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(nPlus1Candidate);
			if (numberOfRemainingSeats == numberOfContinuingCandidates - n) {
				if (potential < nPlus1CandidateNumberOfVotes) {
					endElection(ballotStacks);
				} else {
					eliminateNCandidates(ballotStacks, finalN);
				}
				return;
			} else if (potential < nPlus1CandidateNumberOfVotes) {
				finalN = n;
			}
			n++;
		}
		printlnAlways("PROBLEM IN CHANNEL2");
	}

	/*
	 * @ requires ballotStacks != null; @ requires availableSurplus > 0; @
	 */
	/**
	 * Checks whether the surplus votes can save the lowest candidate. This will
	 * only be done if distributing the surplus votes can affect the result of
	 * the election or save the deposit of the lowest continuing candidate in
	 * applicable elections.
	 * 
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 * @param availableSurplus
	 *            The number of surplus votes available for distribution.
	 * @return <code>true> if distributing the surplus votes can affect the result of the election or save the deposit 
	 * of the lowest continuing candidate in applicable elections.
	 */
	private/* @ pure @ */boolean checkCanSurplusSaveLowestCandidate(BallotStacks ballotStacks, int availableSurplus) {
		int ordering[] = getOrdering(ballotStacks);
		for (int i = 0; i < numberOfContinuingCandidates; i++) {
			int lowestCandidate = ordering[numberOfContinuingCandidates - (i + 1)];
			int lowestCandidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(lowestCandidate);
			if (lowestCandidateNumberOfVotes != 0) {
				int secondLowestCandidate = ordering[numberOfContinuingCandidates - (i + 2)];
				int secondLowestCandidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(secondLowestCandidate);
				int votesNeededToSaveLowestCandidate = secondLowestCandidateNumberOfVotes - lowestCandidateNumberOfVotes;
				int votesNeededToSaveLowestCandidatesDeposit = recoupQuota - lowestCandidateNumberOfVotes;
				// Are there enough surplus votes to save the lowest candidate from
				// elimination?
				if (availableSurplus >= votesNeededToSaveLowestCandidate && votesNeededToSaveLowestCandidate >= 0) {
					return true;
				}
				// Are there enough surplus votes to save the lowest candidate from
				// losing their deposit?
				if (votesNeededToSaveLowestCandidatesDeposit > 0 && availableSurplus >= votesNeededToSaveLowestCandidatesDeposit) {
					return true;
				}
				// The surplus should not be distributed - It will make no difference to
				// the result of the election
				return false;
			}
		}
		// The surplus should not be distributed - It will make no difference to
		// the result of the election
		return false;
	}

	/*
	 * @ requires ballotStacks != null; @ requires availableSurplus >= 0; @
	 */
	/**
	 * Checks whether the surplus votes should be distributed. This will only be
	 * done if distributing the surplus votes can affect the result of the
	 * election or save the deposit of a continuing candidate in applicable
	 * elections.
	 * 
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 * @param availableSurplus
	 *            The number of surplus votes available for distribution.
	 * @return <code>true> if distributing the surplus votes can affect the result of the election or save the deposit 
	 * of a continuing candidate in applicable elections.
	 */
	private/* @ pure @ */boolean checkForDistributableSurpluses(BallotStacks ballotStacks, int availableSurplus) {
		if (availableSurplus == 0) {
			return false;
		}
		int ordering[] = getOrdering(ballotStacks);
		int highestCandidate = ordering[0];
		int highestCandidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(highestCandidate);
		int votesNeededToElectHighestCandidate = quota - highestCandidateNumberOfVotes;
		// Are there enough surplus votes to elect the highest candidate?
		if (availableSurplus >= votesNeededToElectHighestCandidate) {
			return true;
		}
		return checkCanSurplusSaveLowestCandidate(ballotStacks, availableSurplus);
	}

	/*
	 * @ @ requires ballotPapersToBeDistributed != null; @ requires (\forall int
	 * i; 0 <= i && i < ballotPapersToBeDistributed.size(); @
	 * ballotPapersToBeDistributed.get(i) != null &&
	 * ballotPapersToBeDistributed.get(i) instanceof BallotPaper); @
	 */
	/**
	 * Distributes the passed votes to the remaining candidates. This is done by
	 * examining each ballot paper's next preference
	 * 
	 * @param ballotPapersToBeDistributed
	 *            the List of ballot papers to be distributed
	 * @return an array of lists representing the stacks of votes that were
	 *         distributed to each candidate
	 */
	private List[] distribute(List ballotPapersToBeDistributed) {
		int totalNumberOfVotes = ballotPapersToBeDistributed.size();
		List[] totals = new List[numberOfCandidates + 1];
		for (int i = 0; i < numberOfCandidates + 1; i++) {
			totals[i] = new ArrayList();
		}
		for (int i = 0; i < totalNumberOfVotes; i++) {
			BallotPaper vote = (BallotPaper) ballotPapersToBeDistributed.get(i);
			int canditateNumber = vote.getNextPreference();
			while (canditateNumber != -1 && status[canditateNumber] != CONTINUING) {
				vote.removeTopPreference();
				canditateNumber = vote.getNextPreference();
			}
			if (canditateNumber == -1) {
				canditateNumber = numberOfCandidates;
			}
			totals[canditateNumber].add(vote);
		}
		List[] output = new List[numberOfCandidates + 1];
		for (int i = 0; i < numberOfCandidates + 1; i++) {
			List transferredVotes = totals[i];
			int size = transferredVotes.size();
			List orderedTransferVotes = new ArrayList(size);
			boolean[] done = new boolean[size];
			for (int j = 0; j < size; j++) {
				int min = Integer.MAX_VALUE;
				int minIndex = -1;
				for (int k = 0; k < size; k++) {
					if (!done[k]) {
						BallotPaper v = (BallotPaper) transferredVotes.get(k);
						if (v.getBallotNumber() < min) {
							min = v.getBallotNumber();
							minIndex = k;
						}
					}
				}
				orderedTransferVotes.add(transferredVotes.get(minIndex));
				done[minIndex] = true;
			}
			// copy transfers to votes
			output[i] = new ArrayList();
			for (int j = 0; j < size; j++) {
				BallotPaper vote = (BallotPaper) orderedTransferVotes.get(j);
				output[i].add(vote);
			}
		}
		return output;
	}

	/**
	 * Distributes surplus ballot papers from an elected candidate to the
	 * remaining candidates
	 * 
	 * @param votes
	 *            the array of Lists of ballot papers (one list per candidate)
	 *            from which the surplus is to be distributed
	 * @param totalSurplus
	 *            the actual surplus - this many ballot papers from <ode>votes</code>
	 *            will actually be distributed.
	 * @return a list of the ballot papers that were distributed to each
	 *         candidate
	 */
	private List[] distributeSurplus(List votes, int totalSurplus) {
		List[] validSurpluses = distribute(votes);
		int transferrableVotes = votes.size() - validSurpluses[numberOfCandidates].size();
		if (transferrableVotes > totalSurplus) { // proportions
			int[] transferNumbers = new int[numberOfCandidates];
			double transferFactor = (double) totalSurplus / (double) transferrableVotes;
			// double[] remainders = new double[numberOfCandidates];
			int[] rems = new int[numberOfCandidates];
			int totalDistributedVotes = 0;
			for (int i = 0; i < numberOfCandidates; i++) {
				double solution = (validSurpluses[i].size() * transferFactor);
				int distributableSurplus = (int) Math.floor(solution);
				int rem = validSurpluses[i].size() * totalSurplus - (distributableSurplus * transferrableVotes);
				if (rem == transferrableVotes) {
					/*
					 * oldRoundingError is set here. rem will only equal
					 * transferrableVotes if a rounding error has occured. This
					 * will only be the case if the flooring of
					 * distributableSurplus causes the loss of a vote.
					 */
					distributableSurplus++;
					rem = 0;
					oldRoundingError = true;
				}
				transferNumbers[i] = distributableSurplus;
				totalDistributedVotes += distributableSurplus;
				rems[i] = rem;
				// double remainder = solution - distributableSurplus;
				// remainders[i] = remainder;
			}
			int shortfall = totalSurplus - totalDistributedVotes;
			int numVotesToTransfer = shortfall;
			boolean[] done = new boolean[numberOfCandidates];
			int[] tieOrdering = new int[0];
			int tieIndex = 0;
			for (int i = 0; i < shortfall; i++) {
				int max = -1;
				int tied = 1;
				int index = -1;
				int[] tiedCandidates = new int[numberOfCandidates];
				for (int j = 0; j < numberOfCandidates; j++) {
					tiedCandidates[j] = -1;
				}
				for (int j = 0; j < numberOfCandidates; j++) {
					if (!done[j]) {
						if (rems[j] > max) {
							tied = 1;
							max = rems[j];
							index = j;
						} else if (rems[j] == max) {
							if (transferNumbers[j] > transferNumbers[index]) {
								index = j;
								tied = 1;
							} else if (transferNumbers[j] == transferNumbers[index]) {
								// now check who had more at the earliest
								// count...
								CandidateStats indexCandidateStats = (CandidateStats) stats.get(index);
								CandidateStats jCandidateStats = (CandidateStats) stats.get(j);
								boolean tiedOnEveryCount = true;
								for (int k = 1; k < countNumber + 1; k++) {
									int indexStatsNumberOfVotes = indexCandidateStats.getNumOfVotes(k);
									int jStatsNumberOfVotes = jCandidateStats.getNumOfVotes(k);
									if (indexStatsNumberOfVotes < jStatsNumberOfVotes) {
										index = j;
										tied = 1;
										tiedOnEveryCount = false;
										break;
									}
									if (jStatsNumberOfVotes < indexStatsNumberOfVotes) {
										tiedOnEveryCount = false;
										break;
									}
								}
								if (tiedOnEveryCount) {
									tiedCandidates[tied++] = j;
								}
							}
						}
					}
				}
				if (tied > 1) {
					// the first tie was not previously added to tiedCandidates.
					tiedCandidates[0] = index;
				}
				if (tied > 1 && tied > numVotesToTransfer) {
					String message = "WARNING: While distributing surpluses there was a tie between "
							+ tied
							+ " candidates (both have the same number of transferred votes and remainders, "
							+ "select the candidates in order to decide who receives the extra vote: The first candidate will be awarded the extra vote.";
					// LORCAN swapping the ordering here as a trial fix, not sure if it will work for ties greater than 2.
					if (tieOrdering.length == 0) {
						tieOrdering = seperateTies(tied, Tools.reverseList(tiedCandidates), message, false);
					}
					//LORCAN: WHERE IS THIS VOTE ACTUALLY BEING TRANSFERRED, I DON'T SEE tieOrdering[0] BEING USED ANYWHERE ELSE?
					println("Selected candidate " + candidates[tieOrdering[tieIndex]] + ". They will receive the extra vote.");
					int selection = tieOrdering[tieIndex];
					tieIndex++;
					transferNumbers[selection]++;
					totalDistributedVotes++;
					done[selection] = true;
					// reduce the number of votes by one
					numVotesToTransfer--;
				} else {
					transferNumbers[index]++;
					totalDistributedVotes++;
					done[index] = true;
					// reduce the number of votes by one
					numVotesToTransfer--;
				}
			}
			// now distribute the votes
			int votesToTransfer = totalSurplus;
			List[] totals = new List[numberOfCandidates + 1]; // distribute
			// votes
			for (int i = 0; i < numberOfCandidates + 1; i++) {
				totals[i] = new ArrayList();
			}
			for (int i = votes.size() - 1; i > -1; i--) {
				if (votesToTransfer == 0) {
					break;
				}
				BallotPaper vote = (BallotPaper) votes.get(i);
				int preference = vote.getNextPreference();
				if (preference != -1 && transferNumbers[preference] > 0) {
					totals[preference].add(vote);
					transferNumbers[preference]--;
					votesToTransfer--;
				}
			}
			if (votesToTransfer != 0) {
				printlnAlways("PROBLEM IN distributeSurplus");
			}
			return totals;
		} else {
			int[] voteNumbers = new int[votes.size()];
			for (int i = 0; i < votes.size(); i++) {
				voteNumbers[i] = ((BallotPaper) votes.get(i)).getBallotNumber();
			}
			// distribute all votes
			int nonTransferrableVotes = totalSurplus - transferrableVotes;
			List[] totals = new List[numberOfCandidates + 1]; // distribute
			// votes
			for (int i = 0; i < numberOfCandidates + 1; i++) {
				totals[i] = new ArrayList();
			}
			for (int i = votes.size() - 1; i > -1; i--) {
				BallotPaper vote = (BallotPaper) votes.get(i);
				int preference = vote.getNextPreference();
				if (preference == -1) {
					if (nonTransferrableVotes > 0) {
						totals[numberOfCandidates].add(vote);
						nonTransferrableVotes--;
					}
				} else {
					totals[preference].add(vote);
					surplusVotes[preference].add(vote);
				}
			}
			return totals;
		}
	}

	/*
	 * @ @ requires ballotStacks != null; @
	 */
	/**
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 */
	private void distributeSurpluses(BallotStacks ballotStacks) {
		int topSurplusIndex = -1;
		int numberOfSurpluses = 0;
		int topSurplus = -1;
		int totalSurplus = 0;
		int numberTied = 0;
		int[] tiedCanidates = new int[numberOfCandidates];
		for (int i = 0; i < numberOfCandidates; i++) {
			tiedCanidates[i] = -1;
		}
		CandidateStats surplusCandidateStats = (CandidateStats) stats.get(result[0]);
		for (int i = 0; i < result.length; i++) {
			int index = result[i];
			if (index == -1) {
				break;
			}
			int surplus = ballotStacks.getCandidateNumberOfBallotPapers(index) - quota;
			if (surplus > 0) {
				if (surplus > topSurplus) {
					topSurplus = surplus;
					topSurplusIndex = index;
					tiedCanidates[0] = index;
					numberTied = 1;
					surplusCandidateStats = (CandidateStats) stats.get(index);
				} else if (surplus == topSurplus) {
					boolean tied = true;
					// which surplus came first?
					if (countElected[topSurplusIndex] < countElected[index]) {
						tied = false;
					} else if (countElected[topSurplusIndex] > countElected[index]) {
						topSurplusIndex = index;
						tied = false;
						surplusCandidateStats = (CandidateStats) stats.get(index);
						numberTied = 1;
					} else {
						// now check at all counts, starting with the first, if
						// all are equal then
						CandidateStats iSurplusCandidateStats = (CandidateStats) stats.get(index);
						for (int j = 1; j < countNumber; j++) {
							int iSurplusStatsNumberOfVotes = iSurplusCandidateStats.getNumOfVotes(j);
							int surplusStatsNumberOfVotes = surplusCandidateStats.getNumOfVotes(j);
							if (surplusStatsNumberOfVotes > iSurplusStatsNumberOfVotes) {
								tied = false;
								break;
							}
							if (surplusStatsNumberOfVotes < iSurplusStatsNumberOfVotes) {
								topSurplusIndex = index;
								tiedCanidates[0] = index;
								surplusCandidateStats = (CandidateStats) stats.get(index);
								numberTied = 1;
								tied = false;
								break;
							}
						}
					}
					if (tied) {
						tiedCanidates[numberTied] = index;
						numberTied++;
					}
				}
				totalSurplus += surplus;
				numberOfSurpluses++;
			}
		}
		if (numberTied > 1) {
			// look and see if we had a surplus tie already, if so use the previous ordering
			if (surplusTies.length == 0) {
				final String message = "WARNING "
						+ numberTied
						+ " candidates are tied with the same surplus, select an ordering to decide which of the following "
						+ "candidates will have their surplus distributed: The first candidate will have their surplus distributed first, and so forth as deemed necessary.";
				int[] tieOrdering = seperateTies(numberTied, Tools.reverseList(tiedCanidates), message, false);
				int selection = tieOrdering[0];
				println("Selected candidate " + candidates[selection] + ". Their surplus will be distributed.");
				topSurplusIndex = selection;
				surplusTies = new int[tieOrdering.length];
				for (int i = 1; i < tieOrdering.length; i++) {
					surplusTies[i - 1] = tieOrdering[i];
				}
			} else {
				int selection = surplusTies[0];
				println("Selected candidate " + candidates[selection]
						+ " from a previous tie ordering. Their surplus will be distributed.");
				topSurplusIndex = selection;
				int[] copy = new int[surplusTies.length - 1];
				for (int i = 1; i < surplusTies.length; i++) {
					copy[i - 1] = surplusTies[i];
				}
				surplusTies = copy;
			}
		}
		// only distribute the highest surplus
		int[] requiredVotes = new int[numberOfCandidates];
		int[] requiredForRecoupVotes = new int[numberOfCandidates];
		for (int i = 0; i < numberOfContinuingCandidates; i++) {
			int total = ballotStacks.getCandidateNumberOfBallotPapers(i);
			int numberOfRequiredVotes = quota - total;
			if (status[i] == CONTINUING) {
				requiredVotes[i] = numberOfRequiredVotes;
				int requiredForRecoup = recoupQuota - total;
				requiredForRecoupVotes[i] = Math.max(requiredForRecoup, 0);
			}
		}
		List votesToTransfer;
		if (countElected[topSurplusIndex] == 1) {
			votesToTransfer = ballotStacks.getCandidateStack(topSurplusIndex);
		} else {
			// TODO get rid of surplus votes here and you can remove it
			// everywhere.
			votesToTransfer = surplusVotes[topSurplusIndex];
		}
		List[] distributedSurpluses = distributeSurplus(votesToTransfer, topSurplus);
		List[] output = new List[numberOfCandidates + 1];
		for (int i = 0; i < numberOfCandidates + 1; i++) {
			List transferredVotes = distributedSurpluses[i];
			int size = transferredVotes.size();
			List orderedTransferVotes = new ArrayList(size);
			boolean[] done = new boolean[size];
			for (int j = 0; j < size; j++) {
				int min = Integer.MAX_VALUE;
				int minIndex = -1;
				for (int k = 0; k < size; k++) {
					if (!done[k]) {
						BallotPaper v = (BallotPaper) transferredVotes.get(k);
						if (v.getBallotNumber() < min) {
							min = v.getBallotNumber();
							minIndex = k;
						}
					}
				}
				orderedTransferVotes.add(transferredVotes.get(minIndex));
				done[minIndex] = true;
			}
			// copy transfers to votes
			output[i] = new ArrayList();
			for (int j = 0; j < size; j++) {
				BallotPaper vote = (BallotPaper) orderedTransferVotes.get(j);
				output[i].add(vote);
			}
		}
		distributedSurpluses = output;
		printSurplus(topSurplusIndex, distributedSurpluses);
		// now move the votes
		for (int i = 0; i < numberOfCandidates; i++) {
			if (status[i] != ELECTED) {
				surplusVotes[i] = new ArrayList();
			}
		}
		for (int i = 0; i < distributedSurpluses.length; i++) {
			List distributedVotes = distributedSurpluses[i];
			for (int j = 0; j < distributedVotes.size(); j++) {
				BallotPaper vote = (BallotPaper) distributedVotes.get(j);
				ballotStacks.transferBallotPaper(vote, topSurplusIndex, i);
				surplusVotes[i].add(vote);
			}
		}
	}

	/*
	 * @ @ requires ballotStacks != null; @
	 */
	/**
	 * Checks to see if any of the candidates are over the quota. If they are,
	 * they are deemed elected.
	 * 
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 */
	private void electCandidatesOverTheQuota(BallotStacks ballotStacks) {
		int[] ordering = getOrdering(ballotStacks);
		int i;
		for (i = 0; i < numberOfContinuingCandidates; i++) {
			int orderIndex = ordering[i];
			// Any candidates above the quota are deemed elected
			int candidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(orderIndex);
			int surplus = candidateNumberOfVotes - quota;
			if (status[orderIndex] == CONTINUING && surplus >= 0) {
				status[orderIndex] = ELECTED;
				countElected[orderIndex] = countNumber;
				numberOfRemainingSeats--;
				for (int j = 0; j < result.length; j++) {
					if (result[j] == -1) {
						result[j] = orderIndex;
						break;
					}
				}
			} else {
				break;
			}
		}
		numberOfContinuingCandidates -= i;
	}

	/*
	 * @ @ requires ballotPapers != null; @ ensures \result.length ==
	 * getNumberOfSeats(); @ ensures (\forall int i; i >= 0 && i <
	 * \result.length; \result[i] >= 0 && \result[i] < getNumberOfCandidates()); @
	 */
	/**
	 * This performs an election using the ballot papers passed here
	 * 
	 * @param ballotPapers
	 *            a List of all the ballot papers to be counted in this election
	 * @return the result of this election - an integer array representing the
	 *         order of the candidates
	 */
	public int[] election(List ballotPapers) {
		// Quota = ((Votes cast)/(No. of seats being filled + 1)) + 1, ignoring
		// any remainder
		// TODO check this!
		quota = (ballotPapers.size() / (numberOfSeats + 1)) + 1;
		recoupQuota = 0;
		if (electionType == ElectionTypes.GENERAL_ELECTION || electionType == ElectionTypes.EUROPEAN_ELECTION) {
			recoupQuota = (quota / 4) + 1;
		}
		println("Quota=" + quota + "\nRecoup Quota=" + recoupQuota + "\nNumber Of Candidates=" + numberOfCandidates
				+ "\nNumber Of Seats=" + numberOfSeats + "\nNumber Of Votes=" + ballotPapers.size());
		initStats(ballotPapers.size());
		countNumber = 1;
		// lastSetOfVotes = new List[numberOfCandidates + 1];
		surplusVotes = new List[numberOfCandidates + 1];
		for (int i = 0; i < numberOfCandidates + 1; i++) {
			surplusVotes[i] = new ArrayList();
		}
		countElected = new int[numberOfCandidates];
		BallotStacks ballotStacks = firstCount(ballotPapers);
		electCandidatesOverTheQuota(ballotStacks);
		while (numberOfRemainingSeats > 0) {
			printCount(ballotStacks);
			incrementCountNumber();
			// did anyone get elected?
			// int numberElected = 0;
			electCandidatesOverTheQuota(ballotStacks);
			// did anyone get elected?
			int availableSurplus = getAvailableSurplus(ballotStacks);
			// when the surpluses are distributed it's time to eliminate
			// candidates
			if (availableSurplus == 0) {
				removeZeros(ballotStacks);
			}
			// 3 choices:
			// 1. fillLastSeat
			if (numberOfContinuingCandidates == numberOfRemainingSeats) {
				endElection(ballotStacks);
				printCount(ballotStacks);
				return result;
			} else if (numberOfContinuingCandidates == (numberOfRemainingSeats + 1)) {
				while (availableSurplus > 0 && numberOfRemainingSeats > 0) {
					if (checkCanSurplusSaveLowestCandidate(ballotStacks, availableSurplus)) {
						distributeSurpluses(ballotStacks);
						electCandidatesOverTheQuota(ballotStacks);
						availableSurplus = getAvailableSurplus(ballotStacks);
						// update votes
						if (availableSurplus != 0) {
							printCount(ballotStacks);
							incrementCountNumber();
						}
					} else {
						break;
					}
				}
				endElection(ballotStacks);
				printCount(ballotStacks);
				return result;
			} else {
				// 2. are there surpluses? distribution is prohibited if it
				// cannot materially affect the progress of the count
				if (checkForDistributableSurpluses(ballotStacks, availableSurplus)) {
					distributeSurpluses(ballotStacks);
					electCandidatesOverTheQuota(ballotStacks);
					if (numberOfRemainingSeats == 0) {
						printCount(ballotStacks);
					}
				} else { // 3. eliminate lowest
					removeZeros(ballotStacks);
					channelOneStart(ballotStacks, availableSurplus);
					// can we end the election here?
					/*					if ((numberOfContinuingCandidates == numberOfRemainingSeats + 1)&& numberOfContinuingCandidates != 0) {
					 endElection(ballotStacks);
					 printCount(ballotStacks);
					 return result;
					 }
					 */// printCount(ballotStacks);
				}
			}
		}
		// printCount(ballotStacks);
		return result;
	}

	/*
	 * @ @ requires eliminatedCandidate >=0 &&eliminatedCandidate <
	 * numberOfCandidates; @
	 */
	/**
	 * Eliminates the specified candidate and transfers their ballot papers to
	 * the remaining candidates
	 * 
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 * @param eliminatedCandidate
	 *            the index of the candidate to be eliminated
	 */
	private void eliminateCandidate(BallotStacks ballotStacks, int eliminatedCandidate, boolean multiple) {
		// exclude the lowest candidates, finish the election
		List[] transfers = new List[numberOfCandidates + 1];
		for (int i = 0; i < numberOfCandidates + 1; i++) {
			transfers[i] = new ArrayList();
			if (i == numberOfCandidates || status[i] != ELECTED && !multiple) {
				surplusVotes[i] = new ArrayList();
			}
		}
		status[eliminatedCandidate] = EXCLUDED;
		int[] excludedCandidates = {eliminatedCandidate};
		int[] numberOfVotesToTransfer = new int[1];
		List eliminatedCandidateBallotPapers = ballotStacks.getCandidateStack(eliminatedCandidate);
		List[] distributedVotes = distribute(eliminatedCandidateBallotPapers);
		for (int j = 0; j < distributedVotes.length; j++) {
			List candidateVotes = distributedVotes[j];
			for (int k = 0; k < candidateVotes.size(); k++) {
				BallotPaper vote = (BallotPaper) candidateVotes.get(k);
				// votes[eliminatedCandidate].remove(vote);
				transfers[j].add(vote);
				numberOfVotesToTransfer[0]++;
			}
		}
		// sort transfers
		for (int i = 0; i < numberOfCandidates + 1; i++) {
			List transferredVotes = transfers[i];
			int size = transferredVotes.size();
			List orderedTransferVotes = new ArrayList(size);
			boolean[] done = new boolean[size];
			for (int j = 0; j < size; j++) {
				int min = Integer.MAX_VALUE;
				int minIndex = -1;
				for (int k = 0; k < size; k++) {
					if (!done[k]) {
						BallotPaper v = (BallotPaper) transferredVotes.get(k);
						if (v.getBallotNumber() < min) {
							min = v.getBallotNumber();
							minIndex = k;
						}
					}
				}
				orderedTransferVotes.add(transferredVotes.get(minIndex));
				done[minIndex] = true;
			}
			// copy transfers to votes
			for (int j = 0; j < size; j++) {
				BallotPaper vote = (BallotPaper) orderedTransferVotes.get(j);
				// votes[i].add(vote);
				ballotStacks.transferBallotPaper(vote, eliminatedCandidate, i);
				surplusVotes[i].add(vote);
			}
		}
		numberOfContinuingCandidates--;
		printTransfers(excludedCandidates, numberOfVotesToTransfer, transfers);
	}

	/*
	 * @ @ requires n > 0 && n < numberOfContinuingCandidates; @
	 */
	/**
	 * Eliminates the n lowest candidates and distributes their ballot papers to
	 * the remaining candidates.
	 * 
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 * @param n
	 *            the number of candidates to be eliminated
	 */
	private void eliminateNCandidates(BallotStacks ballotStacks, int n) {
		//  Lorcan - took this out will it make a difference?
		// the difference will be in terms of non transferrable votes i think
		// if (n == 1) {
		// int eliminatedCandidate =
		// getLowestCandidateForElimination(ballotStacks);
		// eliminateCandidate(ballotStacks, eliminatedCandidate);
		// }
		boolean multiple = (n == 1) ? false : true;
		boolean first = true;
		for (int i = 0; i < n; i++) {
			int eliminatedCandidate = getLowestCandidateForElimination(ballotStacks, multiple);
			if (first) {
				eliminateCandidate(ballotStacks, eliminatedCandidate, false);
				first = false;
			} else {
				eliminateCandidate(ballotStacks, eliminatedCandidate, true);
			}
			status[eliminatedCandidate] = EXCLUDED;
			// electCandidatesOverTheQuota(ballotStacks);
		}
		electCandidatesOverTheQuota(ballotStacks);
		//
		// // exclude n lowest candidates, finish the election
		// int[] order = getOrdering(ballotStacks);
		// List[] transfers = new List[numberOfCandidates + 1];
		// for (int i = 0; i < numberOfCandidates + 1; i++) {
		// transfers[i] = new ArrayList();
		// if (i == numberOfCandidates || status[i] != ELECTED) {
		// surplusVotes[i] = new ArrayList();
		// }
		// }
		// int[] excludedCandidates = new int[n];
		// for (int i = 0; i < n; i++) {
		// int candidate = order[numberOfContinuingCandidates - (i + 1)];
		// status[candidate] = EXCLUDED;
		// excludedCandidates[i] = candidate;
		// }
		// int[] numberOfVotesToTransfer = new int[n];
		// for (int i = 0; i < n; i++) {
		// int candidate = order[numberOfContinuingCandidates - (i + 1)];
		// // status[candidate] = EXCLUDED;
		// List excludedCandidateVotes =
		// ballotStacks.getCandidateStack(candidate);
		// List[] distributedVotes = distribute(excludedCandidateVotes);
		// for (int j = 0; j < distributedVotes.length; j++) {
		// List candidateVotes = distributedVotes[j];
		// for (int k = 0; k < candidateVotes.size(); k++) {
		// BallotPaper vote = (BallotPaper) candidateVotes.get(k);
		// //votes[candidate].remove(vote);
		// transfers[j].add(vote);
		// numberOfVotesToTransfer[i]++;
		// }
		// }
		// }
		// // sort transfers
		// for (int i = 0; i < numberOfCandidates; i++) {
		// List transferredVotes = transfers[i];
		// int size = transferredVotes.size();
		// List orderedTransferVotes = new ArrayList(size);
		// boolean[] done = new boolean[size];
		// for (int j = 0; j < size; j++) {
		// int min = Integer.MAX_VALUE;
		// int minIndex = -1;
		// for (int k = 0; k < size; k++) {
		// if (!done[k]) {
		// BallotPaper v = (BallotPaper) transferredVotes.get(k);
		// if (v.getBallotNumber() < min) {
		// min = v.getBallotNumber();
		// minIndex = k;
		// }
		// }
		// }
		// orderedTransferVotes.add(transferredVotes.get(minIndex));
		// done[minIndex] = true;
		// }
		// // copy transfers to votes
		// for (int j = 0; j < size; j++) {
		// BallotPaper vote = (BallotPaper) orderedTransferVotes.get(j);
		// //votes[i].add(vote);
		// ballotStacks.transferBallotPaper(vote, eliminatedCandidate, i);
		// surplusVotes[i].add(vote);
		// }
		// }
		// numberOfContinuingCandidates -= n;
		// printTransfers(excludedCandidates, numberOfVotesToTransfer,
		// transfers);
	}

	/**
	 * Ends the election, if there are seats to be filled, the highest remaining
	 * candidates are elected
	 * 
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 */
	private void endElection(BallotStacks ballotStacks) {
		// exclude n lowest candidates, finish the election
		int[] order = getOrdering(ballotStacks);
		int resultIndex = -1;
		for (int i = 0; i < result.length; i++) {
			if (result[i] == -1) {
				resultIndex = i;
				break;
			}
		}
		if (resultIndex != -1) { // we look for a tie iff the last electable
			// candidate is tied with the first
			// eliminatable candidate...
			int lastElectableIndex = result.length - resultIndex - 1;
			int lastElectableNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(order[lastElectableIndex]);
			int firstEliminatableNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(order[lastElectableIndex + 1]);
			if (lastElectableNumberOfVotes == firstEliminatableNumberOfVotes) {
				// check for a tie... among the lowest - not the highest, ordering does not matter among the elected
				int numberTied = 0;
				int[] tiedCanidates = new int[numberOfContinuingCandidates];
				int lowestCandidateIndex = order[numberOfContinuingCandidates - 1];
				int lowestCandidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(lowestCandidateIndex);
				tiedCanidates[numberTied++] = lowestCandidateIndex;
				CandidateStats lowestCandidateStats = (CandidateStats) stats.get(lowestCandidateIndex);
				for (int i = 1; i < order.length; i++) {
					int iLowestCandidate = order[numberOfContinuingCandidates - (1 + i)];
					int iLowestCandidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(iLowestCandidate);
					if (iLowestCandidateNumberOfVotes == lowestCandidateNumberOfVotes) {
						boolean tied = true;
						// now check at all counts, starting with the first, if
						// all are equal then
						CandidateStats iLowestCandidateStats = (CandidateStats) stats.get(iLowestCandidate);
						for (int j = 1; j < countNumber; j++) {
							int iLowestStatsNumberOfVotes = iLowestCandidateStats.getNumOfVotes(j);
							int lowestStatsNumberOfVotes = lowestCandidateStats.getNumOfVotes(j);
							if (lowestStatsNumberOfVotes < iLowestStatsNumberOfVotes) {
								tied = false;
								break;
							}
							if (lowestStatsNumberOfVotes > iLowestStatsNumberOfVotes) {
								numberTied = 0;
								tiedCanidates[numberTied++] = iLowestCandidate;
								lowestCandidateStats = (CandidateStats) stats.get(iLowestCandidate);
								tied = false;
								break;
							}
						}
						if (tied) {
							tiedCanidates[numberTied++] = iLowestCandidate;
						}
					}
				}
				//LORCAN: Problem here whereby asking whic to eliminate, but in fact both are elected.
				//i.e 3 candidates left, 2 are tieing but oter one should actually be eliminated.
				//Passed - EU - 3 - 8 - 20 - 11OCT230121 - IN - SERVER1134538414 - Tie\CoyleDoyle+1_2_3-1_2+IES+3_2_1-2_1
				if (numberTied > 1) {
					//TODO: LORCAN: Two problems here (as per dataset e-mailed)
					//The first problem is that the first index of tiedCandidates is always zero. i.e. it is not being set.
					//If you run the election I e-mailed you will notice that Conor Hayes is re introduced to the draw even though he is eliminated.
					//Somewhere else you have code like this, is something similar needed:
					//tiedCandidates[0] = index;
					//The second problem here is that it should not be a tie as in the e-mailed one.
					//Mike Carney should be eliminated has he had the smallest number of votes at an earlier election
					int selection = selectCandidateOnPreviousTie(numberTied, tiedCanidates);
					if (selection > -1) {
						println("Selected candidate " + candidates[selection] + " based on earlier count");
					} else {
						final String message = "WARNING "
								+ numberTied
								+ " candidates are tied with the same number of votes, select an ordering to decide which of the following "
								+ "candidates will be eliminated: The first candidate will be eliminated first, and so forth as deemed necessary.";
						int[] tieOrdering = seperateTies(numberTied, tiedCanidates, message, true);
						selection = tieOrdering[0];
						println("Selected candidate " + selection);
					}
					int elimiatedCandidate = selection;
					for (int i = 0; i < numberOfContinuingCandidates; i++) {
						int candidate = order[i];
						if (candidate != elimiatedCandidate) {
							status[candidate] = ELECTED;
							result[resultIndex++] = candidate;
						}
					}
					status[elimiatedCandidate] = EXCLUDED;
					numberOfRemainingSeats = 0;
					numberOfContinuingCandidates = 0;
					return;
				}
				// LORCAN: there is a bug here, what if more than one candidate are being eliminated at this point in the election... might never happen
				for (int i = 0; i < numberOfContinuingCandidates; i++) {
					int candidate = order[i];
					if (candidate == tiedCanidates[0]) {
						status[candidate] = EXCLUDED;
					} else {
						status[candidate] = ELECTED;
						result[resultIndex++] = candidate;
					}
				}
				numberOfRemainingSeats = 0;
				numberOfContinuingCandidates = 0;
			}
		}
		for (int i = 0; i < numberOfContinuingCandidates; i++) {
			int candidate = order[i];
			if (i < numberOfRemainingSeats) {
				status[candidate] = ELECTED;
				result[resultIndex++] = candidate;
			} else {
				status[candidate] = EXCLUDED;
			}
		}
		numberOfRemainingSeats = 0;
		numberOfContinuingCandidates = 0;
	} /*
	 * @ @ requires ballotPapers != null; @ requires (\forall int i; 0 <= i &&
	 * i < ballotPapers.size(); @ ballotPapers.get(i) != null &&
	 * ballotPapers.get(i) instanceof BallotPaper); @
	 */

	/**
	 * Performs the first count of the election
	 * 
	 * @param ballotPapers
	 *            a List of all the ballot papers to be counted in this election
	 * @return the piles of ballot papers (one pile per candidate) after the
	 *         first count.
	 */
	private BallotStacks firstCount(List ballotPapers) {
		BallotStacks ballotStacks = new BallotStacks(candidates);
		ballotStacks.firstCount(ballotPapers);
		for (int i = 0; i < numberOfCandidates; i++) {
			int numberOfCandidateVotes = ballotStacks.getCandidateNumberOfBallotPapers(i);
			int[] values = new int[numberOfCandidateVotes];
			for (int j = 0; j < numberOfCandidateVotes; j++) {
				BallotPaper ballotPaper = ballotStacks.getCandidateVote(i, j);
				values[j] = ballotPaper.getBallotNumber();
			}
			((CandidateStats) stats.get(i)).addVotes(values, countNumber);
		}
		return ballotStacks;
	}

	/**
	 * Returns an int array representing the ordering of the candidates in the
	 * current election. The ith element of the array will be the index of the
	 * cancidate in that position in the election, i.e. candidateNames[order[0]]
	 * will be in first place
	 * 
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 * @return an int array representing the ordering of the candidates in the
	 *         current election.
	 */
	private/* @ pure @ */int[] getAllOrdering(BallotStacks ballotStacks) {
		int numberOfElectedCandidates = numberOfSeats - numberOfRemainingSeats;
		int[] ordering = new int[numberOfCandidates];
		boolean done[] = new boolean[numberOfCandidates];
		int pos;
		for (pos = 0; pos < numberOfElectedCandidates; pos++) {
			ordering[pos] = result[pos];
			done[result[pos]] = true;
		}
		for (int i = pos; i < numberOfCandidates; i++) {
			int max = -1;
			int index = -1;
			for (int j = 0; j < numberOfCandidates; j++) {
				int candidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(j);
				if (status[j] != ELECTED && !done[j] && candidateNumberOfVotes > max) {
					max = candidateNumberOfVotes;
					index = j;
				}
			}
			if (index == -1) {
				printlnAlways("PROBLEM");
				break;
			}
			ordering[i] = index;
			done[index] = true;
		}
		return ordering;
	}

	/**
	 * Returns the total number of surplus votes that are available for
	 * distribution
	 * 
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 * @return the total number of surplus votes that are available for
	 *         distribution
	 */
	private/* @ pure @ */int getAvailableSurplus(BallotStacks ballotStacks) {
		int availableSurplus = 0;
		for (int i = 0; i < numberOfSeats; i++) {
			int candidate = result[i];
			if (candidate != -1) {
				int candidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(result[i]);
				int surplus = candidateNumberOfVotes - quota;
				if (surplus > 0) {
					availableSurplus += surplus;
				}
			}
		}
		return availableSurplus;
	}

	/**
	 * Gets the index of the candidate with the lowest number of votes. This
	 * candidate will be eliminated.
	 * 
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)s
	 * @return the index of the candidate with the lowest number of votes.
	 */
	private int getLowestCandidateForElimination(BallotStacks ballotStacks, boolean multiple) {
		// tie, what if bottom candidates have the same number of votes?
		int[] order = getOrdering(ballotStacks);
		int lowestCandidate = order[numberOfContinuingCandidates - 1];
		int lastCandidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(lowestCandidate);
		int secondLowestCandidate = order[numberOfContinuingCandidates - 2];
		int secondLowestCandidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(secondLowestCandidate);
		if (lastCandidateNumberOfVotes == secondLowestCandidateNumberOfVotes) {
			int numberTied = 1;
			int[] tiedCanidates = new int[numberOfCandidates];
			CandidateStats lowestCandidateStats = (CandidateStats) stats.get(lowestCandidate);
			tiedCanidates[0] = lowestCandidate;
			for (int i = 2; i < numberOfContinuingCandidates + 1; i++) {
				int iLowestCandidate = order[numberOfContinuingCandidates - i];
				int iLowestCandidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(iLowestCandidate);
				// multiple is used for when we have multiple eliminations - in
				// this case ties are irrelevant as both candidates are finished
				if (iLowestCandidateNumberOfVotes == lastCandidateNumberOfVotes && !multiple) {
					boolean tied = true;
					// now check at all counts, starting with the first, if all
					// are equal then
					CandidateStats iLowestCandidateStats = (CandidateStats) stats.get(iLowestCandidate);
					for (int j = 1; j < countNumber; j++) {
						int iLowestStatsNumberOfVotes = iLowestCandidateStats.getNumOfVotes(j);
						int lowestStatsNumberOfVotes = lowestCandidateStats.getNumOfVotes(j);
						if (lowestStatsNumberOfVotes < iLowestStatsNumberOfVotes) {
							tied = false;
							break;
						}
						if (lowestStatsNumberOfVotes > iLowestStatsNumberOfVotes) {
							tiedCanidates[0] = iLowestCandidate;
							lowestCandidateStats = (CandidateStats) stats.get(iLowestCandidate);
							numberTied = 1;
							tied = false;
							break;
						}
					}
					if (tied) {
						tiedCanidates[numberTied] = iLowestCandidate;
						numberTied++;
					}
				} else {
					break;
				}
			}
			if (numberTied == 1) {
				return tiedCanidates[0];
			}
			int selection = selectCandidateOnPreviousTie(numberTied, tiedCanidates);
			if (selection > -1) {
				println("Selected candidate " + candidates[selection] + " based on earlier count");
				//LORCAN: CHANGED THIS FROM lowestCandidate. Donal
				return selection;
			}
			String message = "WARNING "
					+ numberTied
					+ " lowest candidates are tied, select an ordering over the following candidates. The first candidate will be eliminated first, and so forth as deemed necessary.";
			int[] tieOrdering = seperateTies(numberTied, tiedCanidates, message, true);
			selection = tieOrdering[0];
			println("Selected candidate " + candidates[selection]);
			return selection;
		}
		return lowestCandidate;
	}

	//TODO: This method checks previous ties to see if a tied candidate should be selected
	private int selectCandidateOnPreviousTie(int numberTied, int[] tiedCanidates) {
		for (int i = 0; i < actualTieBreakers.size(); i++) {
			//Assuming previous tie is a match, will be set to false if not
			boolean foundPreviousTie = true;
			int[] actualPreviousTieOrdering = (int[]) actualTieBreakers.get(i);
			for (int j = 0; j < numberTied; j++) {
				int candNumber = tiedCanidates[j]; //Candidate to check for in previous tie
				boolean foundCandidate = false;
				for (int k = 0; k < actualPreviousTieOrdering.length; k++) {
					if (candNumber == actualPreviousTieOrdering[k]) {
						foundCandidate = true;
						break;
					}
				}
				if (!foundCandidate) {
					//If candidate not found then this tie is not a match
					foundPreviousTie = false;
					break;
				}
			}
			if (foundPreviousTie) {
				for (int j = 0; j < actualPreviousTieOrdering.length; j++) {
					int cNum = actualPreviousTieOrdering[j];
					//Check if cNum is in the list of currently tied candidates. If so then return it.
					for (int k = 0; k < numberTied; k++) {
						if (cNum == tiedCanidates[k])
							return cNum;
					}
				}
			}
		}
		//Tie not previously solved
		return -1;
	}

	/**
	 * returns the number of candidates in this election.
	 * 
	 * @return the number of candidates in this election.
	 */
	public/* @ pure @ */int getNumberOfCandidates() {
		return numberOfCandidates;
	}

	/**
	 * Returns the number of seats available in this election.
	 * 
	 * @return the number of seats available in this election.
	 */
	public/* @ pure @ */int getNumberOfSeats() {
		return numberOfSeats;
	}

	/**
	 * Gets the ordering of the candidates
	 * 
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 * @return the ordering of the candidates
	 */
	private/* @ pure @ */int[] getOrdering(BallotStacks ballotStacks) {
		int[] ordering = new int[numberOfContinuingCandidates];
		boolean done[] = new boolean[numberOfCandidates];
		for (int i = 0; i < numberOfContinuingCandidates; i++) {
			int max = -1;
			int index = -1;
			for (int j = 0; j < numberOfCandidates; j++) {
				int candidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(j);
				if (status[j] == CONTINUING && !done[j] && candidateNumberOfVotes > max) {
					max = candidateNumberOfVotes;
					index = j;
				}
			}
			if (index == -1) {
				printlnAlways("PROBLEM");
				break;
			}
			ordering[i] = index;
			done[index] = true;
		}
		return ordering;
	}

	/**
	 * Returns this election's CandidateStats.
	 * 
	 * @return Returns this election's CandidateStats.
	 */
	public/* @ pure @ */List getStats() {
		return stats;
	}

	public List getTieOrders() {
		return tieBreakers;
	}

	/**
	 * Increments the count number by one
	 */
	private void incrementCountNumber() {
		countNumber++;
	}

	/*
	 * @ @ requires numberOfVotes >=0; @
	 */
	/**
	 * Initialises the <code>CandidateStats</code> List
	 * 
	 * @param numberOfVotes
	 *            the number of BallotPapers in this election
	 */
	private void initStats(int numberOfVotes) {
		for (int i = 0; i < candidates.length; i++) {
			stats.add(new CandidateStats(candidates[i], numberOfVotes));
		}
		stats.add(new CandidateStats("non-transferable not effective", numberOfVotes));
	}

	/**
	 * Returns <code>true</code> if this election encountered a situation that
	 * require a tie-bread.
	 * 
	 * @return Returns the electionContainedTies.
	 */
	public/* @ pure @ */boolean isElectionContainedTies() {
		return electionContainedTies;
	}

	/**
	 * Returns <code>true</code> if the rounding conditions that caused IES
	 * software to fail occured here
	 * 
	 * @return Returns the oldRoundingError.
	 */
	public/* @ pure @ */boolean isOldRoundingError() {
		return oldRoundingError;
	}

	/**
	 * Prints information about the current count
	 * 
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 */
	private/* @ pure @ */void printCount(BallotStacks ballotStacks) {
		StringBuffer message = new StringBuffer();
		message.append("Results after count " + countNumber + "\n");
		int[] ordering = getAllOrdering(ballotStacks);
		for (int i = 0; i < numberOfCandidates; i++) {
			int index = ordering[i];
			int candidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(index);
			message.append(candidateNumberOfVotes);
			if (candidateNumberOfVotes < 1000) {
				message.append("\t");
			}
			message.append("\t-\t" + candidates[index]);
			if (status[index] == CONTINUING) {
				message.append(" (CONTINUING)\n");
			} else if (status[index] == EXCLUDED) {
				message.append(" (EXCLUDED)\n");
			} else if (status[index] == ELECTED) {
				message.append(" (ELECTED)\n");
			}
		}
		int numberOfNontransferrableVotes = ballotStacks.getCandidateNumberOfBallotPapers(numberOfCandidates);
		message.append(numberOfNontransferrableVotes);
		if (numberOfNontransferrableVotes < 1000) {
			message.append("\t");
		}
		message.append("\t-\tNon transferrable votes.\n");
		println(message.toString());
	}

	/**
	 * Prints out the current line if the print flag is set
	 * 
	 * @param line
	 *            the line to be printed
	 */
	private/* @ pure @ */void println(String line) {
		if (print) {
			Tools.println(line);
		}
	}

	/**
	 * Prints out the current int if the print flag is set
	 * 
	 * @param line
	 *            the line to be printed
	 */
	private/* @ pure @ */void println(int num) {
		if (print) {
			Tools.println(num);
		}
	}

	/**
	 * Prints out the current line whether or not the print flag is set
	 * 
	 * @param line
	 *            the line to be printed
	 */
	private/* @ pure @ */void printlnAlways(String line) {
		Tools.println(line);
	}

	public void printSurplus(int candidateIndex, List[] surplus) {
		statsSurplus(surplus, candidateIndex);
		StringBuffer message = new StringBuffer();
		int surplusSize = 0;
		for (int i = 0; i < numberOfCandidates; i++) {
			if (status[i] == CONTINUING) {
				int numberOfVotes = surplus[i].size();
				surplusSize += numberOfVotes;
				message.append(numberOfVotes);
				if (numberOfVotes > -100 && numberOfVotes < 1000) {
					message.append("\t");
				}
				message.append("\t-\t" + candidates[i] + "\n");
			}
		}
		int numberOfNontransferrableVotes = surplus[numberOfCandidates].size();
		surplusSize += numberOfNontransferrableVotes;
		message.append(numberOfNontransferrableVotes);
		if (numberOfNontransferrableVotes < 1000) {
			message.append("\t");
		}
		message.append("\t-\tNon transferrable votes.\n");
		println("Distributing " + surplusSize + " suplus votes from candidate " + candidates[candidateIndex] + " in count "
				+ countNumber + "\n");
		println(message.toString());
	}

	/**
	 * Prints out the way votes were transferred in the current count
	 * 
	 * @param excludedCandidates
	 *            an array containing the indicies of the excluded candidates
	 * @param numberOfVotesToTransfer
	 *            the number of votes to transfer
	 * @param transfers
	 *            the ballot papers that were transferred - these details will
	 *            be printed
	 */
	public void printTransfers(int[] excludedCandidates, int[] numberOfVotesToTransfer, List[] transfers) {
		statTransfers(transfers, excludedCandidates);
		StringBuffer message = new StringBuffer();
		for (int i = 0; i < numberOfCandidates; i++) {
			if (status[i] == CONTINUING) {
				message.append(transfers[i].size());
				if (transfers[i].size() > -100 && transfers[i].size() < 1000) {
					message.append("\t");
				}
				message.append("\t-\t" + candidates[i] + "\n");
			}
		}
		int numberOfNontransferrableVotes = transfers[numberOfCandidates].size();
		message.append(numberOfNontransferrableVotes);
		if (numberOfNontransferrableVotes < 1000) {
			message.append("\t");
		}
		message.append("\t-\tNon transferrable votes.\n");
		for (int i = 0; i < excludedCandidates.length; i++) {
			int candidateIndex = excludedCandidates[i];
			println("Distributing " + numberOfVotesToTransfer[i] + " votes from candidate " + candidates[candidateIndex] + " in count "
					+ countNumber);
		}
		println(message.toString());
	}

	/**
	 * Excludes the candidates with zero votes
	 * 
	 * @param ballotStacks
	 *            the piles of ballot papers (one pile per candidate)
	 */
	private void removeZeros(BallotStacks ballotStacks) {
		// count the zeros...
		int[] order = getOrdering(ballotStacks);
		int numberOfZeros = 0;
		for (int i = 0; i < numberOfContinuingCandidates; i++) {
			int lastCandidate = order[numberOfContinuingCandidates - (i + 1)];
			int lastCandidateNumberOfVotes = ballotStacks.getCandidateNumberOfBallotPapers(lastCandidate);
			if (lastCandidateNumberOfVotes > 0) {
				break;
			}
			numberOfZeros++;
		}
		if (numberOfZeros == 0) {
			return;
		} else if (numberOfRemainingSeats == numberOfContinuingCandidates - numberOfZeros) {
			endElection(ballotStacks);
		} else {
			for (int i = 0; i < numberOfZeros; i++) {
				status[order[numberOfContinuingCandidates - (i + 1)]] = EXCLUDED;
			}
			numberOfContinuingCandidates -= numberOfZeros;
		}
	}

	/*
	 * @ requires numberTied > 1; @ requires message != null; @ requires
	 * tiedCandidates.length == numberTied; @ requires tiedCandidates != null && @
	 * (\forall int i; 0 <= i && i < tiedCandidates.length; tiedCandidates[i] >
	 * 0 && tiedCandidates[i] < numberTied); @ ensures (\forall int i; 0 <= i &&
	 * i < \result.length; \result[i] > 0 && \result[i] < numberTied); @ ensures
	 * electionContainedTies == true; @
	 */
	/*
	 * @ requires numberTied > 1; @ requires message != null; @ requires
	 * tiedCandidates.length == numberTied; @ requires tiedCandidates != null && @
	 * (\forall int i; 0 <= i && i < tiedCandidates.length; tiedCandidates[i] >
	 * 0 && tiedCandidates[i] < numberTied); @ ensures \result > 0; @ ensures
	 * \result < numberTied; @ ensures electionContainedTies == true; @
	 */
	/**
	 * Seperates a number of tied candidates. This is generally done by asking
	 * the user to select one candidate using the command prompt.
	 * 
	 * @param numberTied
	 *            the number of tied candidates
	 * @param tiedCandidates
	 *            the tied candidates
	 * @param message
	 *            the message representing the choice for the user to consider
	 * @return the candidate to be selected
	 */
	private int[] seperateTies(int numberTied, int[] tiedCandidates, String message, boolean elimination) {
		int[] tieOrdering = new int[numberTied];
		electionContainedTies = true;
		int selection;
		if (userAssistedTies) {
			try {
				BufferedReader stdin = new BufferedReader(new InputStreamReader(System.in));
				String digitstring = "";
				while (true) {
					try {
						printlnAlways(message);
						for (int i = 0; i < numberTied; i++) {
							printlnAlways((i + 1) + " = " + candidates[tiedCandidates[i]]);
						}
						for (int i = 0; i < numberTied; i++) {
							digitstring = stdin.readLine();
							selection = Integer.parseInt(digitstring);
							if (selection > 0 && selection < numberTied + 1) {
								// return tiedCandidates[selection - 1];
								tieOrdering[i] = selection;
							}
						}
						break;
					} catch (NumberFormatException e) {
						printlnAlways(digitstring + " is not a valid answer. please select a number between 1 and " + numberTied);
					}
				}
				tieBreakers.add(tieOrdering);
			} catch (IOException e) {
				e.printStackTrace();
				System.exit(0);
			}
		} else {
			println(message);
			for (int i = 0; i < numberTied; i++) {
				println((i + 1) + " = " + candidates[tiedCandidates[i]]);
			}
			if (tieBreakers.size() <= numberOfTies) {
				println("Candidates seperated by default ordering:");
				for (int i = 0; i < numberTied; i++) {
					tieOrdering[i] = numberTied - i;
					println(tieOrdering[i]);
				}
				tieBreakers.add(tieOrdering);
			} else {
				tieOrdering = (int[]) tieBreakers.get(numberOfTies);
				println("Candidates seperated by entered ordering:");
				for (int i = 0; i < numberTied; i++) {
					println(tieOrdering[i]);
				}
			}
		}
		numberOfTies++;
		int actualOrdering[] = new int[numberTied];
		for (int i = 0; i < actualOrdering.length; i++) {
			actualOrdering[i] = tiedCandidates[tieOrdering[i] - 1];
		}
		if (elimination) {
			actualTieBreakers.add(actualOrdering);
		}
		return actualOrdering;
	}

	/**
	 * @param print
	 *            The print to set.
	 */
	public void setPrint(boolean print) {
		this.print = print;
	}

	public void setTieOrders(List tieBreakers) {
		if (tieBreakers != null) {
			this.tieBreakers = tieBreakers;
		} else {
			this.tieBreakers = new ArrayList();
		}
	}

	/**
	 * <code>true</code> if the algorithm should ask the user to break ties.
	 * By default the algorithm selects the last candidate in the set of tied
	 * candidates
	 * 
	 * @param userAssistedTies
	 *            The userAssistedTies to set.
	 */
	public void setUserAssistedTies(boolean userAssistedTies) {
		this.userAssistedTies = userAssistedTies;
	}

	private void statsSurplus(List[] distributedSurpluses, int topSurplusIndex) {
		int[][] voteNums = new int[distributedSurpluses.length][];
		int totalNumVotes = 0;
		for (int i = 0; i < distributedSurpluses.length; i++) {
			List v = distributedSurpluses[i];
			int[] values = new int[v.size()];
			for (int j = 0; j < values.length; j++) {
				BallotPaper vote = (BallotPaper) v.get(j);
				values[j] = vote.getBallotNumber();
			}
			voteNums[i] = values;
			totalNumVotes += values.length;
			((CandidateStats) stats.get(i)).addVotes(values, countNumber);
		}
		int surplusVoteNums[] = new int[totalNumVotes];
		int index = 0;
		for (int i = 0; i < voteNums.length; i++) {
			for (int j = 0; j < voteNums[i].length; j++) {
				surplusVoteNums[index] = voteNums[i][j];
				index++;
			}
		}
		((CandidateStats) stats.get(topSurplusIndex)).removeVotesFromSurplus(surplusVoteNums);
	}

	private void statTransfers(List[] transfers, int[] excludedCandidates) {
		for (int i = 0; i < transfers.length; i++) {
			List v = transfers[i];
			int[] values = new int[v.size()];
			for (int j = 0; j < values.length; j++) {
				BallotPaper vote = (BallotPaper) v.get(j);
				values[j] = vote.getBallotNumber();
			}
			((CandidateStats) stats.get(i)).addVotes(values, countNumber);
		}
		for (int i = 0; i < excludedCandidates.length; i++) {
			((CandidateStats) stats.get(excludedCandidates[i])).removeVotesFromExclusion();
		}
	}
}
