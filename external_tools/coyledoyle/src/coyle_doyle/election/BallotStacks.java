/*
 * All Rights Reserved.
 *
 *
 * Created on: Sep 11, 2005
 * Package: election
 * File: BallotStacks.java
 * Author: Lorcan Coyle and Dónal Doyle
 */
package coyle_doyle.election;
import java.util.ArrayList;
import java.util.List;
/**
 * @author Lorcan Coyle and Dónal Doyle
 */
public class BallotStacks {
	/*@
	 @ ensures \result > 0;
	 @*/
	/**
	 * @return Returns the numberOfCandidates.
	 */
	public/*@ pure @*/int getNumberOfCandidates() {
		return numberOfCandidates;
	}
	/**
	 * The Array of Lists of ballot papers (one per candidate and one for non-transferrable votes
	 */
	private List[]		ballotStacks;
	/**
	 * This is the list of Candidate names
	 */
	private String[]	candidateNames;
	/**
	 * The number of candidates in the current election
	 */
	private int			numberOfCandidates;
	/**
	 * Sets up the stacks of ballot papers
	 * @param candidateNames an array containing the names of the candidates in this election
	 */
	public BallotStacks(String[] candidateNames) {
		this.candidateNames = candidateNames;
		numberOfCandidates = candidateNames.length;
		ballotStacks = new List[numberOfCandidates + 1];
		for (int i = 0; i < numberOfCandidates; i++) {
			ballotStacks[i] = new ArrayList();
		}
		// This is for non-transferrable votes
		ballotStacks[numberOfCandidates] = new ArrayList();
	}
	/*@
	 @ requires ballotPapers != null;
	 @ requires (\forall int i; 0 <= i && i < ballotPapers.size(); 
	 @ ballotPapers.get(i) != null && ballotPapers.get(i) instanceof BallotPaper);
	 @*/
	/**
	 * Performs the first count of the election 
	 * @param ballotPapers
	 *           a List of all the ballot papers to be counted in this election
	 */
	public void firstCount(List ballotPapers) {
		int numberOfVotes = ballotPapers.size();
		for (int i = 0; i < numberOfVotes; i++) {
			BallotPaper ballotPaper = (BallotPaper) ballotPapers.get(i);
			int canditateNumber = ballotPaper.getTopPreference();
			if (canditateNumber != -1) {
				ballotStacks[canditateNumber].add(ballotPaper);
			}
		}
	}
	/*@
	 @ requires candidateIndex > -1;
	 @ requires candidateIndex < getNumberOfCandidates();
	 @*/
	/**
	 * Returns the number of ballot papers in this candidate's stack
	 * @param candidateIndex the candidate in question
	 * @return the number of ballot papers in this candidate's stack
	 */
	public/*@ pure @*/int getCandidateNumberOfBallotPapers(int candidateIndex) {
		return ballotStacks[candidateIndex].size();
	}
	/*@
	 @ requires ballotPaper != null;
	 @ requires fromCandidateIndex > -1 && fromCandidateIndex < getNumberOfCandidates();
	 @ requires toCandidateIndex > -1 && toCandidateIndex < getNumberOfCandidates();
	 @*/
	/**
	 * Transfers a ballot paper from one candidate's stack to another's
	 * @param ballotPaper the ballot paper to be transferred
	 * @param fromCandidateIndex the index of the candidate who's stack this ballot paper will be removed from
	 * @param toCandidateIndex the index of the candidate who's stack this ballot paper will be moved to
	 */
	public void transferBallotPaper(BallotPaper ballotPaper, int fromCandidateIndex, int toCandidateIndex) {
		int ballotPaperIndex = ballotPaper.getBallotNumber();
		transferBallotPaper(ballotPaperIndex, fromCandidateIndex, toCandidateIndex);
	}
	/*@
	 @ requires ballotPaperIndex >= 0;
	 @ requires fromCandidateIndex > -1 && fromCandidateIndex < getNumberOfCandidates();
	 @ requires toCandidateIndex > -1 && toCandidateIndex < getNumberOfCandidates();
	 @*/
	/**
	 * Transfers a ballot paper from one candidate's stack to another's
	 * @param ballotPaperIndex the index of the ballot paper to be transferred
	 * @param fromCandidateIndex the index of the candidate who's stack this ballot paper will be removed from
	 * @param toCandidateIndex the index of the candidate who's stack this ballot paper will be moved to
	 */
	public void transferBallotPaper(int ballotPaperIndex, int fromCandidateIndex, int toCandidateIndex) {
		for (int i = 0; i < getCandidateNumberOfBallotPapers(fromCandidateIndex); i++) {
			BallotPaper testBallotPaper = getCandidateVote(fromCandidateIndex, i);
			if (testBallotPaper.getBallotNumber() == ballotPaperIndex) {
				ballotStacks[fromCandidateIndex].remove(i);
				ballotStacks[toCandidateIndex].add(testBallotPaper);
				return;
			}
		}
		System.out.println("ERROR: vote " + ballotPaperIndex + " should have been transferred from "
				+ candidateNames[fromCandidateIndex] + " to " + candidateNames[toCandidateIndex] + " but it was not in their stack.");
		System.exit(1);
	}
	/*@ 
	 @ requires candidateIndex >=0 && candidateIndex < getNumberOfCandidates();
	 @ requires voteIndex >= 0 && voteIndex < getCandidateNumberOfBallotPapers(candidateIndex);
	 @*/
	/**
	 * Returns the specified candidate's specified ballot paper
	 * @param candidateIndex the specified candidate
	 * @param voteIndex the specified index of the ballot paper
	 * @return the specified candidate's specified ballot paper
	 */
	public/*@ pure @*/BallotPaper getCandidateVote(int candidateIndex, int voteIndex) {
		return (BallotPaper) ballotStacks[candidateIndex].get(voteIndex);
	}
	/*@
	 @ requires candidateIndex >= 0;
	 @ requires candidateIndex < getNumberOfCandidates();
	 @*/
	// TODO remove this method!
	public/*@ pure @*/List getCandidateStack(int candidateIndex) {
		return ballotStacks[candidateIndex];
	}
}
