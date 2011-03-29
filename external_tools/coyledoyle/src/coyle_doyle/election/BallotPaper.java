/*
 * All Rights Reserved.
 *
 *
 * Created on: Aug 28, 2005
 * Package: election 
 * File: BallotPaper.java 
 * Author: Lorcan Coyle and Dónal Doyle
 */
package coyle_doyle.election;

/**
 * The BallotPaper class represents a single ballot paper in an election. It contains a number identifying it (and used in surplus
 * distributions) and an integer array that defines the preferences expressed on this ballot paper.
 * 
 * @author Lorcan Coyle and Dónal Doyle
 */
public class BallotPaper {

	// is this necessary?

	/**
	 * The number of this ballot
	 */
	private int			ballotNumber;

	/**
	 * <code>true</code> if there are no more preferences available on this ballot paper. If this is the case, this vote is not
	 * transferrable.
	 */
	private boolean	deadVote	= false;

	/**
	 * The number of candidates in the current election. This is the maximum number of preferences expressable on a ballot paper
	 */
	private int			numberOfCandidates;

	/**
	 * This is an array representing the preferences of this ballot paper
	 */
	private int[]		preferences;

	/**
	 * The index of the candidate with the highest preference
	 */
	private int			topCandidate;

	/*@
	 @ requires ballotNumber > 0;
	 @ //TODO need to check if all preferences exist on this ballot paper
	 @*/
	/**
	 * Constructs a new Ballot Paper. Takes in the number of this paper and the array of preferences that this Ballot Paper represents.
	 * 
	 * @param ballotNumber
	 *           the number of this ballot paper
	 * @param preferences
	 *           the array of preferences on this ballot paper
	 */
	public BallotPaper(int ballotNumber, int[] preferences) {
		this.ballotNumber = ballotNumber;
		this.preferences = preferences;
		this.numberOfCandidates = preferences.length;
	}

	//@ pure
	/**
	 * @return Returns the ballotNumber.
	 */
	public int getBallotNumber() {
		return ballotNumber;
	}

	//@ pure
	/**
	 * Returns the index of the candidate with the next highest preference. The current highest preference candidate has either been
	 * eliminated of elected (in which case this ballot paper is part of a surplus distribution).
	 * 
	 * @return the index of the candidate with the next highest preference
	 */
	public int getNextPreference() {
		if (deadVote) {
			return -1;
		}
		int nextPreferenceNumber = preferences[topCandidate] + 1;
		for (int j = 0; j < numberOfCandidates; j++) {
			if (preferences[j] == nextPreferenceNumber) {
				//topCandidate = j;
				return j;
			}
		}
		return -1;
	}

	//@ pure
	/**
	 * @return Returns this ballot paper's preferences.
	 */
	public int[] getPreferences() {
		return preferences;
	}

	/**
	 * Returns the index of the candidate with the highest preference
	 * 
	 * @return the index of the candidate with the highest preference
	 */
	public int getTopPreference() {
		if (!deadVote) {
			int last = numberOfCandidates + 1;
			for (int i = 1; i < last; i++) {
				for (int j = 0; j < numberOfCandidates; j++) {
					if (preferences[j] == i) {
						topCandidate = j;
						return j;
					}
				}
			}
			deadVote = true;
		}
		return -1;
	}

	/**
	 * This should be run on every Ballot Paper after every count This could be improved
	 */
	public void removeTopPreference() {
		if (!deadVote) {
			//	int oldTopCandidate = preferences[topCandidate];
			topCandidate = getNextPreference();
			//preferences[oldTopCandidate] = - preferences[oldTopCandidate];
		}
	}

	//@ pure
	/**
	 * Returns a String version of this Ballot Paper
	 * 
	 * @return a String version of this Ballot Paper
	 */
	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append("Vote number =\t" + ballotNumber + "\tPreferences =\t");
		for (int i = 0; i < preferences.length; i++) {
			if (i > 0) {
				sb.append(",");
			}
			sb.append(preferences[i]);
		}
		sb.append("\n");
		return sb.toString();
	}

}
