/*
 * All Rights Reserved.
 *
 *
 * Created on: Aug 28, 2005 
 * Package: election 
 * File: CandidateStats.java 
 * Author: Lorcan Coyle and Dónal Doyle
 */
package election;

/**
 * This class represents the count number that each ballot paper was (finally) allocated to this candidate. It is used for statistical,
 * auditing and debugging purposes.
 * 
 * @author Lorcan Coyle and Dónal Doyle
 */
public class CandidateStats {

	public static int	INCORRECT_VOTE_NUMBERS		= 3;

	public static int	INCORRECT_VOTE_LOCATIONS	= 2;

	public static int	CORRECT_VOTE_LOCATIONS		= 0;

	public static int	INVALID_OBJECT					= 4;

	/**
	 * Used for the difference between candidates after running equals()
	 */
	private int			differenceType;

	/**
	 * The candidate's name
	 */
	private String		candidateName;

	/**
	 * This array contains the count that the ballot paper with that index was assigned to this candidate
	 */
	private int[]		candidateVotes;

	/**
	 * The current count number
	 */
	private int			countNumber;

	/**
	 * Constructs a store for the ballot papers that this candidate received at each count
	 * 
	 * @param name
	 *           the name of the candiate
	 * @param numOfVotes
	 *           the total number of votes in the election - this is used to initialise the internal ballot paper array
	 */
	public CandidateStats(String name, int numOfVotes) {
		candidateName = name;
		candidateVotes = new int[numOfVotes + 1];
		countNumber = 0;
	}

	/**
	 * Adds the ballot paper IDs to this candidate in this count
	 * 
	 * @param votes
	 *           an array of the ballot paper IDs that are to be assigned to this candidate
	 * @param countNumber
	 *           the current count number
	 */
	public void addVotes(int[] votes, int countNumber) {
		for (int i = 0; i < votes.length; i++) {
			candidateVotes[votes[i]] = countNumber;
		}
		this.countNumber = countNumber;
	}

	/**
	 * Removes the transferred surplus from this candidate
	 * 
	 * @param votes
	 *           the surplus ballot paper IDs that need to be transferred
	 */
	public void removeVotesFromSurplus(int[] votes) {
		for (int i = 0; i < votes.length; i++) {
			candidateVotes[votes[i]] = 0;
		}
	}

	/**
	 * Removes all assigned vote indicies from this candidate. The candidate has been excluded.
	 */
	public void removeVotesFromExclusion() {
		for (int i = 0; i < candidateVotes.length; i++) {
			candidateVotes[i] = 0;
		}
	}

	/**
	 * Sets the array giving details of what count each vote was allocated to this candidate (the final allocation)
	 * 
	 * @param voteCountNumbers
	 *           the array giving details of what count each vote was allocated to this candidate
	 * @param numOfCounts
	 *           the number of counts in this election
	 */
	public void setVotes(int[] voteCountNumbers, int numOfCounts) {
		countNumber = numOfCounts;
		for (int i = 0; i < voteCountNumbers.length; i++) {
			candidateVotes[i] = voteCountNumbers[i];
		}
	}

	/**
	 * Returns a String representation of the number of votes this candidate received in all counts
	 * 
	 * @return a String representation of the number of votes this candidate received in all counts
	 */
	public String toString() {
		StringBuffer buffer = new StringBuffer();
		int countVotes[] = new int[countNumber + 1];
		int size = 0;
		for (int i = 0; i < candidateVotes.length; i++) {
			countVotes[candidateVotes[i]]++;
		}
		for (int i = 1; i < countVotes.length; i++) {
			buffer.append("Count Number " + i + ":" + countVotes[i] + "\n");
			size += countVotes[i];
		}
		return "Number of votes = " + size + "\n" + buffer.toString();
	}

	/**
	 * Tests whether two candidate's statistics are the same. This is used to test whether the IES counting algorithm is giving the
	 * exact same result as the Coyle-Doyle algorithm
	 * 
	 * @param otherCandidateStats
	 *           The statistics of the other candidates
	 * @return <code>true</code> if the two candidateStats are equal
	 */
	public boolean equals(Object otherCandidateStats) {
		differenceType = 0;
		if (otherCandidateStats instanceof CandidateStats) {
			CandidateStats c = (CandidateStats) otherCandidateStats;
			String cName = c.candidateName.replaceAll(" ", "");
			String tName = candidateName.replaceAll(" ", "");
			if (!cName.equals(tName)) {
				System.out.println("Error: Wrong Name:\t" + getCandidateName() + "\t" + c.getCandidateName());
				return false;
			}
			if (candidateVotes.length != c.candidateVotes.length) {
				System.out.println("Incorrect number of votes\n" + candidateName);
				System.out.println("Coyle - Doyle: Length = " + candidateVotes.length);
				System.out.println("IES          : Length = " + c.candidateVotes.length);
				differenceType = INCORRECT_VOTE_NUMBERS;
				return false;
			}
			boolean pass = true;
			for (int i = 0; i < candidateVotes.length; i++) {
				if (candidateVotes[i] != c.candidateVotes[i]) {
					System.out.println("Incorrect vote for ");
					System.out.println(candidateName);
					System.out.println("Vote Number   = " + i);
					System.out.println("Coyle - Doyle = " + candidateVotes[i]);
					System.out.println("IES           = " + c.candidateVotes[i]);
					differenceType = INCORRECT_VOTE_LOCATIONS;
					pass = false;
				}
			}
			return pass;
		}
		differenceType = INVALID_OBJECT;
		return false;
	}

	/**
	 * Returns the number of votes in the specified count for this candidate
	 * 
	 * @param countNumber
	 *           the count number
	 * @return the number of votes in the specified count for this candidate
	 */
	public int getNumOfVotes(int countNumber) {
		int result = 0;
		for (int i = 0; i < candidateVotes.length; i++) {
			if (candidateVotes[i] == countNumber) {
				result++;
			}
		}
		return result;
	}

	/**
	 * Returns a String representation of this candidate's votes for each count in the election
	 * 
	 * @return a String representation of this candidate's votes for each count in the election
	 */
	public String getAllVotes() {
		StringBuffer buffer = new StringBuffer();
		int count = 0;
		for (int j = 0; j < candidateVotes.length; j++) {
			if (candidateVotes[j] > 0) {
				count++;
			}
		}
		buffer.append("\n" + candidateName + " recieved " + count + " votes");
		for (int i = 1; i <= countNumber; i++) {
			boolean first = true;
			if (getNumOfVotes(i) > 0) {
				buffer.append("\n\n" + getNumOfVotes(i) + " votes recieved from Count " + i + "\n");
				for (int j = 0; j < candidateVotes.length; j++) {
					if (candidateVotes[j] == i) {
						if (first) {
							buffer.append(j);
							first = false;
						} else {
							buffer.append("," + j);
						}
					}
				}
			}
		}
		return buffer.toString();
	}

	/**
	 * Returns this candidate's name
	 * 
	 * @return Returns the candidateName.
	 */
	public String getCandidateName() {
		return candidateName;
	}

	public int getDifferenceType() {
		return differenceType;
	}
}
