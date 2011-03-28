/*
 * All Rights Reserved.
 *
 *
 * Created on: Mar 25, 2004
 * Package: testers
 * File: ParseIESVotes.java
 * Author: Lorcan Coyle and Dónal Doyle
 */
package coyle_doyle_election;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

/**
 * @author doyledp To change the template for this generated type comment go to
 *         Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class ParseIESVotes {

	private String[]				numbers							= {"First", "Second", "Third", "Fourth", "Fifth", "Sixth", "Seventh",
			"Eighth", "Ninth", "Tenth", "Eleventh", "Twelfth","Thirteenth","Fourteenth","Fifteenth","Sixteenth"};

	public static final String	filename							= "C:\\Results\\out.txt";

	private List					stats;

	private boolean				firstPage;

	private int						numOfCounts;

	private int						numVotesCast;

	private int						quota;

	private int						deposit;

	private int						seats;

	private int						candidates;

	private CandidateStats		currentStats;

	private boolean				readNonTransferableVotes	= false;
    
    BufferedReader in;

	public ParseIESVotes() {
		this(filename);
	}

	public ParseIESVotes(String filename) {
		this(new File(filename));
	}

	public ParseIESVotes(File filename) {
		firstPage = true;
		stats = new ArrayList();
		try {
			in = new BufferedReader(new FileReader(filename));
			while (in.ready()) {
				String line = in.readLine();
				if (line.indexOf("Location of all votes after") != -1)
					readPageHeader(in);
				else if (line.indexOf(" votes as follows:") != -1 || line.indexOf(" vote as follows:") != -1) {
					String candidateName = line.substring(0, line.indexOf(" is credited with"));
					String sVotes = line.substring(line.indexOf("with ") + 5, line.indexOf(" vote"));
					if (sVotes.equals("0")) {
						currentStats = new CandidateStats(candidateName, numVotesCast);
						stats.add(currentStats);
					} else {
						currentStats = new CandidateStats(candidateName, numVotesCast);
						stats.add(currentStats);
						readVotes(in);
					}
				}
				if (line.indexOf("are non-transferable not effective as follows:") != -1) {
					readNonTransferableVotes(in);
					in.close();
					return;
				}
			}
			if (readNonTransferableVotes == false) {
				int[] votes = new int[numVotesCast + 1];
				currentStats = new CandidateStats("non-transferable not effective", numVotesCast);
				currentStats.setVotes(votes, numOfCounts);
				stats.add(currentStats);
			}
			in.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public void readPageHeader(BufferedReader in) throws IOException {
		for (int i = 0; i < 18; i++) {
			String line = in.readLine();
			if (firstPage) {
				if (firstPage && i == 10) {
					numOfCounts = (new Integer(line)).intValue();
				} else if (firstPage && i == 11) {
					numVotesCast = (new Integer(line)).intValue();
				} else if (firstPage && i == 12) {
					quota = (new Integer(line)).intValue();
				} else if (firstPage && i == 13) {
					deposit = (new Integer(line)).intValue();
				} else if (firstPage && i == 14) {
					seats = (new Integer(line)).intValue();
				} else if (firstPage && i == 15) {
					candidates = (new Integer(line)).intValue();
				}
			}
		}
		firstPage = false;
	}

	public void readVotes(BufferedReader in) throws IOException {
		int currentCountNumber = numOfCounts + 1;
		int[] votes = new int[numVotesCast + 1];
		while (true) {
			String line = in.readLine();
			if (line.indexOf("Source") != -1) {
				line = in.readLine();
				readPageHeader(in);
				line = in.readLine();
				// If Candidate not continued
				if (line.indexOf("CONTINUED") == -1) {
					if (line.indexOf("votes are non-transferable not effective") != -1
							|| line.indexOf("vote are non-transferable not effective") != -1) {
						currentStats.setVotes(votes, numOfCounts);
						votes = new int[numVotesCast + 1];
						readNonTransferableVotes(in);
						return;
					}
					// Next Candidate
					String candidateName = line.substring(0, line.indexOf(" is credited with"));
					int pos = line.indexOf(" votes as follows");
					if (pos == -1) {
						pos = line.indexOf(" vote as follows");
					}
					String sVotes = line.substring(line.indexOf("with ") + 5, pos);
					if (sVotes.equals("0")) {
						currentStats.setVotes(votes, numOfCounts);
						votes = new int[numVotesCast + 1];
						currentStats = new CandidateStats(candidateName, numVotesCast);
						stats.add(currentStats);
						return;
					} else {
						currentStats.setVotes(votes, numOfCounts);
						votes = new int[numVotesCast + 1];
						currentStats = new CandidateStats(candidateName, numVotesCast);
						stats.add(currentStats);
						readVotes(in);
						return;
					}
				}
				if (line.indexOf("received in the") == -1)
					line = in.readLine();
			}
			if (line.indexOf(" votes received in the ") != -1) {
				String countNumber = line.substring(line.indexOf(" votes received in the ") + 23, line.indexOf(" Count"));
				for (int i = 0; i < numbers.length; i++) {
					if (countNumber.equals(numbers[i])) {
						currentCountNumber = i + 1;
						break;
					}
				}
				line = in.readLine();
				if (line.indexOf("Source") != -1) {
					line = in.readLine();
					readPageHeader(in);
					line = in.readLine();
					line = in.readLine();
				}
				line = line.substring(14);
			}
			if (line.indexOf(" is credited with ") != -1) {
				String candidateName = line.substring(0, line.indexOf(" is credited with"));
				int beginning = line.indexOf("with ") + 5;
				int end = line.indexOf(" votes as follows");
				if (end == -1) {
					end = line.indexOf(" vote as follows");
				}
				String sVotes = line.substring(beginning, end);
				if (sVotes.equals("0")) {
					currentStats.setVotes(votes, numOfCounts);
					votes = new int[numVotesCast + 1];
					currentStats = new CandidateStats(candidateName, numVotesCast);
					stats.add(currentStats);
					return;
				} else {
					currentStats.setVotes(votes, numOfCounts);
					votes = new int[numVotesCast + 1];
					currentStats = new CandidateStats(candidateName, numVotesCast);
					stats.add(currentStats);
					readVotes(in);
					return;
				}
			}
			if (line.indexOf("are non-transferable not effective") != -1) {
				currentStats.setVotes(votes, numOfCounts);
				votes = new int[numVotesCast + 1];
				readNonTransferableVotes(in);
				return;
			}
			StringTokenizer tokeniser = new StringTokenizer(line, ",");
			while (tokeniser.hasMoreElements()) {
				String token = tokeniser.nextToken();
				token = token.trim();
				int voteNumber = (new Integer(token)).intValue();
				votes[voteNumber] = currentCountNumber;
			}
		}
	}

	public void readNonTransferableVotes(BufferedReader in) throws IOException {
		int currentCountNumber = numOfCounts + 1;
		int[] votes = new int[numVotesCast + 1];
		readNonTransferableVotes = true;
		while (in.ready()) {
			String line = in.readLine();
			if (line.indexOf("Source") != -1) {
				line = in.readLine();
				readPageHeader(in);
				line = in.readLine();
				if (line != null && line.indexOf(" votes became non-transferable not effective in the ") == -1
						&& line.indexOf(" vote became non-transferable not effective in the ") == -1) {
					line = in.readLine();
				}
				if (line == null) {
					currentStats = new CandidateStats("non-transferable not effective", numVotesCast);
					currentStats.setVotes(votes, numOfCounts);
					stats.add(currentStats);
					return;
				}
			}
			if (line.indexOf(" votes became non-transferable not effective in the ") != -1
					|| line.indexOf(" vote became non-transferable not effective in the ") != -1) {
				String countNumber = (line.indexOf(" votes became non-transferable not effective in the ") != -1) ? line.substring(line
						.indexOf(" votes became non-transferable not effective in the ") + 52, line.indexOf(" Count")) : line.substring(line
						.indexOf(" vote became non-transferable not effective in the ") + 52, line.indexOf(" Count"));
				for (int i = 0; i < numbers.length; i++) {
					if (countNumber.equals(numbers[i])) {
						currentCountNumber = i + 1;
						break;
					}
				}
				line = in.readLine();
				if (line.indexOf("Source") != -1) {
					line = in.readLine();
					readPageHeader(in);
					line = in.readLine();
					line = in.readLine();
				}
				line = line.substring(14);
			}
			if (line.indexOf("Vote numbers:") != -1)
				line = line.substring(14);
			StringTokenizer tokeniser = new StringTokenizer(line, ",");
			while (tokeniser.hasMoreElements()) {
				String token = tokeniser.nextToken();
				token = token.trim();
				int voteNumber = (new Integer(token)).intValue();
				votes[voteNumber] = currentCountNumber;
			}
		}
	}
    
    public void close(){
        try {
            in.close();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

	public static void main(String[] args) {
		new ParseIESVotes();
	}

	/**
	 * @return Returns the stats.
	 */
	public List getStats() {
		return stats;
	}
}
