/*
 * All Rights Reserved.
 *
 *
 * Created on: Sep 11, 2005
 * Package: election
 * File: Tester.java
 * Author: Administrator
 */
package coyle_doyle_election;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.channels.FileChannel;
import java.util.Calendar;
import java.util.List;
import java.util.Random;
/**
 * @author Administrator
 */
public class Tester {
	private static Random rn = new Random();
	private boolean containedTies = false;
	private boolean containedOldError = true;
	private String[] months = { "JAN", "FEB", "MAR", "APR", "MAY", "JUN", "JUL", "AUG", "SEP", "OCT", "NOV", "DEC" };
	public String getResult() {
		return result;
	}
	private String result = "untested";
	boolean copyFiles = false;
	public String runTest(String votesMixNumberedPath, String voteLocationsIES, int numSeats, String electionType, String outputPath,
			boolean userAssistedTies, String code, boolean copyFiles) {
		result = "";
		boolean passed = true;
		boolean exception = false;
		int numVotes = 0;
		List coyleDoyleStats = null;
		String[] candidateNames = { "" };
		try {
			ParseIESASC voteLocations = new ParseIESASC();
			List votes = voteLocations.parseFile(votesMixNumberedPath);
			candidateNames = voteLocations.getCandidateNames();
			numVotes = votes.size();
			//Run our election software to calculate location of votes after final count
			int eType = -1;
			if (electionType.equals("EU")) {
				eType = ElectionTypes.EUROPEAN_ELECTION;
			} else if (electionType.equals("LO")) {
				eType = ElectionTypes.LOCAL_ELECTION;
			} else if (electionType.equals("GE")) {
				eType = ElectionTypes.GENERAL_ELECTION;
			}
			coyleDoyleStats = runCoyleDoyleAlgorithm(candidateNames, numSeats, eType, votes, userAssistedTies);
			//Parse Location of Votes given by IES Location of Votes after final count
			File fi = new File(voteLocationsIES);
			if (!fi.exists()) {
				System.out.println("error " + voteLocationsIES + " does not exist");
			}
			ParseIESVotes p = new ParseIESVotes(voteLocationsIES);
			List iesStats = p.getStats();
			//Compare location of Votes between Coyle Doyle Implementation and the IES implementation
			for (int i = 0; i < coyleDoyleStats.size(); i++) {
				CandidateStats tcdCandidate = (CandidateStats) coyleDoyleStats.get(i);
				//if (i == iesStats.size()) {
				//	if (tcdCandidate.getCandidateName().equals("non-transferable not effective")) {
				//		break;
				//	}
				//}
				// Donal will fix this
				CandidateStats iesCandidate = (CandidateStats) iesStats.get(i);
				if (!tcdCandidate.equals(iesCandidate)) {
					passed = false;
				}
			}
		} catch (RuntimeException e) {
			exception = true;
			e.printStackTrace();
		}
		//Set saving path
		Calendar calendar = Calendar.getInstance();
		int hour = calendar.get(Calendar.HOUR_OF_DAY);
		int day = calendar.get(Calendar.DAY_OF_MONTH);
		int min = calendar.get(Calendar.MINUTE);
		int month = calendar.get(Calendar.MONTH);
		int sec = calendar.get(Calendar.SECOND);
		String sDay = String.valueOf(day);
		String sHour = String.valueOf(hour);
		String sMin = String.valueOf(min);
		String sSec = String.valueOf(sec);
		if (sHour.length() == 1) {
			sHour = "0" + sHour;
		}
		if (sMin.length() == 1) {
			sMin = "0" + sMin;
		}
		if (sDay.length() == 1) {
			sDay = "0" + sDay;
		}
		if (sSec.length() == 1) {
			sSec = "0" + sSec;
		}
		outputPath = outputPath + "\\";
		String randomEnd = randomstring(6, 6);
		String electionDetails = electionType + " - " + numSeats + " - " + candidateNames.length + " - " + numVotes + " - " + sDay
				+ months[month] + sHour + sMin + sSec + " - " + code;
		if (exception) {
			outputPath = outputPath + "Exception - ";
			result = "Exception";
		} else if (passed) {
			outputPath = outputPath + "Passed - ";
			result = "Pass";
		} else {
			outputPath = outputPath + "Failed - ";
			result = "Fail";
		}
		outputPath = outputPath + electionDetails;
		if (containedTies) {
			outputPath = outputPath + " - Tie";
		}
		if (containedOldError) {
			outputPath = outputPath + " - OldError";
		}
		outputPath = outputPath + "\\";
		//System.out.println(outputPath);
		if (copyFiles) {
			File f = new File(outputPath);
			if (!f.exists()) {
				f.mkdir();
			}
			//Copy output to the output folder
			try {
				//Copy votes location
				FileChannel srcChannel = new FileInputStream(voteLocationsIES).getChannel();
				FileChannel dstChannel = new FileOutputStream(outputPath + (new File(voteLocationsIES)).getName()).getChannel();
				dstChannel.transferFrom(srcChannel, 0, srcChannel.size());
				srcChannel.close();
				dstChannel.close();
				//Copy votes mixed and numbered
				srcChannel = new FileInputStream(votesMixNumberedPath).getChannel();
				dstChannel = new FileOutputStream(outputPath + (new File(votesMixNumberedPath)).getName()).getChannel();
				dstChannel.transferFrom(srcChannel, 0, srcChannel.size());
				srcChannel.close();
				dstChannel.close();
				BufferedWriter out = new BufferedWriter(new FileWriter(outputPath + "coyleDoyle.txt"));
				for (int i = 0; i < coyleDoyleStats.size(); i++) {
					StringBuffer buffer = new StringBuffer();
					CandidateStats tcdCandidate = (CandidateStats) coyleDoyleStats.get(i);
					buffer.append(tcdCandidate.getAllVotes());
					out.write(buffer.toString());
				}
				out.flush();
				out.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		return result;
	}
	private List runCoyleDoyleAlgorithm(String[] candidateNames, int numSeats, int electionType, List votes, boolean userAssistedTies) {
		Election election = new Election(candidateNames, numSeats, electionType);
		election.setPrint(false);
		election.setUserAssistedTies(userAssistedTies);
		election.election(votes);
		containedTies = election.isElectionContainedTies();
		containedOldError = election.isOldRoundingError();
		List coyleDoyleStats = election.getStats();
		return coyleDoyleStats;
	}
	public static int rand(int lo, int hi) {
		int n = hi - lo + 1;
		int i = rn.nextInt() % n;
		if (i < 0) {
			i = -i;
		}
		return lo + i;
	}
	public static String randomstring(int lo, int hi) {
		int n = rand(lo, hi);
		byte b[] = new byte[n];
		for (int i = 0; i < n; i++) {
			b[i] = (byte) rand('a', 'z');
		}
		return new String(b);
	}
}
