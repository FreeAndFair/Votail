/*
 * All Rights Reserved.
 *
 *
 * Created on: Sep 6, 2005
 * Package: election
 * File: IESBulkTester.java
 * Author: Administrator
 */
package election;
import java.io.File;
import java.util.Properties;
import java.util.StringTokenizer;
/**
 * @author Administrator
 */
public class IESBulkTester {
	/**
	 * Tests all the elections in IESInput
	 */
	private final String slash = File.separator;
	public IESBulkTester() {
		//RunCount runOldElections = new RunCount(Datasets.DUBLIN_NORTH_2002);
		//String path = "d:" + slash + "IESInput" + slash + "TEMP" + slash + "F01";
		Properties pr = System.getProperties();
		String root;
		if (pr.getProperty("user.dir").equals("D:\\workspace\\e-vote")) {
			// home machine
			root = "E:" + slash + "IESInput" + slash + "stillFailing" + slash;
		} else {
			// college machine
			root = "D:" + slash + "IESData" + slash;
		}
		boolean multipleDirectories = false;
		int[] results = new int[3];
		if (multipleDirectories) {
			String path = root + "passed";
			File parentDirectory = new File(path);
			String[] files = parentDirectory.list();
			for (int i = 0; i < files.length; i++) {
				String directory = files[i];
				int[] result = testDirectory(path + slash + directory);
				results[0] += result[0];
				results[1] += result[1];
				results[2] += result[2];
			}
		} else {
			String path = root + "Fails";
			results = testDirectory(path);
		}
		System.out.println("Passed: " + results[0]);
		System.out.println("Failed: " + results[1]);
		System.out.println("Exception: " + results[2]);
	}
	public static void main(String[] args) {
		new IESBulkTester();
	}
	private int[] testDirectory(String path) {
		int s = 0;
		int passed = 0, failed = 0, exception = 0;
		File parentDirectory = new File(path);
		String[] files = parentDirectory.list();
		String outputPath = "e:" + slash + "IESInput";
		boolean copyFiles = false;
		boolean userAssistedTies = false;
		String code = "RE - MANU";
		int numBallots = Integer.MAX_VALUE;
		for (int i = 0; i < files.length; i++) {
			s++;
			String directory = files[i];
			File d = new File(path + slash + directory);
			if (d.isDirectory()) {
				String electionType = "none";
				int numSeats = 0;
				String status = "nothing";
				String directoryName = d.getName();
				// Exception - EU - 7 - 8 - 1700 - 05SEP172425 - IT - MAZDA15347354889 - OldError
				StringTokenizer st = new StringTokenizer(directoryName, "-");
				int t = 0;
				while (st.hasMoreTokens()) {
					String token = st.nextToken();
					t++;
					switch (t) {
						case 1:
							status = token.trim();
							break;
						case 2:
							electionType = token.trim();
							break;
						case 3:
							numSeats = Integer.parseInt(token.trim());
							break;
						case 5:
							numBallots = Integer.parseInt(token.trim());
							break;
					}
				}
				if (status.equals("Passed") || status.equals("Failed") || status.equals("Exception")) {
					if (numSeats > 0) {
						if (1 == 1) {// numBallots < 1000) {
							if (electionType.equals("EU") || electionType.equals("GE") || electionType.equals("LE")) {
								String votesMixNumberedPath = path + slash + directoryName + slash + "votesMixNumbered.asc";
								File votesMixNumberedFile = new File(votesMixNumberedPath);
								boolean goAhead = true;
								if (!votesMixNumberedFile.exists()) {
									goAhead = false;
								}
								String voteLocationsIESPath = path + slash + directoryName + slash + "voteLocationsIES.txt";
								File voteLoocationsIESFile = new File(voteLocationsIESPath);
								if (!voteLoocationsIESFile.exists()) {
									goAhead = false;
								}
								if (goAhead){// && directoryName.indexOf("Tie") == -1 && directoryName.indexOf("OldError") == -1) {
									System.out.println(s + "\t" + directoryName);
									System.out.println(">>>>>>>>>>>>>>>>>> Testing election " + directoryName);
									Tester tester = new Tester();
									tester.runTest(votesMixNumberedPath, voteLocationsIESPath, numSeats, electionType, outputPath,
											userAssistedTies, code, copyFiles);
									String result = tester.getResult();
									if (result.equals("Pass")) {
										passed++;
										//System.out.println("mkdir '" + outputPath + slash + "passes" + slash + directory + "'");
										//System.out.println("mv '" + path + slash + directory + slash + "*' '" + outputPath + slash + "passes"
										//		+ slash + directory + "'");
										//System.out.println("rm -R '" + path + slash + directory + "'");
									} else if (result.equals("Fail")) {
										failed++;
									} else if (result.equals("Exception")) {
										exception++;
									}
									System.out
											.println(" < < < < < < < < < Finished Testing election " + directoryName + " ***" + result + "***");
								} else if ((directoryName.indexOf("Tie") == -1 && directoryName.indexOf("OldError") == -1)) {
									System.out.println(s + "\t" + directoryName);
								}
								if (!goAhead) {
									System.out.print("'" + directoryName + "' ");
								}
							}
						}
					}
				}
			}
		}
		int[] result = new int[3];
		result[0] = passed;
		result[1] = failed;
		result[2] = exception;
		return result;
	}
}
