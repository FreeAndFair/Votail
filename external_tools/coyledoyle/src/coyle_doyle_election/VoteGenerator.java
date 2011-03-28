/*
 * All Rights Reserved.
 *
 *
 * Created on: Sep 10, 2005
 * Package: election
 * File: VoteGenerator.java
 * Author: Lorcan Coyle and Dónal Doyle
 */
package coyle_doyle_election;

import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Random;

import javax.swing.JFrame;

/**
 * This Class allows random elections to be generated for testing. The elections are generated in CSV format and dumped to a file.
 * 
 * @author Lorcan Coyle and Dónal Doyle
 */
public class VoteGenerator {
	/**
	 * Generates and outputs random votes to a file
	 * 
	 * @param numberofvotes
	 *           the number of votes to be generated
	 * @param numberofcandidates
	 *           the number of candidates in the election
	 * @param file
	 *           the name of the output file
	 * @throws IOException
	 *            thrown if there is a problem writing to the file
	 */
	public static void votesGenerator(int numberofvotes, int numberofcandidates, File file) throws IOException {
		BufferedWriter bw = new BufferedWriter(new FileWriter(file));
		Random rand = new Random(System.currentTimeMillis());
		for (int i = 0; i < numberofvotes; i++) {
			int numberOfPreferences = 1 + rand.nextInt(numberofcandidates);
			int[] preferences = new int[numberofcandidates];
			boolean candidates[] = new boolean[numberofcandidates];
			for (int j = 0; j < numberOfPreferences; j++) {
				int ithpreference;
				do {
					ithpreference = rand.nextInt(numberofcandidates);
				} while (candidates[ithpreference]);
				candidates[ithpreference] = true;
				preferences[ithpreference] = j + 1;
			}
			StringBuffer votes = new StringBuffer();
			votes.append(i + 1);
			for (int j = 0; j < numberofcandidates; j++) {
				votes.append(",");
				votes.append(preferences[j]);
			}
			votes.append("\n");
			bw.write(votes.toString());
		}
		bw.flush();
		bw.close();
	}
	/**
	 * New files are generated from the command line. The correct usage of the Election Generator is java ElectioGenerator numberofvotes
	 * numberofcandidates filename
	 * 
	 * @param args
	 *           a String array, the first element is an integer representing the number of votes required, the second is the number of
	 *           candidates required and the third is the output file location
	 */
	public static void main(String[] args) {

		if (args.length != 3) {
			System.out.println("The correct usage of the Election Generator is"
					+ " java ElectioGenerator numberofvotes numberofcandidates filename");
			return;
		}
		int numberofvotes = Integer.parseInt(args[0]);
		int numberofcandidates = Integer.parseInt(args[1]);
		File f = new File(args[2]);
		try {
			f.createNewFile();
			if (f.exists()) {
				votesGenerator(numberofvotes, numberofcandidates, f);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}

		JFrame frame = new JFrame("Finished");
		frame.addWindowListener(new WindowAdapter() {
			public void windowClosing(WindowEvent arg0) {
				System.exit(0);
			}
		});
		frame.pack();
		frame.show();
	}
}
