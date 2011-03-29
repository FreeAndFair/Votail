/*
 * All Rights Reserved.
 *
 *
 * Created on: Aug 29, 2005
 * Package: testers
 * File: Datasets.java
 * Author: Lorcan Coyle and Dónal Doyle
 */
package coyle_doyle.testers;

import coyle_doyle.election.ElectionTypes;

/**
 * @author Lorcan Coyle and Dónal Doyle
 */
public class Datasets {
	/**
	 * The Constant for the Dublin West 2002 dataset
	 */
	public static final int					DUBLIN_WEST_2002	= 0;
	/**
	 * The Constant for the Dublin North 2002 dataset
	 */
	public static final int					DUBLIN_NORTH_2002	= 1;
	/**
	 * The Constant for the Meath 2002 dataset
	 */
	public static final int					MEATH_2002			= 2;
	/**
	 * The Constant for the European MiniElection dataset
	 */
	public static final int					EURO_MINI			= 3;
	/**
	 * The Constant for the Local MiniElection dataset
	 */
	public static final int					LOCAL_MINI			= 4;
	/**
	 * The Constant for the Town Council MiniElection dataset
	 */
	public static final int					TOWN_MINI			= 5;
	/**
	 * The filenames for the election datasets
	 */
	private static final String[]	FILENAMES			= {"Dublin West 2002.csv", "Dublin North 2002.csv", "Meath 2002.csv",
			"Euro_MiniElection.csv", "Local_MiniElection.csv", "Town_MiniElection.csv"};
	/**
	 * The number of seats for the election datasets
	 */
	private static final int[]		SEATNUMBERS			= {3, 4, 5, 3, 5, 9};
	/**
	 * The election type for the election datasets
	 */
	private static final int[]		ELECTIONTYPE		= {ElectionTypes.GENERAL_ELECTION, ElectionTypes.GENERAL_ELECTION,
			ElectionTypes.GENERAL_ELECTION, EURO_MINI, LOCAL_MINI, TOWN_MINI};

	/**
	 * Gets the filename of the appropriate election
	 * 
	 * @param election
	 *           the election
	 * @return the filename of the appropriate election
	 */
	public static String getFilename(int election) {
		return "data/" + FILENAMES[election];
	}

	/**
	 * Gets the type of the appropriate election (e.g. Dáil, European, etc)
	 * 
	 * @param election
	 *           the election
	 * @return the type of the appropriate election
	 */
	public static int getElectionType(int election) {
		return ELECTIONTYPE[election];
	}

	/**
	 * Gets the number of seats available in the appropriate election
	 * 
	 * @param election
	 *           the election
	 * @return the number of seats available in the appropriate election
	 */
	public static int getNumberOfSeats(int election) {
		return SEATNUMBERS[election];
	}
}
