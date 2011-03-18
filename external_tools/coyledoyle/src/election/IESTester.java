/*
 * Created on 30-Aug-2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package election;

import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
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

import javax.swing.JFrame;


/**
 * @author Administrator
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class IESTester extends JFrame{

    private static Random rn = new Random();
    boolean containedTies = false;
    boolean containedOldError = true;
    String[] months = {"JAN","FEB","MAR","APR","MAY","JUN","JUL","AUG","SEP","OCT","NOV","DEC"};
    
    public IESTester(String votesMixNumberedPath, String voteLocationsIES, int numSeats, String electionType, String outputPath, boolean userAssistedTies, String code){
		super("Java Code");
		pack();
		show();
		String result = runTest(votesMixNumberedPath,voteLocationsIES,numSeats,electionType,outputPath,userAssistedTies,code);
		super.setTitle("Finished Test - "+result);

		addWindowListener(new WindowAdapter()
		{
			public void windowClosing(WindowEvent arg0)
			{
				System.exit(0);
			}
		});
    }
    
    private String runTest(String votesMixNumberedPath, String voteLocationsIES, int numSeats, String electionType, String outputPath, boolean userAssistedTies, String code){
        String result = "";
        boolean passed = true;
        boolean exception = false;
        int numVotes = 0;
        List coyleDoyleStats = null; 
		
        try {
            ParseIESASC voteLocations = new ParseIESASC();
            List votes = voteLocations.parseFile(votesMixNumberedPath);
            String[] candidateNames = voteLocations.getCandidateNames();
            numVotes = votes.size();
            
            //Run our election software to calculate location of votes after final count
            int eType = -1;
            if(electionType.equals("EU"))
                eType = ElectionTypes.EUROPEAN_ELECTION;
            else if(electionType.equals("LO"))
                eType = ElectionTypes.LOCAL_ELECTION;
            else if(electionType.equals("GE"))
                eType = ElectionTypes.GENERAL_ELECTION;
            
            coyleDoyleStats = runCoyleDoyleAlgorithm(candidateNames,numSeats,eType,votes,userAssistedTies);
            					
            //Parse Location of Votes given by IES Location of Votes after final count
            ParseIESVotes p = new ParseIESVotes(voteLocationsIES);
            List iesStats = p.getStats();
            
            //Compare location of Votes between Coyle Doyle Implementation and the IES implementation
            for (int i = 0; i < coyleDoyleStats.size() ; i++)
            {
            	CandidateStats tcdCandidate = (CandidateStats)coyleDoyleStats.get(i);
            	if(i==iesStats.size()){
            	    if(tcdCandidate.getCandidateName().equals("non-transferable not effective")){
            	        break;
            	    }
            	}
            	CandidateStats iesCandidate = (CandidateStats)iesStats.get(i);
            	if(!tcdCandidate.equals(iesCandidate))
            		passed = false;
            }
        } catch (RuntimeException e) {
            exception = true;
            e.printStackTrace();
        }   
		
		//Set saving path
		Calendar C = Calendar.getInstance();
		int hour = C.get(Calendar.HOUR_OF_DAY);
		int day = C.get(Calendar.DAY_OF_MONTH);
		int min = C.get(Calendar.MINUTE);
		int month = C.get(Calendar.MONTH);
		int sec = C.get(Calendar.SECOND);
		String sDay = String.valueOf(day);
		String sHour = String.valueOf(hour);
		String sMin = String.valueOf(min);
		String sSec = String.valueOf(sec);
		if(sHour.length()==1)
			sHour = "0" + sHour;
		if(sMin.length()==1)
			sMin = "0" + sMin;
		if(sDay.length()==1)
			sDay = "0" + sDay;
		if(sSec.length()==1)
			sSec = "0" + sSec;
		outputPath = outputPath + "\\";
		String randomEnd = randomstring(6,6);
		if(exception){
		    outputPath = outputPath + "Exception - " + electionType + " - " + numSeats + " - " + numVotes + " - " + sDay + months[month] + sHour + sMin + sSec + " - " + code;
		    result = "Exception";
		} else if(passed){
		    outputPath = outputPath + "Passed - " + electionType + " - " + numSeats + " - " + numVotes + " - " + sDay + months[month] + sHour + sMin + sSec + " - " + code;
		    result = "Pass";
		}else{
		    outputPath = outputPath + "Failed - " + electionType + " - " + numSeats + " - " + numVotes + " - " + sDay + months[month] + sHour + sMin + sSec + " - " + code;
		    result = "Fail";
		}
		if(containedTies)
			outputPath = outputPath + " - Tie";
		if(containedOldError)
			outputPath = outputPath + " - OldError";
		outputPath = outputPath + "\\";
		System.out.println(outputPath);
		File f = new File(outputPath);
		if(!f.exists())
			f.mkdir();
		
		//Copy output to the output folder
		try 
		{    
			//Copy votes location 
			FileChannel srcChannel = new FileInputStream(voteLocationsIES).getChannel();
			FileChannel dstChannel = new FileOutputStream(outputPath+(new File (voteLocationsIES)).getName()).getChannel();            
			dstChannel.transferFrom(srcChannel, 0, srcChannel.size());            
			srcChannel.close();        
			dstChannel.close();    
			
			//Copy votes mixed and numbered
			srcChannel = new FileInputStream(votesMixNumberedPath).getChannel();
			dstChannel = new FileOutputStream(outputPath+(new File (votesMixNumberedPath)).getName()).getChannel();            
			dstChannel.transferFrom(srcChannel, 0, srcChannel.size());            
			srcChannel.close();        
			dstChannel.close();    
			
			BufferedWriter out = new BufferedWriter(new FileWriter(outputPath+"coyleDoyle.txt"));
			for (int i = 0; i < coyleDoyleStats.size() ; i++)
			{
				StringBuffer buffer = new StringBuffer();
				CandidateStats tcdCandidate = (CandidateStats)coyleDoyleStats.get(i);
				buffer.append(tcdCandidate.getAllVotes());
				out.write(buffer.toString());
			}
			out.flush();
			out.close();
		} 
		catch (IOException e) { e.printStackTrace();   }
		return result;
    }
    
    private List runCoyleDoyleAlgorithm(String[] candidateNames, int numSeats, int electionType, List votes, boolean userAssistedTies){
        Election election = new Election(candidateNames, numSeats, electionType);
        election.setUserAssistedTies(false);
		election.election(votes);
		containedTies = election.isElectionContainedTies();
		containedOldError = election.isOldRoundingError();
		List coyleDoyleStats = election.getStats();
		return coyleDoyleStats;
    }
    
    public static int rand(int lo, int hi)
    {
            int n = hi - lo + 1;
            int i = rn.nextInt() % n;
            if (i < 0)
                    i = -i;
            return lo + i;
    }
    
    public static String randomstring(int lo, int hi)
    {
            int n = rand(lo, hi);
            byte b[] = new byte[n];
            for (int i = 0; i < n; i++)
                    b[i] = (byte)rand('a', 'z');
            return new String(b);
    }
    
	public static void main(String[] args)
	{
		if (args.length != 6 && args.length != 7) {
			System.out.println("The correct usage of the Tester is\njava IESTester votesMixNumberedPath voteLocationsIES electionType numSeats outputPath userAssistedTies [code] [rand]");
			for (int i = 0; i < args.length; i++) {
			    System.out.println("args["+i+"] = " + args[i]);
			}
			return;
		}
	    String votesMixNumberedPath = args[0]; 
	    String voteLocationsIES  = args[1];
	    String electionType = args[2];
	    int numSeats = Integer.parseInt(args[3]);
	    String outputPath = args[4];
	    boolean userAssistedTies = (new Boolean(args[5])).booleanValue();
	    String code = "RE - MANU";
	    if(args.length==7)
	        code = args[6];
		new IESTester(votesMixNumberedPath,voteLocationsIES,numSeats,electionType,outputPath,userAssistedTies,code);
	}
}
