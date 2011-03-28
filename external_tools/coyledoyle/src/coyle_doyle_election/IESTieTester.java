/*
 * Created on 30-Aug-2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package coyle_doyle_election;

import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

import javax.swing.JFrame;


/**
 * @author Administrator
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class IESTieTester extends JFrame{

 
    public IESTieTester(String votesMixNumberedPath, String voteLocationsIES, int numSeats, String electionType, String outputPath, String tieOrders){
		super("Java Code");
		pack();
		setVisible(true);
		String result = runTest(votesMixNumberedPath,voteLocationsIES,numSeats,electionType,outputPath,tieOrders);
		super.setTitle("Finished Test - " + result);

		addWindowListener(new WindowAdapter()
		{
			public void windowClosing(WindowEvent arg0)
			{
				System.exit(0);
			}
		});
    }
    
    private String runTest(String votesMixNumberedPath, String voteLocationsIES, int numSeats, String electionType, String outputPath, String tieOrders){
        boolean passed = true;
        List coyleDoyleStats = null; 
		
        try {
            ParseIESASC voteLocations = new ParseIESASC();
            List votes = voteLocations.parseFile(votesMixNumberedPath);
            String[] candidateNames = voteLocations.getCandidateNames();
            
            //Run our election software to calculate location of votes after final count
            int eType = -1;
            if(electionType.equals("EU"))
                eType = ElectionTypes.EUROPEAN_ELECTION;
            else if(electionType.equals("LO"))
                eType = ElectionTypes.LOCAL_ELECTION;
            else if(electionType.equals("GE"))
                eType = ElectionTypes.GENERAL_ELECTION;
            
            
            List ties = new ArrayList();
            StringTokenizer tiesTokenizer = new StringTokenizer(tieOrders,"-");
            while(tiesTokenizer.hasMoreElements()){
                String tie = tiesTokenizer.nextToken();
                List list = new ArrayList();
                StringTokenizer tieTokenizer = new StringTokenizer(tie,"_");
                while(tieTokenizer.hasMoreElements()){
                    String s = tieTokenizer.nextToken();
                    list.add(new Integer(s));
                }
                int[] t = new int[list.size()];
                for (int i = 0; i < t.length; i++) {
                    t[i] = ((Integer)list.get(i)).intValue();
                }
                ties.add(t);
            }
            
            coyleDoyleStats = runCoyleDoyleAlgorithm(candidateNames,numSeats,eType,votes,ties);
            if(coyleDoyleStats==null){
                return "Exception";
            }
                
            					
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
            return "Exception";
        }   
             
		try 
		{    
			BufferedWriter out = new BufferedWriter(new FileWriter(outputPath));
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
        if(passed)
            return "Passed";
        else
            return "Failed";
    }
    
    private List runCoyleDoyleAlgorithm(String[] candidateNames, int numSeats, int electionType, List votes, List ties){
        try {
            Election election = new Election(candidateNames, numSeats, electionType);
            election.setUserAssistedTies(false);
            election.setPrint(false);
            election.setTieOrders(ties);
            election.election(votes);
            List coyleDoyleStats = election.getStats();
            return coyleDoyleStats;
        } catch (Exception e) {
            e.printStackTrace();
            return null;
        }
    }
    
	public static void main(String[] args)
	{
		if (args.length != 6) {
			System.out.println("The correct usage of the Tester is\njava IESTieTester votesMixNumberedPath voteLocationsIES electionType numSeats outputPath tieOrders");
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
	    String tieOrders = args[5];
		new IESTieTester(votesMixNumberedPath,voteLocationsIES,numSeats,electionType,outputPath,tieOrders);
	}
}
