/*
 * Created on 08-Oct-2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package election;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;
import java.util.StringTokenizer;

/**
 * @author Administrator
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class ElectionTieReTester {
    
   
    
    static String path = "D:\\TestedTies\\Pass\\T4";
    
    static String folder = "Passed - EU - 5 - 8 - 8100 - 19OCT044735 - IT - YOGIBEAR8811565032 - Tie";
    
    static String output = "CoyleDoyle+2_1+IES+1_2 - Finished Test - Failed";    
    
    /**
     * 
     */
    public boolean testFolder(File mixNumbered, File iesOutput, File coyleDoyleOutput, int numOfSeats, int electionType) {
        try{
            ParseIESASC pA = new ParseIESASC();
            List votes = pA.parseFile(mixNumbered);
            String[] candidateNames = pA.getCandidateNames();
    
            Election counter = new Election(candidateNames, numOfSeats, electionType);
            counter.setPrint(true);
            counter.setUserAssistedTies(true);            
            counter.election(votes);
            List tcdStats = counter.getStats();
                
            ParseIESVotes p = new ParseIESVotes(iesOutput);
            List iesStats = p.getStats();
                
            boolean passed = true;
            for (int i = 0; i < tcdStats.size() ; i++)
            {
                CandidateStats tcdCandidate = (CandidateStats)tcdStats.get(i);
                CandidateStats iesCandidate = (CandidateStats)iesStats.get(i);
                if(!tcdCandidate.equals(iesCandidate))
                {
                    passed = false;
                }
            }
            if(passed){
                try 
                {    
                    BufferedWriter out = new BufferedWriter(new FileWriter(coyleDoyleOutput));
                    for (int i = 0; i < tcdStats.size() ; i++)
                    {
                        StringBuffer buffer = new StringBuffer();
                        CandidateStats tcdCandidate = (CandidateStats)tcdStats.get(i);
                        buffer.append(tcdCandidate.getAllVotes());
                        out.write(buffer.toString());
                    }
                    out.flush();
                    out.close();
                } 
                catch (IOException e) { e.printStackTrace();   }
            }
            return passed;
        }catch (Exception e) {
            e.printStackTrace();
            return false;
        }
    }
    
    public static void main(String[] args) {
        //LORCAN: Change this to test folder
        StringTokenizer tokenizer = new StringTokenizer(folder," - ");
        tokenizer.nextToken();
        String electionType = (String)tokenizer.nextToken();
        String nSeats = (String)tokenizer.nextToken();
        int numSeats = (new Integer(nSeats)).intValue();
        int eType = -1;
        if(electionType.equals("EU"))
            eType = ElectionTypes.EUROPEAN_ELECTION;
        else if(electionType.equals("LO"))
            eType = ElectionTypes.LOCAL_ELECTION;
        else if(electionType.equals("GE"))
            eType = ElectionTypes.GENERAL_ELECTION;
        ElectionTieReTester electionTieReTester =  new ElectionTieReTester();
        File mixNumbered = new File(path+"\\"+folder+"\\votesMixNumbered.asc");
        File iesOutput = new File(path+"\\"+folder+"\\"+output+"\\voteLocationsIES.txt");
        File coyleDoyleOutput = new File(path+"\\"+folder+"\\"+output+"\\coyleDoyle.txt");
        boolean passed = electionTieReTester.testFolder(mixNumbered,iesOutput,coyleDoyleOutput,numSeats,eType);
        System.out.println(passed);
    }
    
}
