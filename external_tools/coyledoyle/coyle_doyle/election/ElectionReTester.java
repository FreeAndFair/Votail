/*
 * Created on 08-Oct-2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package coyle_doyle.election;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.util.List;
import java.util.StringTokenizer;

/**
 * @author Administrator
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class ElectionReTester {
    
    private List tieOrders;
    
    public int differenceType;

    public boolean testFolder(File folder, int numOfSeats, int electionType) {
        return testFolder(folder, numOfSeats, electionType, true, true);
    }
    
    public boolean testFolder(File folder, int numOfSeats, int electionType, boolean print, boolean userAssistedTies) {
        return testFolder(folder, numOfSeats, electionType, print, userAssistedTies, null);
    }
    
    /**
     * 
     */
    public boolean testFolder(File folder, int numOfSeats, int electionType, boolean print, boolean userAssistedTies, List tieOrders) {
        try{
            ParseIESASC pA = new ParseIESASC();
            List votes = pA.parseFile(folder.toString() + "/" + "votesMixNumbered.asc");
            String[] candidateNames = pA.getCandidateNames();
    
            Election counter = new Election(candidateNames, numOfSeats, electionType);
            counter.setPrint(print);
            counter.setUserAssistedTies(userAssistedTies);
            counter.setTieOrders(tieOrders);
            
            counter.election(votes);
            List coyleDoyleStats = counter.getStats();
            this.tieOrders = counter.getTieOrders();
                
            ParseIESVotes p = new ParseIESVotes(folder.toString() + "/" + "voteLocationsIES.txt");
            List iesStats = p.getStats();
                
            boolean passed = true;
            for (int i = 0; i < coyleDoyleStats.size() ; i++)
            {
                differenceType = -1;
                CandidateStats tcdCandidate = (CandidateStats)coyleDoyleStats.get(i);
                CandidateStats iesCandidate = (CandidateStats)iesStats.get(i);
                if(!tcdCandidate.equals(iesCandidate))
                {
                    differenceType = tcdCandidate.getDifferenceType();
                    passed = false;
                    System.out.println("Failed Folder: " + folder.toString());
                    System.out.println();
                    break;
                }
            }
            
            BufferedWriter out = new BufferedWriter(new FileWriter(folder.getAbsolutePath()+"\\coyleDoyle.txt"));
            for (int i = 0; i < coyleDoyleStats.size() ; i++)
            {
                StringBuffer buffer = new StringBuffer();
                CandidateStats tcdCandidate = (CandidateStats)coyleDoyleStats.get(i);
                buffer.append(tcdCandidate.getAllVotes());
                out.write(buffer.toString());
            }
            return passed;
        }catch (Exception e) {
            e.printStackTrace();
            return false;
        }
    }

    public int getDifferenceType() {
        return differenceType;
    }
    
    public List getTieOrders(){
        return tieOrders;
    }
    
    public static void main(String[] args) {
        //LORCAN: Change this to test folder
        String folder = "D:\\IES-Testdata\\Phase 2\\MiniatureElection\\Results\\TownCouncil - LO - 9 - 16 - 10";
        if(args.length>=1){
            folder = args[0];
        }
        String folderName = folder.substring(folder.lastIndexOf("\\")+1);
        StringTokenizer tokenizer = new StringTokenizer(folderName," - ");
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
        ElectionReTester electionReTester =  new ElectionReTester();
        boolean passed = electionReTester.testFolder(new File(folder),numSeats,eType);
        System.out.println(passed);
    }
    
}
