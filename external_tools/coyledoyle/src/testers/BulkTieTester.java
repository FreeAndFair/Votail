/*
 * Created on 14-Nov-2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package testers;

import java.io.BufferedWriter;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.List;
import java.util.StringTokenizer;

import coyle_doyle_election.CandidateStats;
import coyle_doyle_election.Election;
import coyle_doyle_election.ElectionTypes;
import coyle_doyle_election.FileUtils;
import coyle_doyle_election.ParseIESASC;
import coyle_doyle_election.ParseIESVotes;


public class BulkTieTester {
    
    public static final String testedPath = "D:\\IES-Testdata\\Phase 1\\TiedElections\\Pass\\";
    StringBuffer fails = new StringBuffer();
    StringBuffer exceptions = new StringBuffer();

    public BulkTieTester(){
        long startTime = System.currentTimeMillis();
        int numPasses = 0;
        int numFails = 0;
        int numElections = 0;
        File testedDir = new File(testedPath);
        File[] subTestedDirs = testedDir.listFiles();
        
        try {
            File outputFile = new File(testedPath+"\\summary.txt");
            outputFile.createNewFile();
            FileOutputStream out = new FileOutputStream(outputFile);
            DataOutputStream dataOut = new DataOutputStream(out);  

//            File namesFile = new File(testedPath+"\\names.txt");
//            namesFile.createNewFile();
//            FileOutputStream namesOut = new FileOutputStream(namesFile);
//            DataOutputStream namesDataOut = new DataOutputStream(namesOut);  
            String output = "";
            
            for (int i = 0; i < subTestedDirs.length; i++) {
                File subTestedDir = subTestedDirs[i];
                if(!subTestedDir.isDirectory()){
                    continue;
                }
                File[] dirs = subTestedDir.listFiles();
                for (int j = 0; j < dirs.length; j++) {
                    File dir = dirs[j];
                    int numOldErrors = 0;
                    
                    String dirName = dir.getName();
                    StringTokenizer tokenizer = new StringTokenizer(dirName," - ");
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
    
                    
                    ParseIESASC pA = new ParseIESASC();
                    List votes = pA.parseFile(dir.getAbsolutePath()+"\\votesMixNumbered.asc");
                    
                    String[] candidateNames = pA.getCandidateNames();
                    
                    //Repeat for each permutation
                    File[] permutationFolders = dir.listFiles();
                    int numPermutations = 0;
                    for (int k = 0; k < permutationFolders.length; k++) {
                        File permuationFolder = permutationFolders[k];
                        if(!permuationFolder.isDirectory())
                            continue;
                        numPermutations++;
                        String folderName = permuationFolder.getName();
                        int index1 = folderName.indexOf("+")+1;
                        int index2 = folderName.indexOf("+",index1);
                        String tieOrders = folderName.substring(index1,index2);
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
                            for (int m = 0; m < t.length; m++) {
                                t[m] = ((Integer)list.get(m)).intValue();
                            }
                            ties.add(t);
                        }
                        
                        Election election = new Election(candidateNames,numSeats,eType);
                        election.setPrint(false);
                        election.setUserAssistedTies(false);
                        election.setTieOrders(ties);
                        election.election(votes);
                        List coyleDoyleStats = election.getStats();
                        if(election.isOldRoundingError()){
                               numOldErrors++;
                        }
                        
//                        BufferedWriter cdOut = new BufferedWriter(
//                                new FileWriter(permuationFolder.getAbsolutePath()
//                                        + "\\coyleDoyle.txt"));
//                        for (int w = 0; w < coyleDoyleStats.size(); w++) {
//                            StringBuffer buffer = new StringBuffer();
//                            CandidateStats tcdCandidate = (CandidateStats) coyleDoyleStats
//                                    .get(w);
//                            buffer.append(tcdCandidate.getAllVotes());
//                            cdOut.write(buffer.toString());
//                        }
//                        cdOut.close();

    
                        
                        ParseIESVotes parseIESVotes = new ParseIESVotes(permuationFolder.getAbsolutePath()+"\\voteLocationsIES.txt");
                        List iesStats = parseIESVotes.getStats();
                        parseIESVotes.close();
                        
                        if(coyleDoyleStats.equals(iesStats)){
                            numPasses++;
                        } else {
                            System.out.println("Failed:\t"+ permuationFolder.getAbsolutePath());                        
                            numFails++;
                            fails.append(dir.getAbsoluteFile()+"\n");
                        }
                        
//                        String newName = permuationFolder.getAbsolutePath();
//                        newName = newName.replaceAll(" - Finished Test - Passed","");
//                        File newDir = new File(newName);
//                        if(!permuationFolder.renameTo(newDir)){
//                            System.out.print("ERROR: RENAMING FOLDER " + permuationFolder.getAbsolutePath() + " TO " + newDir.getAbsolutePath());
//                            exceptions.append("ERROR: RENAMING FOLDER " + permuationFolder.getAbsolutePath() + " TO " + newDir.getAbsolutePath()+"\n");
//                        }                       
                    }
                    numElections++;
                    if(numElections%100 == 0){
                        System.out.println(numElections+" folders tested - Passes: " + numPasses + " Fails: " + numFails);
                    }
                    
                    
                    String newDirName = String.valueOf(numElections);
                    while(newDirName.length()<4){
                        newDirName = "0"+newDirName;
                    }
                    
                    newDirName = "T"+newDirName;
                    
//                    File newDir = new File(subTestedDir.getAbsolutePath()+"\\"+newDirName+"-"+electionType+"-"+nSeats+"-"+candidateNames.length+"-"+votes.size());
                    String oldv131Error = "";
                    if(numOldErrors>0){
                        oldv131Error = ","+numOldErrors + " OldError";
                        if(numOldErrors>1)
                            oldv131Error = oldv131Error +"s";
                    }
//                    String change = dir.getAbsolutePath() + "\t" + newDir.getAbsolutePath()+"\n";
//                    byte[] namesData = change.getBytes();
//                    namesDataOut.write(namesData,0,namesData.length);
                    
//                    if(!dir.renameTo(newDir)){
//                        System.out.print("ERROR: RENAMING FOLDER " + dir.getAbsolutePath() + " TO " + newDir.getAbsolutePath());
//                        exceptions.append("ERROR: RENAMING FOLDER " + dir.getAbsolutePath() + " TO " + newDir.getAbsolutePath()+"\n");
                        output = electionType+","+nSeats+","+candidateNames.length+","+votes.size()+","+numPermutations+oldv131Error+","+subTestedDir.getName()+"\\"+dir.getName()+"\r";
//                    } else {
//                        output = electionType+","+nSeats+","+candidateNames.length+","+votes.size()+","+numPermutations+oldv131Error+","+subTestedDir.getName()+"\\"+newDir.getName()+"\r";
//                    }
                    byte[] data = output.getBytes();
                    dataOut.write(data, 0 , data.length);
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        }      
        long endTime = System.currentTimeMillis();
        long time = endTime - startTime;
        StringBuffer output = new StringBuffer();
        output.append(numElections+" folders tested - Passes: " + numPasses + " Fails: " + numFails + "\t\t"+ (time/1000) + "(s)\n\n");
        output.append("Fails\n"+fails.toString()+"\n\n");
        output.append("Exceptions\n");
        output.append(exceptions.toString());
        System.out.println(output);
        FileUtils.outputFile(new File("c:\\outputTieTester.txt"),output.toString());   
    }
    
    /**
     * @param args
     */
    public static void main(String[] args) {
        new BulkTieTester();
        // TODO Auto-generated method stub

    }

}
