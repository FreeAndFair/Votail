/*
 * Created on 14-Nov-2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package coyle_doyle.testers;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.BufferedWriter;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.StringTokenizer;

import javax.swing.JButton;
import javax.swing.JFrame;

import coyle_doyle.election.CandidateStats;
import coyle_doyle.election.Election;
import coyle_doyle.election.ElectionTypes;
import coyle_doyle.election.FileUtils;
import coyle_doyle.election.ParseIESASC;
import coyle_doyle.election.ParseIESVotes;
import coyle_doyle.election.TieIterator;


public class BulkTester {
    
    public static final String testedPath = "D:\\IES-Testdata\\Phase 1\\OldErrorTesting\\";
    StringBuffer fails = new StringBuffer();
    StringBuffer exceptions = new StringBuffer();
    int numPasses = 0;
    int numFails = 0;
    int numElections = 0;
    long startTime = 0;
    
    public BulkTester(){
        JFrame frame = new JFrame("Tester");
        
        JButton button = new JButton("Print");
        button.addActionListener(new ActionListener() {
        
            public void actionPerformed(ActionEvent arg0) {
                printInfo();
            }
        
        });
        frame.add(button);
        frame.pack();
        frame.setVisible(true);
        startTime = System.currentTimeMillis();
        long lastEndTime = startTime;
        File testedDir = new File(testedPath);
        File[] subTestedDirs = testedDir.listFiles();
        Arrays.sort(subTestedDirs);
        String output = "";
        int count = 0;
        try {
            File outputFile = new File(testedPath+"\\summary.txt");
            outputFile.createNewFile();
            FileOutputStream out = new FileOutputStream(outputFile);
            DataOutputStream dataOut = new DataOutputStream(out);  

//            File namesFile = new File(testedPath+"\\names.txt");
//            namesFile.createNewFile();
//            FileOutputStream namesOut = new FileOutputStream(namesFile);
//            DataOutputStream namesDataOut = new DataOutputStream(namesOut);  
            
            for (int i = 0; i < subTestedDirs.length; i++) {
                File subTestedDir = subTestedDirs[i];
                if(!subTestedDir.isDirectory()){
                    continue;
                }
                File[] dirs = subTestedDir.listFiles();
                for (int j = 0; j < dirs.length; j++) {
                    File dir = dirs[j];
                    try {
               
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
                        
                        
                           
                        Election election = new Election(candidateNames,numSeats,eType);
                        election.setPrint(false);
                        election.setUserAssistedTies(false);
                        election.election(votes);
                        List coyleDoyleStats = election.getStats();
                        String oldv131Error = "";
                        if(election.isOldRoundingError()){
                            oldv131Error = ",OldError";
                            System.out.print("FOUND ONE");
                        }
//                        BufferedWriter cdOut = new BufferedWriter(new FileWriter(dir.getAbsolutePath()+"\\coyleDoyle.txt"));
//                        for (int w = 0; w < coyleDoyleStats.size() ; w++)
//                        {
//                            StringBuffer buffer = new StringBuffer();
//                            CandidateStats tcdCandidate = (CandidateStats)coyleDoyleStats.get(w);
//                            buffer.append(tcdCandidate.getAllVotes());
//                            cdOut.write(buffer.toString());
//                        }
//                        cdOut.close();
                        
    
                        
                        ParseIESVotes parseIESVotes = new ParseIESVotes(dir.getAbsolutePath()+"\\voteLocationsIES.txt");
                        List iesStats = parseIESVotes.getStats();
                        parseIESVotes.close();
                        
                        if(coyleDoyleStats.equals(iesStats)){
                            numPasses++;
                        } else {
                            System.out.println("Failed:\t"+ dir.getAbsolutePath());                        
                            numFails++;
                            fails.append(dir.getAbsoluteFile()+"\n");
                        }
    
                        count++;
                        String newDirName = String.valueOf(count);
                        while(newDirName.length()<6){
                            newDirName = "0"+newDirName;
                        }
                        
//                        File newDir = new File(subTestedDir.getAbsolutePath()+"\\"+newDirName+"-"+electionType+"-"+nSeats+"-"+candidateNames.length+"-"+votes.size());
                        output = electionType+","+nSeats+","+candidateNames.length+","+votes.size()+oldv131Error+","+subTestedDir.getName()+"\\"+dir.getName()+"\r";
                        byte[] data = output.getBytes();
                        dataOut.write(data, 0 , data.length);
                        
//                        String change = dir.getAbsolutePath() + "\t" + newDir.getAbsolutePath()+"\n";
//                        byte[] namesData = change.getBytes();
//                        namesDataOut.write(namesData,0,namesData.length);
                        
//                        if(!dir.renameTo(newDir)){
//                            System.out.print("ERROR: RENAMING FOLDER " + dir.getAbsolutePath() + " TO " + newDir.getAbsolutePath());
//                            exceptions.append("ERROR: RENAMING FOLDER " + dir.getAbsolutePath() + " TO " + newDir.getAbsolutePath());
//                        }
                    } catch (Exception e) {
                        System.out.println(e.getMessage()+"\t"+dir);
                        exceptions.append(dir.getAbsoluteFile()+"\n");
                    }
                    
                    
                    
                    
                    numElections++;
                    if(numElections%1000 == 0){
                        long time = System.currentTimeMillis();
                        long length = time - lastEndTime;
                        lastEndTime = time;
                        length = length/1000;
                        System.out.println(numElections+" folders tested - Passes: " + numPasses + " Fails: " + numFails + "\t\t"+ length + "(s)");
                    }
                }
            }
    
            printInfo();
        } catch (Exception e) {
            e.printStackTrace();
        }

    }
    
    private void printInfo(){
        long endTime = System.currentTimeMillis();
        long time = endTime - startTime;
        StringBuffer output = new StringBuffer();
        output.append(numElections+" folders tested - Passes: " + numPasses + " Fails: " + numFails + "\t\t"+ (time/1000) + "(s)\n\n");
        output.append("Fails\n"+fails.toString()+"\n\n");
        output.append("Exceptions\n");
        output.append(exceptions.toString());
        System.out.println(output);
        FileUtils.outputFile(new File("c:\\outputTester.txt"),output.toString());       
    }
    
    /**
     * @param args
     */
    public static void main(String[] args) {
        new BulkTester();
        // TODO Auto-generated method stub

    }

}
