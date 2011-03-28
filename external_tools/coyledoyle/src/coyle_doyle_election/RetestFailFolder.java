/*
 * Created on 10-Oct-2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package coyle_doyle_election;

import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.StringTokenizer;

import javax.swing.JFrame;


/**
 * @author Administrator
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class RetestFailFolder {
    
    static String retestFolderPath = "D:\\IES-Testdata\\Fails\\fails";
    static String emptyFileFolder = "D:\\IES-Testdata\\Fails\\emptyFiles\\";
    static String missingVotesFolder = "D:\\IES-Testdata\\Fails\\missingVotes\\";
    static String newPassFolder = "D:\\IES-Testdata\\Fails\\newPass\\";
    static String stillFailFolder = "D:\\IES-Testdata\\Fails\\stillFailing\\";
    static String emptyFolder = "D:\\IES-Testdata\\Fails\\emptyFolder\\";
    static boolean run = true;
    
    public static boolean testFolder(){
        JFrame frame = new JFrame();
        frame.addWindowListener(new WindowAdapter(){
			public void windowClosing(WindowEvent e)
			{
				if(run)
				    run =false;
				else
				    System.exit(0);
			}
		});
		frame.setVisible(true);
        File retestFolder = new File(retestFolderPath);
        File[] subFolders = retestFolder.listFiles();
        Arrays.sort(subFolders);
        StringBuffer buffer = new StringBuffer();
        boolean passed = true;
        for (int i = 0; i < subFolders.length && run; i++){
            if(i%100==0)
                System.out.println(i+" complete");
            File subFolder = subFolders[i];
            System.out.println(subFolder.getName());
            
            //Check that the folder is not empty
            File[] folderFiles = subFolder.listFiles();
            if(folderFiles.length==0){
                String name = subFolder.getName();
                String moveFolder = emptyFolder+name;
                try {
                    FileUtils.moveDir(subFolder.getAbsolutePath(),moveFolder);
                } catch (IOException e) {
                    e.printStackTrace();
                }                    
                continue;                
            }
            
            //Check if IES Vote location is empty
            File iesFile = new File(subFolder+"\\voteLocationsIES.txt");
            if(iesFile.length()==0){
                String name = subFolder.getName();
                String moveFolder = emptyFileFolder+name;
                try {
                    FileUtils.moveDir(subFolder.getAbsolutePath(),moveFolder);
                } catch (IOException e) {
                    e.printStackTrace();
                }                    
                continue;
            }

            //Check if Mixed Numbered Vote location is empty
            File ascFile = new File(subFolder+"\\votesMixNumbered.asc");
            if(ascFile.length()==0){
                String name = subFolder.getName();
                String moveFolder = emptyFileFolder+name;
                try {
                    FileUtils.moveDir(subFolder.getAbsolutePath(),moveFolder);
                } catch (IOException e) {
                    e.printStackTrace();
                }                    
                continue;
            }
            
            
            StringTokenizer tokenizer = new StringTokenizer(subFolder.getName().toString()," - ");
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
            passed = electionReTester.testFolder(subFolder,numSeats,eType,false,false,null);
            
            if(passed){
                String name = subFolder.getName();
                String moveFolder = newPassFolder+name.replaceAll("Failed","Passed");
                moveFolder = moveFolder.replaceAll("Exception","Passed");
                try {
                    FileUtils.moveDir(subFolder.getAbsolutePath(),moveFolder);
                } catch (IOException e) {
                    e.printStackTrace();
                }
            } else {
                int differenceType = electionReTester.getDifferenceType();
                if(differenceType == CandidateStats.INCORRECT_VOTE_NUMBERS){
                    String name = subFolder.getName();
                    String moveFolder = missingVotesFolder+name;
                    try {
                        FileUtils.moveDir(subFolder.getAbsolutePath(),moveFolder);
                    } catch (IOException e) {
                        e.printStackTrace();
                    }                    
                } else{
//                    String name = subFolder.getName();
//                    String moveFolder = stillFailFolder+name;
//                    try {
//                        FileUtils.moveDir(subFolder.getAbsolutePath(),moveFolder);
//                    } catch (IOException e) {
//                        e.printStackTrace();
//                    }             
                }
            } 
            buffer.append(passed + "\t" + subFolder.getName().toString() + "\t" + passed + "\n");
        }        
        System.out.println(buffer);
        return passed;
    }
    
    public static void main(String[] args) {
        RetestFailFolder.testFolder();
    }

}
