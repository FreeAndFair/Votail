/*
 * Created on 21-Nov-2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package testers;

import java.io.DataOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.util.Arrays;
import java.util.StringTokenizer;

import election.FileUtils;
import election.TieIterator;

public class StatsCollector {

    static String normalPath = "D:\\IES-Testdata\\Passed";
    static String tiesPath = "D:\\IES-Testdata\\OriginalTies";
    
    public static void analyseFolder(String folderPath, File outputFile, boolean tieFolder){
        File testedDir = new File(folderPath);
        File[] subTestedDirs = testedDir.listFiles();
        Arrays.sort(subTestedDirs);

        byte[] data;
        try {
            outputFile.createNewFile();
            FileOutputStream out = new FileOutputStream(outputFile);
            DataOutputStream dataOut = new DataOutputStream(out);           
            for (int i = 0; i < subTestedDirs.length; i++) {
                File subTestedDir = subTestedDirs[i];
                System.out.println(subTestedDir.getName());
                File[] dirs = subTestedDir.listFiles();
                for (int j = 0; j < dirs.length; j++) {
                    File dir = dirs[j];
               
                        String dirName = dir.getName();
                        StringTokenizer tokenizer = new StringTokenizer(dirName," - ");
                        tokenizer.nextToken();
                        String electionType = tokenizer.nextToken();
                        String nSeats = tokenizer.nextToken();
                        String numCandidates = tokenizer.nextToken();
                        String output = electionType+","+nSeats+","+numCandidates;
                        if(tieFolder){
                            TieIterator iterator = new TieIterator();
                            iterator.testFolder(dir);
                            output = output + ","+iterator.getNumElections();
                        }
                        output = output + "\n";
                        data = output.getBytes();
                        dataOut.write(data, 0 , data.length);
                }
            }
            out.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
    
    /**
     * @param args
     */
    public static void main(String[] args) {
        // TODO Auto-generated method stub
        analyseFolder(normalPath,new File("c:\\elections.txt"),false);
        analyseFolder(tiesPath,new File("c:\\electionTies.txt"),true);
    }

}
