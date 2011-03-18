/*
 * Created on 14-Nov-2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package testers;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.StringTokenizer;

public class TieAnalysis {

    private static final String ORIGINAL_TIES = "D:\\IES-Testdata\\OriginalTies";

    private static final String TESTED_TIES = "D:\\IES-Testdata\\TestedTies\\Pass";

    public TieAnalysis() {
        List origList = new ArrayList();
        List testedList = new ArrayList();
        List toDo = new ArrayList();

        File originalTies = new File(ORIGINAL_TIES);
        File testedTies = new File(TESTED_TIES);
        File[] subOrigTies = originalTies.listFiles();
        File[] subTestedTies = testedTies.listFiles();
        Arrays.sort(subOrigTies);
        Arrays.sort(subTestedTies);
        for (int i = 0; i < subOrigTies.length; i++) {
            File[] origDirs = subOrigTies[i].listFiles();
            File[] testedDirs = subTestedTies[i].listFiles();
            Arrays.sort(origDirs);
            Arrays.sort(testedDirs);
            for (int j = 0; j < origDirs.length; j++) {
                origList.add(origDirs[j]);
            }
            for (int j = 0; j < testedDirs.length; j++) {
                testedList.add(testedDirs[j].getName());
            }
        }

        int totalVotes = 0;
        int totalVotesLeft = 0;
        for (int i = 0; i < origList.size(); i++) {
            File origDir = (File) origList.get(i);
            String name = origDir.getName();
            StringTokenizer tokenizer = new StringTokenizer(name, " - ");
            tokenizer.nextToken();
            tokenizer.nextToken();
            tokenizer.nextToken();
            tokenizer.nextToken();
            String v = tokenizer.nextToken();
            int numOfVotes = Integer.valueOf(v).intValue();
            name = name.substring(name.indexOf("-"));
            totalVotes += numOfVotes;
            boolean found = false;

            // Try to find in testDirs;
            for (int k = 0; k < testedList.size(); k++) {
                String s = (String) testedList.get(k);
                if (s.indexOf(name) > -1) {
                    found = true;
                    break;
                }
            }

            if (!found) {
                totalVotesLeft += numOfVotes;
                toDo.add(origDir.getAbsolutePath());
            }
        }
             
        int percentElections = (int)((double)toDo.size()/(double)origList.size()*100.0);
        int percentVotes = (int)((double)totalVotesLeft/(double)totalVotes*100.0);
        System.out.println("Total number of Elections:\t\t    "+origList.size());
        System.out.println("Total number of Elections left:\t\t    "+toDo.size() +" ("+(100-percentElections)+"% complete)");
        System.out.println("Total number of Votes:\t\t\t"+totalVotes);
        System.out.println("Total number of Votes left:\t\t "+totalVotesLeft +" ("+(100-percentVotes)+"% complete)");
        // System.out.println(detailsBuilder);
        System.out.println();
        System.out.println();
        System.out.println();
        for (int i = 0; i < toDo.size(); i++) {
            System.out.println(toDo.get(i));
        }
    }

    /**
     * @param args
     */
    public static void main(String[] args) {
        new TieAnalysis();

    }

}
