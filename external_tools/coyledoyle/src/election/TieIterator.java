/*
 * Created on 15-Oct-2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package election;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

/**
 * @author Administrator
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class TieIterator {
    
//    static String tiesFolder = "D:\\IES-Testdata\\PreparedTies";
//    static String tiesFolder = "D:\\IES-Testdata\\ATie";
    static boolean print = false;
    static boolean userAssistedTies = false;
    private  List orders;
    private int numElections;
   
    public void testFolders(File[] folders){
        for (int i = 0; i < folders.length; i++) {
            testFolder(folders[i]);
            System.out.println("Testing\t" + folders[i].getName()+"\n");
            
            System.out.print(getOrders());
        }
    }
    
    public List testFolder(File folder){
        orders = new ArrayList();
        List ties = new ArrayList();

		StringTokenizer tokenizer = new StringTokenizer(folder.getName().toString()," - ");
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
		List votes = pA.parseFile(folder.toString() + "/" + "votesMixNumbered.asc");
		String[] candidateNames = pA.getCandidateNames();
		
		getPermutations(candidateNames,numSeats,eType,votes);
        ties = orders;
		return ties;
    }

    private void getPermutations(String[] candidateNames, int numSeats, int eType, List votes){
        getPermutations(candidateNames, numSeats, eType, votes, new ArrayList(), 0);
    }
    
    private void getPermutations(String[] candidateNames, int numSeats, int eType, List votes, List currentTieOrder, int tieNumber){
		Election election = new Election(candidateNames,numSeats,eType);
        election.setPrint(print);
        election.setUserAssistedTies(userAssistedTies);
        
		election.setTieOrders((List)((ArrayList)currentTieOrder).clone());
        election.election(votes);
        List tieOrder = election.getTieOrders();
        if(tieOrder.equals(currentTieOrder)){
            orders.add(tieOrder);
            numElections++;
            return;
        } else {
            int[] thisTieOrder = (int[])tieOrder.get(tieNumber);
            int numInTie = thisTieOrder.length;
            Permutation permutation = new Permutation();
            List permutaitons = permutation.listing(numInTie,numInTie);
	        for (int i = 0; i < permutaitons.size() ; i++) {
	            List t = (List)((ArrayList)tieOrder).clone();
                for (int j = tieNumber; j < t.size(); ) {
                    t.remove(j);
                }
	            t.add(tieNumber,(int[])permutaitons.get(i));
	            getPermutations(candidateNames,numSeats,eType,votes,t,tieNumber+1);
	        }
        }
    }
        
    public String getOrders(){
        StringBuilder builder = new StringBuilder();
        for (int j = 0; j < orders.size(); j++) {
            ArrayList order = (ArrayList)orders.get(j);
            builder.append("CoyleDoyle+");
            for (int k = 0; k < order.size(); k++) {
                int[] tieOrder = (int[]) order.get(k);
                for (int index = 0; index < tieOrder.length; index++) {
                    builder.append(tieOrder[index]);
                    if(index<tieOrder.length-1)
                        builder.append("_");
                }
                if(k<order.size()-1)
                    builder.append("-");
            }
            builder.append("+IES+");
            for (int k = 0; k < order.size(); k++) {
                int[] tieOrder = (int[]) order.get(k);
                int[] iesOrder = getIESTieOrder(tieOrder);
                for (int i = 0; i < iesOrder.length; i++) {
                    builder.append(iesOrder[i]);
                    if(i<iesOrder.length-1)
                        builder.append("_");
                }
                if(k<order.size()-1)
                    builder.append("-");
            }
            
            builder.append("\n");
        }
        return builder.toString();
    }
    
    private int[] getIESTieOrder(int[] coyleDoyleOrder){
        int numInTie = coyleDoyleOrder.length;
        int[] iesOrder = new int[numInTie];
        for (int i = 0; i < numInTie; i++) {
            for (int j = 0; j < numInTie; j++) {
                if(coyleDoyleOrder[j]==numInTie-i)
                    iesOrder[i]=j+1;
            }
        }
        return iesOrder;
    }
    
    public int getNumElections() {
        return numElections;
    }

    public static void main(String[] args) {
        TieIterator tieIterator = new TieIterator();
        String folder = "D:\\IES-Testdata\\Ties\\T1\\Passed - EU - 3 - 8 - 20 - 11OCT230121 - IN - SERVER1134538414 - Tie";
        List list = tieIterator.testFolder(new File(folder));
        System.out.println(list); 
        
    }



}
