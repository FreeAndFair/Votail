/*
 * Created on 05-Dec-2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package testers;

import java.io.File;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.Charset;
import java.nio.charset.CharsetDecoder;
import java.nio.charset.CharsetEncoder;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

import coyle_doyle_election.FileUtils;


public class StringCounter {

    /**
     * @param args
     */
    public static void main(String[] args) {
        Hashtable hashtable  = new Hashtable();
        List foundLetters = new ArrayList();
        String letters = FileUtils.readFile(new File("src/testers/xmlString"));
        for (int i = 0; i < letters.length(); i++) {
            char c  = letters.charAt(i);
            Character character = new Character(c);
            if(hashtable.get(character)!=null){
                Integer val = (Integer)hashtable.get(character);
                int v = val.intValue();
                v++;
                hashtable.put(Character.valueOf(c),new Integer(v));
            } else {               
                hashtable.put(Character.valueOf(c),new Integer(1));
                foundLetters.add(character);
            }
        }
        for (int i = 0; i < foundLetters.size(); i++) {
            Character character = (Character)foundLetters.get(i);
            System.out.println(character + "\t" + hashtable.get(character));
        }
        
        Charset charset = Charset.forName("ISO-8859-1");
        CharsetDecoder decoder = charset.newDecoder();
        CharsetEncoder encoder = charset.newEncoder();
        
        try {
            // Convert a string to ISO-LATIN-1 bytes in a ByteBuffer
            // The new ByteBuffer is ready to be read.
            ByteBuffer bbuf = encoder.encode(CharBuffer.wrap("a string"));
            byte[] b = bbuf.array();
            System.out.println(b);
            for (int i = 0; i < b.length; i++) {
                System.out.print(b[i]);
            }
            System.out.println();
        
            // Convert ISO-LATIN-1 bytes in a ByteBuffer to a character ByteBuffer and then to a string.
            // The new ByteBuffer is ready to be read.
            CharBuffer cbuf = decoder.decode(bbuf);
            String s = cbuf.toString();
            System.out.println(s);
        } catch (CharacterCodingException e) {
            e.printStackTrace();
        }
    }
}
