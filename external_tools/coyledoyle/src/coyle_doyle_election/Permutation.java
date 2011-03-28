package coyle_doyle_election;

import java.util.ArrayList;
import java.util.List;


public class Permutation
{
    int[] value;

    public List listing(int number, int select)
    {
        List permutations = new ArrayList();
        
        value = new int [select];

        int[] a = new int[select];                           // initialize
        for (int i = 0; i < select; i++) 
            a[i] = i + 1;                              // 1 - 2 - 3 - 4 - ...

        while (true)
        {       
            for (int n = 0; n < select; n++) 
                value[n] = a[n]; 

            // for this combination, list permutations in lexicographical order
            put_next(permutations);
            while (get_next(select))
                put_next(permutations);

            // generate next combination in lexicographical order
            int i = select - 1;                            // start at last item        
            while ( a[i] == (number - select + i + 1)){  // find next item to increment
                --i;
                if (i < 0) break;                          // all done                
            }
            if (i < 0) break;                          // all done                
            ++a[i];                                    // increment

            for (int j = i + 1; j < select; j++)           // do next combination 
                a[j] = a[i] + j - i;
        }
        return permutations;
    }

//     compute the number of permutations of r objects from a set on n objects
    public int permutations( int n, int r )
    {
        int c = 1;
        if (r > n) return 0;
        int d = n - r;
        
        while (n > 0)
        {
            c = c * n;
            --n; 
        }

        while (d!=0)
        {
            c = c / d;
            --d;
        }

        return c;
    }

//     compute the next permutation given the current permutation
    private boolean get_next( int k )
    {
        int i = k - 1;
        while (i!=0 && value[i-1] >= value[i]){
            i--;
        }

        if (i < 1) return false;                       // all in reverse order 

        int j = k;
        while (value[j-1] <= value[i-1]) 
            j--;

        swap(i - 1, j - 1);

        i++; 
        j = k;

        while (i < j)
        {
            swap(i - 1, j - 1);
            i++;
            j--;
        }

        return true;
    }

    private void swap( int a, int b )
    {
        int temp     = value[a];
        value[a] = value[b];
        value[b] = temp;
    }

    private void put_next(List permutations)
    {
        int[] copy = new int[value.length];
        for (int i = 0; i < value.length; i++)
            copy[i] = value[i];
        permutations.add(copy);
    }

    
    public static void main(String[] args) {
        Permutation permutation = new Permutation();
        List list = permutation.listing(2,2);
        for (int i = 0; i < list.size(); i++) {
            int[] js = (int[])list.get(i);
            for (int j = 0; j < js.length; j++) {
                System.out.print(js[j]+" ");
            }
            System.out.println();
        }
        permutation.permutations(2,2);
        
    }
}
