package src;
import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

/**
 * The Class DepthAnalyserForCSV is used to analyse a graph and extract the
 * nodes at certain depth.
 * 
 * @author Varun Verma
 * 
 */
public class DepthAnalyserForCSV
{
    private static final String ROOT_ARC_KEY = "NULL";

    /**
     * The field arcs is used to store the parent nodes and its children.
     */
    private Map<String, ArrayList<String>> arcs = new HashMap<String, ArrayList<String>>();

    /**
     * The field error_occurred is used to keep a track if any error orrcured.
     */
    private boolean error_occurred = false;

    /**
     * This function reads the file from the given filepath and puts the arcs in
     * the the globally stored variable arcs. using a helper function. This
     * function mainly deals with all the error which could be encountered while
     * reading the file.
     * 
     * @param filepath
     *            : specifies the filepath for the file to be read.
     */
    public void read_file(String filepath)
    {
        BufferedReader br = null;
        try
        {
            br = new BufferedReader(new FileReader(filepath));
            read_arcs_from_file(br);
        }
        catch (FileNotFoundException e)
        {
            error_occurred = true;
            System.err.println("Please provide a valid filepath.");
            return;
        }
        catch (IOException e)
        {
            error_occurred = true;
        }
        finally
        {
            if (br != null)
            {
                try
                {
                    br.close();
                }
                catch (IOException e)
                {
                }
            }
        }
    }

    /**
     * Reads the file from the given buffered reader and stores them globally
     * 
     * @param br
     *            : specifies the input stream to read the data from
     * @throws IOException
     *             : when any IO error occurs while is being read;
     */
    private void read_arcs_from_file(BufferedReader br) throws IOException
    {
        String line;
        br.readLine();
        while ((line = br.readLine()) != null)
        {
            String[] tokens = line.split(",");
            if (arcs.containsKey(tokens[0]))
            {
                arcs.get(tokens[0]).add(tokens[1]);
            }
            else
            {
                ArrayList<String> list = new ArrayList<String>();
                list.add(tokens[1]);
                arcs.put(tokens[0], list);
            }
        }
        if(!arcs.containsKey(ROOT_ARC_KEY))
          error_occurred=true;
    }

    /**
     * This method sorts the given list of nodes. The number of comparisions
     * performed by this algorithm is (n-2)(n-1).
     * 
     * @param nodes
     *            : specifies the list of nodes to be sorted
     */
    private void sort_nodes_in_acsending_order(ArrayList<String> nodes)
    {
        quick_sort(nodes, 0, nodes.size() - 1);
    }

    /**
     * This method uses the quick sort algorithm to perform the sorting of the
     * given nodes.
     * 
     * @param nodes
     *            : specifies the list of nodes to be sorted
     * @param left
     *            : specifies the left index from which the sort has to be done
     * @param right
     *            : specifies the right index from which the sort has to be done
     */
    private void quick_sort(ArrayList<String> nodes, int left, int right)
    {
        int i, j;
        String temp = "";
        String pivot;
        i = left;
        j = right;
        pivot = nodes.get((left + right) / 2);
        while (i <= j)
        {
            while (nodes.get(i).compareTo(pivot) < 0)
                i++;
            while (nodes.get(j).compareTo(pivot) > 0)
                j--;
            if (i <= j)
            {
                temp = nodes.get(i);
                nodes.set(i, nodes.get(j));
                nodes.set(j, temp);
                i++;
                j--;
            }
        }
        if (left < j) quick_sort(nodes, left, j);
        if (i < right) quick_sort(nodes, i, right);
    }

    /**
     * This method is used to extract the nodes at the given depth. The
     * algorithm used is very simple, Basically it keeps a track of all the
     * nodes while it is examining the graph using the arcs which are stored
     * globally. Then when it reaches either depth of 0 or if there are no nodes
     * at given depth, which could be the case when the given depth is larger
     * than the depth of the graph. The list of the current nodes is returned.
     * 
     * @param depth
     *            : specifies the depth at which nodes are to be found in the
     *            graph
     * @return : returns null if depth>depth of tree or depth less than 0 else
     *         returns the nodes at the given depth
     */
    private ArrayList<String> get_nodes_at_depth(int depth)
    {
        ArrayList<String> nodes = arcs.get(ROOT_ARC_KEY);
        if (depth == 0) return nodes;

        while (depth != 0 && nodes.size() != 0)
        {
            ArrayList<String> children = new ArrayList<String>();
            for (String n : nodes)
            {
                if (!arcs.containsKey(n)) break;
                ArrayList<String> connections = arcs.get(n);
                for (String conc : connections)
                {
                    children.add(conc);
                }
            }
            nodes = children;
            depth--;
        }
        return nodes;
    }

    /**
     * This program is used to print the nodes in the given list.
     * 
     * @param node_at_depth
     *            : specifies the list to be printed
     */
    private static void print_nodes(ArrayList<String> node_at_depth)
    {
        for (String s : node_at_depth)
        {
            System.out.println(s);
        }
    }

    /**
     * This method is used to print the usage of this program.
     */
    private static void print_usage()
    {
        System.out.println("USAGE:");
        System.out.println("./myprogram <FILEPATH> <DEPTH>");
        System.out.println("\tDEPTH should be a positive integer.");
    }

    /**
     * This is the main method which is invoked with the command line arguments
     * 
     * @param args
     *            : specifies the command line arguments
     */
    public static void main(String[] args)
    {
        if (args.length != 2)
        {
            System.out.println("Wrong number of arguments.");
            print_usage();
            return;
        }
        DepthAnalyserForCSV analyser = new DepthAnalyserForCSV();
        analyser.read_file(args[0]);
        if (analyser.error_occurred) return;
        Integer depth;
        try
        {
            depth = new Integer(args[1]);
            if (depth < 0)
            {
                print_usage();
                return;
            }
        }
        catch (NumberFormatException e)
        {
            System.out
                    .println("Please enter a valid integer for the second argument");
            print_usage();
            return;
        }
        ArrayList<String> node_at_depth = analyser.get_nodes_at_depth(depth);
        if (node_at_depth.size() == 0) return;
        analyser.sort_nodes_in_acsending_order(node_at_depth);
        print_nodes(node_at_depth);

    }
}
