package src;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

/**
 * @author Varun Verma
 * 
 */
public class TestFilesGenerator
{
    /**
     * 
     */
    public static final String TEST_DIR = TestFilesGenerator.class
            .getProtectionDomain().getCodeSource().getLocation().getPath()
            + "testFiles/";

    public static void main(String[] args)
    {
        int nodes = 10;
        double p = 0.3;
        for (int i = 1; i <= 20; i++)
        {
            String fileRep = "";
            System.out.println("[" + i + "]: Generating random graph.");
            for (int j = 1; j <= nodes; j++)
            {
                for (int k = 1; k <= nodes; k++)
                {
                    if (j != k)
                    {
                        if (Math.random() > p)
                        {
                            fileRep += j + "," + k + "\n";
                        }
                    }
                }
            }
            if(Math.random()>0.5)
            {
              int root = (int) (Math.random() * nodes + 1);
              fileRep += "NULL," + root;
            }
            System.out.println("[" + i + "]: Writing graph to file.");
            try
            {
                FileWriter fw = new FileWriter(new File(TEST_DIR + i));
                fw.write(fileRep);
                fw.close();
            }
            catch (IOException e)
            {
                e.printStackTrace();
            }

        }
    }
}
