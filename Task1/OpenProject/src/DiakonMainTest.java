package src;

/**
 * @author Varun Verma
 * 
 */
public class DiakonMainTest
{
    public static void main(String[] args)
    {
        System.out.println(TestFilesGenerator.TEST_DIR);
        for (int i = 1; i <= 25; i++)
        {
            // test till depth 3
            for (int d = 1; d <= 3; d++)
            {
                DepthAnalyserForCSV.main(new String[] {
                        TestFilesGenerator.TEST_DIR + i, d + "" });
            }
        }
    }
}
