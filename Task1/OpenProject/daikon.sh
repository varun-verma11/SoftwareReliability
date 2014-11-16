source /vol/lab/cs4/SoftwareReliability/coursework1.sh
javac src/*.java
java daikon.Chicory src.DiakonMainTest 
java daikon.Daikon DiakonMainTest.dtrace.gz
