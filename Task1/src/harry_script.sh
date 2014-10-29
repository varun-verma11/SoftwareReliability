#!/bin/bash
 
SR_ROOT=/vol/lab/cs4/SoftwareReliability
DAIKONDIR=$SR_ROOT/daikon_latest
JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64
 
source $DAIKONDIR/scripts/daikon.bashrc
CLASSPATH=.:$CLASSPATH
