#!/bin/tcsh -f
source /vol/lab/cs4/SoftwareReliability/coursework1.sh

switch ($#)
  case 0:
    escjava2 -VCLimit 5000000 -NoCautions bookings/*.java -NoWarn IndexTooBig -NoWarn IndexNegative -NoWarn ArrayStore -NoWarn Modifies;
    breaksw
  case 1:
    escjava2 -VCLimit 5000000 -NoCautions -NoWarn IndexTooBig -NoWarn IndexNegative -NoWarn ArrayStore -NoWarn Modifies $*;
    breaksw
endsw
