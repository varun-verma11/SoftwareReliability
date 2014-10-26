#!/bin/tcsh -f
source /vol/lab/cs4/SoftwareReliability/coursework1.sh

switch ($#)
  case 0:
    escjava2 -VCLimit 5000000 -NoCautions -NoWarn ArrayStore -NoWarn Modifies bookings/*.java;
    breaksw
  case 1:
    escjava2 -VCLimit 5000000 -NoCautions -NoWarn ArrayStore -NoWarn Modifies $*;
    breaksw
endsw
