#!/bin/sh

ONLY_REPORT_FAILURES=0


# TOOL_DIR should be set to the directory of srt_run.sh.
: ${TOOL_DIR:?"Need to set TOOL_DIR environment variable."}

TESTER=testerpy/tester.py
TOOL=$TOOL_DIR/srt_run.sh


# Very simple test cases (to start with):
# Once you have the bounded model checker working, you can remove
# this line, as these tests are included below.
$TESTER $TOOL tests/loopfree/1_simple $ONLY_REPORT_FAILURES -mode bmc

# Loop-free tests (should work with all modes)

#$TESTER $TOOL tests/loopfree $ONLY_REPORT_FAILURES -mode bmc
#$TESTER $TOOL tests/loopfree $ONLY_REPORT_FAILURES -mode bmc -unsound
#$TESTER $TOOL tests/loopfree $ONLY_REPORT_FAILURES -mode verifier
#$TESTER $TOOL tests/loopfree $ONLY_REPORT_FAILURES -mode houdini
#$TESTER $TOOL tests/loopfree $ONLY_REPORT_FAILURES -mode invgen
# Uncomment if you implement comp
#$TESTER $TOOL tests/loopfree $ONLY_REPORT_FAILURES -mode comp

# BMC sound tests
#$TESTER $TOOL tests/bmc_sound $ONLY_REPORT_FAILURES -mode bmc

# BMC unsound tests
#$TESTER $TOOL tests/bmc_unsound $ONLY_REPORT_FAILURES -mode bmc -unsound

# Verifier tests
#$TESTER $TOOL tests/verifier $ONLY_REPORT_FAILURES -mode verifier

# Houdini tests
#$TESTER $TOOL tests/houdini $ONLY_REPORT_FAILURES -mode houdini

# Invariant generation tests
#$TESTER $TOOL tests/invgen $ONLY_REPORT_FAILURES -mode invgen

# Competition mode tests
#$TESTER $TOOL tests/comp $ONLY_REPORT_FAILURES -mode comp

