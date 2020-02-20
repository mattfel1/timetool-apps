#!/bin/bash

# Set data environment variable for running this test
# export TEST_DATA_HOME="$PWD/../data/"

set -e # die if anything fails

type=$1
NUM_THREADS=${NUM_THREADS:-4}
CLOCK_FREQ_MHZ=${CLOCK_FREQ_MHZ:-125}
file_or_tests=$2

WARN="[\e[33mwarn\e[39m]"
INFO="[\e[34minfo\e[39m]"
FAIL="[\e[31merror\e[39m]"

tests="spatial.tests.dev.*"

echo -e "$INFO Using ${NUM_THREADS} thread(s) for testing."

if [[ $TEST_DATA_HOME == "" ]]; then
  echo -e "$WARN TEST_DATA_HOME is not set. Set TEST_DATA_HOME for data-dependent tests to pass."
else 
  echo -e "$INFO Test Data Directory: $TEST_DATA_HOME"
fi

starttime="$(date +'%m_%d_%y_%H_%M_%S')"
fileout="test_${starttime}_$type.log"
echo -e "$INFO Running tests $tests"
echo -e "$INFO Logging tests to $fileout"


# Basic tests
nice sbt -Dmaxthreads=${NUM_THREADS} -Dtest.CXP=true "; project test; testOnly $tests" 2>&1 | tee $fileout
sbtExitCode=${PIPESTATUS[0]}
exit $sbtExitCode
