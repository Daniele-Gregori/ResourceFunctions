#!/usr/bin/env bash
# Run AlgebraicRange tests with formatted output
# Usage:  ./run-tests.sh            (run all tests)
#         ./run-tests.sh "3a"       (run only tests whose TestID contains "3a")

set -euo pipefail
cd "$(dirname "$0")/../../.."

TEST_FILE="Functions/AlgebraicRange/Tests/AlgebraicRange-1-1-0-tests.wlt"
FILTER="${1:-}"

wolframscript -code "
  report = TestReport[\"$TEST_FILE\"];

  passed  = report[\"TestsSucceededCount\"];
  failed  = report[\"TestsFailedCount\"];
  total   = passed + failed;

  results = Values @ report[\"TestResults\"];

  If[\"$FILTER\" =!= \"\",
    results = Select[results, StringContainsQ[#[\"TestID\"], \"$FILTER\"] &];
    total   = Length[results];
    passed  = Count[results, _?(#[\"Outcome\"] === \"Success\" &)];
    failed  = total - passed;
  ];

  Print[\"  Tests run:  \", total];
  Print[\"  Passed:     \", passed];
  Print[\"  Failed:     \", failed];
  Print[\"\"];

  If[failed > 0,
    Print[\"Failed tests:\"];
    Scan[
      Print[\"  FAIL  \", #[\"TestID\"], \"  (\", #[\"Outcome\"], \")\"] &,
      Select[results, #[\"Outcome\"] =!= \"Success\" &]];
    Print[\"\"],

    Print[\"All tests passed.\"]
  ];

  If[\"$FILTER\" =!= \"\",
    Print[\"Details (filter: $FILTER):\"];
    Scan[
      Print[\"  \", If[#[\"Outcome\"] === \"Success\", \"+\", \"-\"],
            \" \", #[\"TestID\"],
            \"  (\", NumberForm[#[\"AbsoluteTimeUsed\"], {4,2}], \"s)\"] &,
      results];
  ];

  Exit[If[failed == 0, 0, 1]]
"
