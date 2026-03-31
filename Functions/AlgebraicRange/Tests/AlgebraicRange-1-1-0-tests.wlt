(* ============================================================ *)
(* COMPREHENSIVE TESTS FOR ResourceFunction["AlgebraicRange"]   *)
(* All argument forms, options, edge cases, properties, errors   *)
(* ============================================================ *)

BeginTestSection["AlgebraicRange Comprehensive Tests"]

(* ---- Setup ---- *)
Get[FileNameJoin[{DirectoryName[$TestFileName], "..", "Kernel", "AlgebraicRange-1-1-0-kernel.wl"}]];
AR = AlgebraicRange;

(* ================================================================ *)
(* TEST GROUP 1: Single-Argument Form  AR[x]                        *)
(* AR[x] gives Sqrt[Range[1, x^2]] for x >= 1                      *)
(* ================================================================ *)

VerificationTest[
  AR[3],
  Sqrt[Range[1, 9]],
  TestID -> "1a-SingleArg-Basic-AR3"
]

VerificationTest[
  AR[1],
  {1},
  TestID -> "1b-SingleArg-EdgeCase-AR1"
]

VerificationTest[
  AR[2],
  Sqrt[Range[1, 4]],
  TestID -> "1c-SingleArg-AR2"
]

VerificationTest[
  Length[AR[5]],
  25,
  TestID -> "1d-SingleArg-AR5-Length25"
]

VerificationTest[
  {First[AR[5]], Last[AR[5]]},
  {1, 5},
  TestID -> "1e-SingleArg-AR5-Endpoints"
]

(* ================================================================ *)
(* TEST GROUP 2: Two-Argument Form  AR[x, y]                        *)
(* AR[x,y] gives Sqrt[Range[x^2, y^2]] for 0 <= x <= y             *)
(* ================================================================ *)

VerificationTest[
  Length[AR[1, 3]],
  9,
  TestID -> "2a-TwoArg-Positive-Length"
]

VerificationTest[
  First[AR[0, 2]],
  0,
  TestID -> "2b-TwoArg-ZeroStart"
]

VerificationTest[
  Last[AR[0, 2]],
  2,
  TestID -> "2c-TwoArg-ZeroStart-LastElement"
]

VerificationTest[
  AR[-3, -1],
  Reverse[-AR[1, 3]],
  TestID -> "2d-TwoArg-NegativeReflection"
]

VerificationTest[
  SubsetQ[AR[2, 5], Range[2, 5]],
  True,
  TestID -> "2e-TwoArg-ExtendsRange"
]

VerificationTest[
  AR[3, 3],
  {3},
  TestID -> "2f-TwoArg-SinglePoint"
]

VerificationTest[
  AR[0, 0],
  {0},
  TestID -> "2g-TwoArg-ZeroZero"
]

VerificationTest[
  MemberQ[AR[-2, 3], 0],
  True,
  TestID -> "2h-TwoArg-MixedBounds-ContainsZero"
]

VerificationTest[
  Last[AR[-3, 0]],
  0,
  TestID -> "2i-TwoArg-NegToZero"
]

VerificationTest[
  AR[Sqrt[2], Sqrt[7]],
  {Sqrt[2], Sqrt[3], 2, Sqrt[5], Sqrt[6], Sqrt[7]},
  TestID -> "2j-TwoArg-IrrationalBounds"
]

VerificationTest[
  AR[-5, -2],
  Reverse[-AR[2, 5]],
  TestID -> "2k-TwoArg-NegativeReflection-Large"
]

VerificationTest[
  AllTrue[AR[-4, -1], Negative],
  True,
  TestID -> "2l-TwoArg-AllNegative"
]

(* ================================================================ *)
(* TEST GROUP 3: Three-Argument Form  AR[x, y, s]  (Step)           *)
(* s is the step upper bound                                         *)
(* ================================================================ *)

VerificationTest[
  Length[AR[0, 3, 1/2]] > 0,
  True,
  TestID -> "3a-ThreeArg-FractionalStep-NonEmpty"
]

VerificationTest[
  Max[N @ Differences[AR[0, 3, 1/2]]] <= 1/2 + 10^-10,
  True,
  TestID -> "3b-ThreeArg-StepUpperBound"
]

VerificationTest[
  OrderedQ[N[AR[2, -2, -1/2]], GreaterEqual],
  True,
  TestID -> "3c-ThreeArg-NegativeStep-Descending"
]

VerificationTest[
  Length[AR[0, 3, 1/Sqrt[2]]] > 0,
  True,
  TestID -> "3d-ThreeArg-IrrationalStep"
]

VerificationTest[
  Length[AR[Sqrt[1 + Sqrt[2]], 4, 1/Sqrt[2]]] > 0,
  True,
  TestID -> "3e-ThreeArg-NestedSqrtBounds"
]

VerificationTest[
  Length[AR[3, 3/2, -1/Sqrt[3]]] > 0,
  True,
  TestID -> "3f-ThreeArg-NegativeIrrationalStep"
]

VerificationTest[
  AR[0, 2, 2],
  {0, 2},
  TestID -> "3g-ThreeArg-StepEqualsSpan"
]

VerificationTest[
  AR[0, 1, 3],
  {0},
  TestID -> "3h-ThreeArg-StepLargerThanSpan"
]

VerificationTest[
  AR[1, 3, 1/2],
  Select[SortBy[
    Outer[Times, Range[0, 3, 1/2], AR[1, 3]] // Flatten // DeleteDuplicates, N],
    1 <= # <= 3 &],
  TestID -> "3i-ThreeArg-OuterProductEquivalence"
]

VerificationTest[
  First[AR[0, 3, 1/2]],
  0,
  TestID -> "3j-ThreeArg-FirstElement"
]

VerificationTest[
  Last[AR[0, 3, 1/2]],
  3,
  TestID -> "3k-ThreeArg-LastElement"
]

VerificationTest[
  Length[AR[0, 1, 1/10]] > 0,
  True,
  TestID -> "3l-ThreeArg-VerySmallStep"
]

(* ================================================================ *)
(* TEST GROUP 4: Four-Argument Form  AR[x, y, s, d]  (Step Bounds)  *)
(* d sets a minimum step (lower bound on differences)                *)
(* ================================================================ *)

VerificationTest[
  With[{diffs = N @ Abs @ Differences[AR[2, 7, 1/3, 1/4]]},
    Min[diffs] >= 1/4 - 10^-10 && Max[diffs] <= 1/3 + 10^-10],
  True,
  TestID -> "4a-FourArg-StepBoundsVerified"
]

VerificationTest[
  Length[AR[2, 7, 1/3, 1/4]] > 0,
  True,
  TestID -> "4b-FourArg-NonEmpty"
]

VerificationTest[
  Length[AR[0, 4, 2, 1/4, "RootOrder" -> 4]] > 0,
  True,
  TestID -> "4c-FourArg-WithRootOrder"
]

VerificationTest[
  With[{diffs = N @ Abs @ Differences[AR[1, 5, 1/2, 1/5, "RootOrder" -> 3]]},
    Min[diffs] >= 1/5 - 10^-10 && Max[diffs] <= 1/2 + 10^-10],
  True,
  TestID -> "4d-FourArg-StepBounds-WithRootOrder"
]

(* ================================================================ *)
(* TEST GROUP 5: Option "RootOrder"                                  *)
(* ================================================================ *)

VerificationTest[
  AR[2],
  AR[2, "RootOrder" -> {2}],
  TestID -> "5a-RootOrder-DefaultEqualsOrder2"
]

VerificationTest[
  Length[AR[2, "RootOrder" -> 3]] > Length[AR[2]],
  True,
  TestID -> "5b-RootOrder-HigherOrderMoreElements"
]

VerificationTest[
  SubsetQ[AR[2, "RootOrder" -> 3], AR[2, "RootOrder" -> {3}]],
  True,
  TestID -> "5c-RootOrder-UpToContainsOnly"
]

VerificationTest[
  SubsetQ[AR[2, "RootOrder" -> 3], AR[2, "RootOrder" -> {2}]],
  True,
  TestID -> "5d-RootOrder-UpToContainsOrder2"
]

VerificationTest[
  AR[2, "RootOrder" -> {3}],
  {1, 2^(1/3), 3^(1/3), 2^(2/3), 5^(1/3), 6^(1/3), 7^(1/3), 2},
  TestID -> "5e-RootOrder-OnlyCubicRoots"
]

VerificationTest[
  Length[AR[1, 3/2, "RootOrder" -> {3, 5}]] > 0,
  True,
  TestID -> "5f-RootOrder-MultipleOrders-3and5"
]

VerificationTest[
  Length[AR[0, 4, 2, "RootOrder" -> {4}]] > 0,
  True,
  TestID -> "5g-RootOrder-FourthRootsOnly"
]

VerificationTest[
  Length[AR[0, 4, 2, 1/4, "RootOrder" -> 4]] > 0,
  True,
  TestID -> "5h-RootOrder-FourthRootsWithStepBounds"
]

VerificationTest[
  Length[AR[1, 4, 1, "RootOrder" -> 4]] > Length[AR[1, 4, 1, "RootOrder" -> 2]],
  True,
  TestID -> "5i-RootOrder-Order4MoreThanOrder2-WithStep"
]

(* ================================================================ *)
(* TEST GROUP 6: Option "StepMethod"                                 *)
(* ================================================================ *)

VerificationTest[
  Length[AR[0, 3, 1/3, "StepMethod" -> "Root"]] > 0,
  True,
  TestID -> "6a-StepMethod-Root-NonEmpty"
]

VerificationTest[
  SubsetQ[
    AR[0, 3, 1/3, "StepMethod" -> "Root"],
    AR[0, 3, 1/3]],
  True,
  TestID -> "6b-StepMethod-OuterSubsetOfRoot"
]

VerificationTest[
  Length[AR[0, 3, 1/3, "StepMethod" -> "Root"]] >= Length[AR[0, 3, 1/3]],
  True,
  TestID -> "6c-StepMethod-RootAtLeastAsLargeAsOuter"
]

(* ================================================================ *)
(* TEST GROUP 7: Option "FareyRange"                                 *)
(* ================================================================ *)

VerificationTest[
  Length[AR[0, 3, 1/3, "FareyRange" -> True]] > 0,
  True,
  TestID -> "7a-FareyRange-NonEmpty"
]

VerificationTest[
  SortBy[Union @ Flatten @ Map[AR[0, 3, #] &,
    DeleteCases[FareySequence[3], 0]], N]
  ===
  AR[0, 3, 1/3, "FareyRange" -> True],
  True,
  TestID -> "7b-FareyRange-UnionEquivalence"
]

VerificationTest[
  Length[AR[0, 3, 1/3, "FareyRange" -> True]] >= Length[AR[0, 3, 1/3]],
  True,
  TestID -> "7c-FareyRange-AtLeastAsLargeAsDefault"
]

(* ================================================================ *)
(* TEST GROUP 8: Option "FormulaComplexity"                          *)
(* ================================================================ *)

VerificationTest[
  Length[AR[4, "RootOrder" -> 4, "FormulaComplexity" -> 4]] <
  Length[AR[4, "RootOrder" -> 4, "FormulaComplexity" -> 8]],
  True,
  TestID -> "8a-FormulaComplexity-LowerFewer"
]

VerificationTest[
  Length[AR[4, "RootOrder" -> 4, "FormulaComplexity" -> 8]] <
  Length[AR[4, "RootOrder" -> 4]],
  True,
  TestID -> "8b-FormulaComplexity-FiniteLessThanInfinity"
]

VerificationTest[
  Length[AR[4, "RootOrder" -> 4, "FormulaComplexity" -> 4]] <
  Length[AR[4, "RootOrder" -> 4, "FormulaComplexity" -> 8]] <
  Length[AR[4, "RootOrder" -> 4]],
  True,
  TestID -> "8c-FormulaComplexity-Monotone"
]

(* ================================================================ *)
(* TEST GROUP 9: Option "AlgebraicsOnly"                             *)
(* ================================================================ *)

VerificationTest[
  FailureQ[AR[0, 5, Sqrt[E]]],
  True,
  TestID -> "9a-AlgebraicsOnly-RejectsTranscendental"
]

VerificationTest[
  Length[AR[0, 5, Sqrt[E], "AlgebraicsOnly" -> False]] > 0,
  True,
  TestID -> "9b-AlgebraicsOnly-False-AcceptsTranscendental"
]

VerificationTest[
  Element[AR[0, 5, Sqrt[E], "AlgebraicsOnly" -> False], Algebraics],
  False,
  TestID -> "9c-AlgebraicsOnly-False-OutputNotAlgebraic"
]

(* ================================================================ *)
(* TEST GROUP 10: Domain Verification (Algebraics, Reals)            *)
(* ================================================================ *)

VerificationTest[
  Element[AR[0, 5, 1/2, "RootOrder" -> 3], Algebraics],
  True,
  TestID -> "10a-Domain-AllAlgebraic"
]

VerificationTest[
  Element[AR[0, 5, 1/2, "RootOrder" -> 3], Reals],
  True,
  TestID -> "10b-Domain-AllReal"
]

VerificationTest[
  Element[AR[3], Algebraics],
  True,
  TestID -> "10c-Domain-SingleArg-Algebraic"
]

VerificationTest[
  Element[AR[-3, -1], Reals],
  True,
  TestID -> "10d-Domain-NegativeRange-Real"
]

(* ================================================================ *)
(* TEST GROUP 11: Sorting & Uniqueness                               *)
(* ================================================================ *)

VerificationTest[
  OrderedQ[N[AR[1, 5]]],
  True,
  TestID -> "11a-Sorted-Ascending-PositiveRange"
]

VerificationTest[
  OrderedQ[N[AR[-5, -1]]],
  True,
  TestID -> "11b-Sorted-Ascending-NegativeRange"
]

VerificationTest[
  OrderedQ[N[AR[-2, 3]]],
  True,
  TestID -> "11c-Sorted-Ascending-MixedRange"
]

VerificationTest[
  With[{t = AR[0, 3, 1/3]},
    Length[t] == Length[DeleteDuplicates[t]]],
  True,
  TestID -> "11d-NoDuplicates-ThreeArg"
]

VerificationTest[
  With[{t = AR[5]},
    Length[t] == Length[DeleteDuplicates[t]]],
  True,
  TestID -> "11e-NoDuplicates-SingleArg"
]

VerificationTest[
  With[{t = AR[0, 4, 1, "RootOrder" -> 3]},
    Length[t] == Length[DeleteDuplicates[t]]],
  True,
  TestID -> "11f-NoDuplicates-WithRootOrder"
]

(* ================================================================ *)
(* TEST GROUP 12: Negative Ranges & Reflection Properties            *)
(* ================================================================ *)

VerificationTest[
  AR[-3, -1] === Reverse[-AR[1, 3]],
  True,
  TestID -> "12a-NegReflection-Small"
]

VerificationTest[
  AR[-5, -2] === Reverse[-AR[2, 5]],
  True,
  TestID -> "12b-NegReflection-Large"
]

VerificationTest[
  AR[-10, -7] === Reverse[-AR[7, 10]],
  True,
  TestID -> "12c-NegReflection-Larger"
]

VerificationTest[
  AR[3/2, -3/2, -1/3] =!= Reverse[AR[-3/2, 3/2, 1/3]],
  True,
  TestID -> "12d-NegStep-Asymmetry"
]

VerificationTest[
  OrderedQ[N[AR[3/2, -3/2, -1/3]], GreaterEqual],
  True,
  TestID -> "12e-NegStep-DescendingOrder"
]

VerificationTest[
  Length[AR[Sqrt[10], -Sqrt[10], -2]] > 0,
  True,
  TestID -> "12f-NegStep-IrrationalBounds"
]

VerificationTest[
  Length[Simplify @ AR[2 Sqrt[2 + Sqrt[3]], -2 Sqrt[2 + Sqrt[3]], -Sqrt[5]]] > 0,
  True,
  TestID -> "12g-NegStep-ComplexIrrationalBounds"
]

(* ================================================================ *)
(* TEST GROUP 13: Error Handling                                     *)
(* ================================================================ *)

VerificationTest[
  FailureQ[AR[Sqrt[1 - Sqrt[2]], 4, 1/Sqrt[2]]],
  True,
  TestID -> "13a-Error-ComplexInput"
]

VerificationTest[
  FailureQ[AR[0, 5, Sqrt[E]]],
  True,
  TestID -> "13b-Error-TranscendentalInput"
]

(* ================================================================ *)
(* TEST GROUP 14: Numeric (Approximate) Inputs                       *)
(* ================================================================ *)

VerificationTest[
  Length[AR[0.1, 3.1]] > 0,
  True,
  TestID -> "14a-Numeric-SimpleDecimal"
]

VerificationTest[
  First[AR[0.1, 3.1]],
  1/10,
  TestID -> "14b-Numeric-DecimalRecognized"
]

VerificationTest[
  Max[Abs[N[AR[1.266314886, 3] - AR[1/2 Sqrt[5 + Sqrt[2]], 3]]]] < 10^-8,
  True,
  TestID -> "14c-Numeric-ApproxVsExact-SmallDiff"
]

(* ================================================================ *)
(* TEST GROUP 15: Superset / Subset Structural Properties            *)
(* ================================================================ *)

VerificationTest[
  SubsetQ[AR[2, 5], Range[2, 5]],
  True,
  TestID -> "15a-SupersetOfRange-Small"
]

VerificationTest[
  SubsetQ[AR[0, 4], Range[0, 4]],
  True,
  TestID -> "15b-SupersetOfRange-WithZero"
]

VerificationTest[
  SubsetQ[AR[1, 10], Range[1, 10]],
  True,
  TestID -> "15c-SupersetOfRange-Large"
]

VerificationTest[
  SubsetQ[AR[0, 3, 1/3, "StepMethod" -> "Root"], AR[0, 3, 1/3]],
  True,
  TestID -> "15d-OuterSubsetOfRoot"
]

(* ================================================================ *)
(* TEST GROUP 16: Combined Options                                   *)
(* ================================================================ *)

VerificationTest[
  Length[AR[0, 3, "RootOrder" -> 4, "FormulaComplexity" -> 6]] > 0,
  True,
  TestID -> "16a-Combined-RootOrder-FormulaComplexity"
]

VerificationTest[
  Length[AR[0, 3, 1/3, "RootOrder" -> 3, "StepMethod" -> "Root"]] > 0,
  True,
  TestID -> "16b-Combined-RootOrder-StepMethod"
]

VerificationTest[
  Length[AR[0, 2, 1/2, "RootOrder" -> 3, "FareyRange" -> True]] > 0,
  True,
  TestID -> "16c-Combined-RootOrder-FareyRange"
]

VerificationTest[
  With[{diffs = N @ Abs @ Differences[AR[1, 5, 1/2, 1/5, "RootOrder" -> 3]]},
    Min[diffs] >= 1/5 - 10^-10 && Max[diffs] <= 1/2 + 10^-10],
  True,
  TestID -> "16d-Combined-FourArgs-RootOrder-BoundsOK"
]

(* ================================================================ *)
(* TEST GROUP 17: Stress / Large Output                              *)
(* ================================================================ *)

VerificationTest[
  Length[AR[0, 10]],
  101,
  TestID -> "17a-Stress-LargeRange-Length"
]

VerificationTest[
  {First[AR[0, 10]], Last[AR[0, 10]]},
  {0, 10},
  TestID -> "17b-Stress-LargeRange-Endpoints"
]

VerificationTest[
  Length[AR[1, 4, 1, "RootOrder" -> 4]] > 100,
  True,
  TestID -> "17c-Stress-HighRootOrder-ManyElements"
]

(* ================================================================ *)
(* TEST GROUP 18: Random Algebraic Domain Check                      *)
(* ================================================================ *)

VerificationTest[
  Block[{$MaxExtraPrecision = 10000},
    With[{r = AR[2 Sqrt[1 + Sqrt[3]], -2 Sqrt[1 + Sqrt[3]], -Sqrt[2]/3, 1/4, "RootOrder" -> {2, 3}]},
      Element[r, Algebraics] && Element[r, Reals]]],
  True,
  TestID -> "18a-Random-AlgebraicAndReal"
]

(* ================================================================ *)
(* TEST GROUP 19: Step Ranges - Mixed Sign (r1 < 0 < r2, s > 0)     *)
(* ================================================================ *)

VerificationTest[
  Length[AR[-2, 3, 1/2]] > 0,
  True,
  TestID -> "19a-MixedAsc-NonEmpty"
]

VerificationTest[
  OrderedQ[N[AR[-2, 3, 1/2]]],
  True,
  TestID -> "19b-MixedAsc-SortedAscending"
]

VerificationTest[
  MemberQ[AR[-2, 3, 1/2], 0],
  True,
  TestID -> "19c-MixedAsc-ContainsZero"
]

VerificationTest[
  Max[N @ Differences[AR[-2, 3, 1/2]]] <= 1/2 + 10^-10,
  True,
  TestID -> "19d-MixedAsc-StepUpperBound"
]

VerificationTest[
  With[{r = AR[-2, 3, 1/2]},
    {First[r], Last[r]}],
  {-2, 3},
  TestID -> "19e-MixedAsc-Endpoints"
]

VerificationTest[
  SubsetQ[AR[-2, 3, 1/2], {-2, -1, 0, 1, 2, 3}],
  True,
  TestID -> "19f-MixedAsc-ContainsIntegers"
]

(* ================================================================ *)
(* TEST GROUP 20: Step Ranges - Both Negative (r1 < r2 < 0, s > 0)  *)
(* ================================================================ *)

VerificationTest[
  Length[AR[-3, -1, 1/2]] > 0,
  True,
  TestID -> "20a-NegAsc-NonEmpty"
]

VerificationTest[
  AllTrue[AR[-3, -1, 1/2], Negative],
  True,
  TestID -> "20b-NegAsc-AllNegative"
]

VerificationTest[
  OrderedQ[N[AR[-3, -1, 1/2]]],
  True,
  TestID -> "20c-NegAsc-SortedAscending"
]

VerificationTest[
  AR[-3, -1, 1/2] === Reverse[-AR[1, 3, 1/2]],
  True,
  TestID -> "20d-NegAsc-ReflectionProperty"
]

VerificationTest[
  Max[N @ Abs @ Differences[AR[-3, -1, 1/2]]] <= 1/2 + 10^-10,
  True,
  TestID -> "20e-NegAsc-StepUpperBound"
]

(* ================================================================ *)
(* TEST GROUP 21: Step Ranges - Both Neg Descending (both < 0, s<0)  *)
(* ================================================================ *)

VerificationTest[
  Length[AR[-1, -3, -1/2]] > 0,
  True,
  TestID -> "21a-NegDesc-NonEmpty"
]

VerificationTest[
  AllTrue[AR[-1, -3, -1/2], Negative],
  True,
  TestID -> "21b-NegDesc-AllNegative"
]

VerificationTest[
  OrderedQ[N[AR[-1, -3, -1/2]], GreaterEqual],
  True,
  TestID -> "21c-NegDesc-SortedDescending"
]

VerificationTest[
  AR[-1, -3, -1/2] === Reverse[-AR[3, 1, -1/2]],
  True,
  TestID -> "21d-NegDesc-ReflectionProperty"
]

VerificationTest[
  Max[N @ Abs @ Differences[AR[-1, -3, -1/2]]] <= 1/2 + 10^-10,
  True,
  TestID -> "21e-NegDesc-StepUpperBound"
]

(* ================================================================ *)
(* TEST GROUP 22: Step Ranges - Mixed Descending (r1>0>r2, s<0)      *)
(* ================================================================ *)

VerificationTest[
  Length[AR[3, -2, -1/2]] > 0,
  True,
  TestID -> "22a-MixedDesc-NonEmpty"
]

VerificationTest[
  OrderedQ[N[AR[3, -2, -1/2]], GreaterEqual],
  True,
  TestID -> "22b-MixedDesc-SortedDescending"
]

VerificationTest[
  MemberQ[AR[3, -2, -1/2], 0],
  True,
  TestID -> "22c-MixedDesc-ContainsZero"
]

VerificationTest[
  Max[N @ Abs @ Differences[AR[3, -2, -1/2]]] <= 1/2 + 10^-10,
  True,
  TestID -> "22d-MixedDesc-StepUpperBound"
]

VerificationTest[
  With[{r = AR[3, -2, -1/2]},
    {First[r], Last[r]}],
  {3, -2},
  TestID -> "22e-MixedDesc-Endpoints"
]

(* ================================================================ *)
(* TEST GROUP 23: FareyRange with Negative/Mixed Arguments           *)
(* ================================================================ *)

VerificationTest[
  Length[AR[-3, -1, 1/3, "FareyRange" -> True]] > 0,
  True,
  TestID -> "23a-Farey-BothNeg-NonEmpty"
]

VerificationTest[
  AllTrue[AR[-3, -1, 1/3, "FareyRange" -> True], Negative],
  True,
  TestID -> "23b-Farey-BothNeg-AllNegative"
]

VerificationTest[
  Length[AR[-3, -1, 1/3, "FareyRange" -> True]] >= Length[AR[-3, -1, 1/3]],
  True,
  TestID -> "23c-Farey-BothNeg-SupersetOfDefault"
]

VerificationTest[
  Length[AR[-2, 3, 1/3, "FareyRange" -> True]] > 0,
  True,
  TestID -> "23d-Farey-Mixed-NonEmpty"
]

VerificationTest[
  MemberQ[AR[-2, 3, 1/3, "FareyRange" -> True], 0],
  True,
  TestID -> "23e-Farey-Mixed-ContainsZero"
]

VerificationTest[
  Length[AR[-2, 3, 1/3, "FareyRange" -> True]] >= Length[AR[-2, 3, 1/3]],
  True,
  TestID -> "23f-Farey-Mixed-SupersetOfDefault"
]

VerificationTest[
  Length[AR[3, -2, -1/3, "FareyRange" -> True]] > 0,
  True,
  TestID -> "23g-Farey-NegStep-NonEmpty"
]

VerificationTest[
  OrderedQ[N[AR[3, -2, -1/3, "FareyRange" -> True]], GreaterEqual],
  True,
  TestID -> "23h-Farey-NegStep-SortedDescending"
]

VerificationTest[
  Length[AR[-1, -3, -1/3, "FareyRange" -> True]] > 0,
  True,
  TestID -> "23i-Farey-BothNegDesc-NonEmpty"
]

VerificationTest[
  Length[AR[-1, -3, -1/3, "FareyRange" -> True]] >= Length[AR[-1, -3, -1/3]],
  True,
  TestID -> "23j-Farey-BothNegDesc-SupersetOfDefault"
]

(* ================================================================ *)
(* TEST GROUP 24: WorkingPrecision Option                            *)
(* ================================================================ *)

VerificationTest[
  AR[1, 3, 1/2, WorkingPrecision -> MachinePrecision] === AR[1, 3, 1/2],
  True,
  TestID -> "24a-WP-ExplicitDefault-SameResult"
]

VerificationTest[
  Length[AR[0, 3, 1/2, WorkingPrecision -> 50]] > 0,
  True,
  TestID -> "24b-WP-HighPrecision-NonEmpty"
]

VerificationTest[
  OrderedQ[N[AR[0, 3, 1/2, WorkingPrecision -> 50]]],
  True,
  TestID -> "24c-WP-HighPrecision-Sorted"
]

VerificationTest[
  OrderedQ[N[AR[-2, 3, 1/2, WorkingPrecision -> 100]]],
  True,
  TestID -> "24d-WP-HighPrecision-Mixed-Sorted"
]

VerificationTest[
  With[{diffs = N @ Abs @ Differences[AR[2, 7, 1/3, 1/4, WorkingPrecision -> 50]]},
    Min[diffs] >= 1/4 - 10^-10 && Max[diffs] <= 1/3 + 10^-10],
  True,
  TestID -> "24e-WP-HighPrecision-FourArg-StepBounds"
]

(* ================================================================ *)
(* TEST GROUP 25: Four-Argument Form - Negative/Mixed Arguments      *)
(* ================================================================ *)

VerificationTest[
  Length[AR[-3, -1, 1/3, 1/4]] > 0,
  True,
  TestID -> "25a-FourArg-BothNeg-NonEmpty"
]

VerificationTest[
  With[{test=AR[-3, -1, 1/3, 1/4] , expected = {-3, -(8/3), -((5 Sqrt[2])/3), -2, -Sqrt[3], -Sqrt[2], -(2/Sqrt[3])}},
    test === expected
  ]   ,
  True,
  TestID -> "25b-FourArg-BothNeg-StepBounds"
]

VerificationTest[
  Length[AR[-2, 3, 1/3, 1/4]] > 0,
  True,
  TestID -> "25c-FourArg-Mixed-NonEmpty"
]

VerificationTest[
  With[{test=AR[-2, 3, 1/3, 1/4] , expected = {-2, -Sqrt[3], -Sqrt[2], -(2/Sqrt[3]), -(2/3), -(1/3), 0, 1/3, 2/3, (2 Sqrt[2])/3, 4/3, 2 Sqrt[2/3], (4 Sqrt[2])/3, Sqrt[5], Sqrt[7], (4 Sqrt[5])/3}},
    test === expected
  ]   ,
  True,
  TestID -> "25d-FourArg-Mixed-StepBounds"
]

EndTestSection[]
