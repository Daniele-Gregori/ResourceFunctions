(* ::Package:: *)

(* ::Title:: *)
(*StringStyleJoin (1.0.0)*)


(* ::Subtitle:: *)
(*Wolfram Resource Function contributed by Daniele Gregori*)


(* ::Section:: *)
(*Package Header*)


BeginPackage["StringStyleJoin`"];


StringStyleJoin::usage=
"StringStyleJoin[\!\(\*SubscriptBox[\(s\), \(1\)]\),\!\(\*SubscriptBox[\(s\), \(2\)]\),\!\(\*SubscriptBox[\(s\), \(3\)]\),...] join an arbitrary sequence of styled or plain strings as a unique string.";


Begin["Private`"];


(* ::Section:: *)
(*Definition*)


(* ::Input::Initialization:: *)
ClearAll[StringStyleJoin]
StringStyleJoin[]="";
StringStyleJoin[syl_Style]:=
	"\!\(\*"<>ToString@ToBoxes@syl<>"\)"
StringStyleJoin[s1_String,syl_Style]:=
	s1<>StringStyleJoin@syl
StringStyleJoin[syl_Style,sm1_String]:=
	StringStyleJoin@syl<>sm1
StringStyleJoin[s__]:=
	Block[{sq="",stp={s}/.syl_Style:>"\!\(\*"<>ToString@ToBoxes@syl<>"\)"},
		{sq,stp}=TakeDrop[stp,1];
		sq<>StringStyleJoin[Sequence@@stp]]


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
