(* ::Package:: *)

(* ::Title:: *)
(*PauseUntil (1.0.0)*)


(* ::Subtitle:: *)
(*Wolfram Resource Function contributed by: Daniele Gregori*)


(* ::Section:: *)
(*Package Header*)


BeginPackage["PauseUntil`"];


PauseUntil::usage=
"PauseUntil[string]
  pauses until a given time, specified as String.

PauseUntil[time]
  pauses until a given TimeObject.

PauseUntil[date]
  pauses until a given DateObject.";


Begin["Private`"];


(* ::Section:: *)
(*Definition*)


(* ::Subsection::Closed:: *)
(*Error management*)


(*possible failures*)

failurePast=Failure["PastDate",
					<|"MessageTemplate"->"Cannot wait until the entered past date: `d`.",
					"MessageParameters"-><|"d"->#|>|>]&;
failureString=Failure["NoStringDate",
						<|"MessageTemplate"->"No TimeObject or DateObject interpretation found for the time: `d`.",
						"MessageParameters"-><|"d"->#|>|>]&;
failureZone=Failure["BadTimeZone",
						<|"MessageTemplate"->"The specified time zone `z` is not allowed.",
						"MessageParameters"-><|"z"->#|>|>]&;
failurePeriodic=Failure["BadPeriodicity",
						<|"MessageTemplate"->"The specified time periodicity `p` is not allowed.",
						"MessageParameters"-><|"p"->#|>|>]&;


(* ::Subsection::Closed:: *)
(*Time units*)


(*special steps for the option "Periodicity"*)

$periodicSteps={"Second","Minute","Hour","Day","Week","Month","Quarter","Year"};
$periodicStepsSpecial={"Weekday","Weekend","BusinessDay",Monday,Tuesday,Wednesday,Thursday,Friday,Saturday,Sunday,"BeginningOfMonth","EndOfMonth"};
$periodicStepsFull=Join[$periodicSteps,$periodicStepsSpecial];
assocStepsSeconds=AssociationThread[$periodicSteps,FoldList[Times,1,{60,60,24,7,30,90,365}]];


(* ::Subsection::Closed:: *)
(*Utility functions*)


(* ::Input::Initialization:: *)
(*helper functions*)

makeDate[arg_,opts___]:=DateObject[arg,opts];
makeTime[arg_,opts___]:=TimeObject[makeDate[arg,opts],opts]

(*secondary function*)

(*returns the nearest future periodic date occuring*)

ClearAll[periodicDate]
Options[periodicDate]={TimeZone->Automatic};

periodicDate[time_?(Or[TimeObjectQ[#],DateObjectQ[#]]&),m_?NumericQ,unit:Alternatives@@$periodicStepsFull,opt:OptionsPattern[periodicDate]]:=
	Module[{unitc,secondsF,n0,n,datenew},
		unitc=If[MemberQ[$periodicStepsSpecial,unit],"Day",unit];
		secondsF[n_]:=AbsoluteTime[time,opt]+n*m*assocStepsSeconds[unitc];
		n0=Ceiling[Sequence@@SolveValues[secondsF[n]==AbsoluteTime[Now,opt],n]];
		datenew=DatePlus[time/.t_TimeObject:>TimeObject[PadRight[t[[1]],3],opt],{n0*m,unit}]]



(* ::Subsection::Closed:: *)
(*Main function*)


(* ::Input::Initialization:: *)
(*options*)

ClearAll[PauseUntil]
Options[PauseUntil]={TimeZone->Automatic,"PauseInformation"->False,"Periodicity"->None};

(*main function*)

PauseUntil[time:_TimeObject?TimeObjectQ|_DateObject?DateObjectQ|_String,options:OptionsPattern[PauseUntil]]:=
	ResourceFunction["CheckReturn"][
		Block[{optzone,timeinit,timefin,timeintern,timeinterpr,now,diffF,diff,negQ,periodtime,perioddiff,wait},
		
		optzone=TimeZone->OptionValue[TimeZone];
		timeinit=AbsoluteTime[optzone];

		timeinterpr=If[Head[time]=!=String,
						Head[time][time[[1]],optzone],
						Block[{interpretF,formats},
									interpretF[arg_,format_]:=
										If[!FailureQ[#],Return@#,arg]&@
											Interpreter[format][arg];
									formats={"Time","DateTime","Date"};
									Fold[interpretF[#1,#2]&,time,formats]
										//If[Head[#]=!=String,
												#,
												failureString[time]//Throw]&]];
		
		now=Switch[
				Head[timeinterpr],
				TimeObject,
					makeTime[timeinit,optzone],
				DateObject,
					makeDate[timeinit,optzone]];

		diffF[t_]:=QuantityMagnitude@DateDifference[now,t,"Seconds"];
		
		diff=diffF[timeinterpr];
		negQ=diff<0;
		
		wait=If[negQ,
				Block[{optperiod=OptionValue["Periodicity"]},
				Which[
					optperiod===None,
						Switch[
							Head[timeinterpr],
							TimeObject,
								86400+diff,
							DateObject,
								failurePast[timeinterpr]//Throw],
					MatchQ[optperiod,_Integer|{_Integer,Alternatives@@$periodicStepsFull}],
						If[!ListQ[optperiod],
							optperiod={optperiod,"Day"}];
						periodtime=periodicDate[timeinterpr,Sequence@@optperiod,optzone];
						perioddiff=diffF[periodtime];
						If[perioddiff<0&&Head[periodtime]===TimeObject,
							86400+perioddiff,
							perioddiff],
					True,
						failurePeriodic[optperiod]//Throw]],
						diff]
					//If[Block[{optinfo=OptionValue["PauseInformation"]},And[optinfo&&BooleanQ[optinfo]]],
							EchoFunction["waiting for: ",ResourceFunction["ReadableTimeString"][#]&][#],#]&;
		
		timefin=AbsoluteTime[optzone];
		timeintern=timefin-timeinit;
		
		Pause[wait-timeintern]],failureZone[OptionValue[TimeZone]]//Throw,{AbsoluteTime::zone}]//Catch


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
