(* ::Package:: *)

(* ::Title:: *)
(*PartitionWhile (1.0.0)*)


(* ::Subtitle:: *)
(*Wolfram Resource Function contributed by: Daniele Gregori*)


(* ::Section:: *)
(*Package Header*)


BeginPackage["PartitionWhile`"];


PartitionWhile::usage=
"PartitionWhile[list,crit]
  partition a list into sublists satisfying a condition.";


Begin["Private`"];


(* ::Section:: *)
(*Definition*)


(* ::Subsection:: *)
(*Shortest partition*)


(* ::Input::Initialization:: *)
(*The default behavior*)
partitionWhileShortest[list_List,fun_Function]:=
	Block[{len,i,j,first,last,elq,prtind},
			
			len=Length[list];
			
			prtind={};			

			For[i=1,i<=len,i++,

				first=i;
				last=0;	
				For[j=i,j<=len,j++,
					
					elq=fun[list[[i;;j]]];
					If[elq,
						last=j,
						(*break immediately*)
						If[last!=0,Break[]]]];

				If[last!=0,
					i=last;
					AppendTo[prtind,{first,last}]]];

			Map[Take[list,#]&,prtind]]


(* ::Subsection:: *)
(*Longer partitions*)


(* ::Input:: *)
(*(*In these only few lines of code change, but I repeat also the rest to allow the user a simpler copy and paste when generating a compiled version*)*)


(* ::Subsubsection:: *)
(*Longest partition*)


(* ::Input::Initialization:: *)
(*This just searches the longest possible partitions*)
partitionWhileLongest[list_List,fun_Function]:=
	Block[{len,i,j,first,last,elq,prtind},
			
			len=Length[list];
			
			prtind={};			

			For[i=1,i<=len,i++,

				first=i;
				last=0;	
				For[j=i,j<=len,j++,
					
					elq=fun[list[[i;;j]]];
					If[elq,
						last=j,
						(*continue until the end*)
						Continue[]]];

				If[last!=0,
					i=last;
					AppendTo[prtind,{first,last}]]];

			Map[Take[list,#]&,prtind]]


(* ::Subsubsection:: *)
(*Next to shortest partitions*)


(*This just searches only the k-next element, but effectively builds a different final partition*)
partitionWhileNext[list_List,fun_Function,k_Integer]:=
	Block[{len,i,j,first,last,next,elq,partind},
			
			len=Length[list];
			
			partind={};			

			For[i=1,i<=len,i++,

				first=i;
				last=0;
				next=0;	
				For[j=i,j<=len,j++,
					
					elq=fun[list[[i;;j]]];
					If[elq,
						last=j,
						(*break after k next elements*)
						next+=1;
						If[last!=0&&next==k,Break[]]]];

				If[last!=0,
					i=last;
					AppendTo[partind,{first,last}]]];

			Map[Take[list,#]&,partind]]


(* ::Subsection:: *)
(*Main definition*)


(* ::Input::Initialization:: *)
ClearAll[PartitionWhile]

Options[PartitionWhile]={"ShortestPartitions"->True};

PartitionWhile[list_,fun_Function,opts:OptionsPattern[PartitionWhile]]:=
	Block[{optshort},

	optshort=OptionValue["ShortestPartitions"];
	
	Which[optshort===True,
				partitionWhileShortest[list,fun],
		
			optshort===False,
				partitionWhileLongest[list,fun],

			IntegerQ@optshort,
				partitionWhileNext[list,fun,optshort]]]


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
