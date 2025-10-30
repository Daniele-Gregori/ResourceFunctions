(* ::Package:: *)

(* ::Title:: *)
(*AssociateColumns (1.0.0)*)


(* ::Subtitle:: *)
(*Wolfram Resource Function contributed by: Daniele Gregori*)


(* ::Section:: *)
(*Package Header*)


BeginPackage["AssociateColumns`"];


AssociateColumns::usage=
"AssociateColumns[tab, {col1, col2}]
  associates one column of tab to another column.

AssociateColumns[tab, {col1, col2}, f]
  specify a merging function for possible duplicate keys.

AssociateColumns[tab, {{col1, col2, \[Ellipsis]}, {col3, col4, \[Ellipsis]}}]
  associates multiple columns as keys to multiple columns as values.

AssociateColumns[tab, {{col1, col2, \[Ellipsis]}, {col3, col4, \[Ellipsis]}}, f]
  specify a merging function.

AssociateColumns[tab, {cols1, cols2, cols3, \[Ellipsis]}]
  creates an arbitrarily nested Association.

AssociateColumns[tab, cols1 -> cols2 -> cols3 -> \[Ellipsis]]
  alternative syntax with a rule for each level of nesting.

AssociateColumns[tab, cols1 -> cols2 -> cols3 -> \[Ellipsis], f]
  specify the same merging function for each nesting level.

AssociateColumns[tab, cols1 -> cols2 -> cols3 -> \[Ellipsis], {f12, f23, \[Ellipsis]}]
  specify a different merging function for each nesting level.";


Begin["Private`"];


(* ::Section:: *)
(*Definition*)


(* ::Input::Initialization:: *)
ClearAll[AssociateColumns,associateColumnsCore,multiColumns]


(*table and column patterns*)

tabPatt=_Tabular|{_Association..}|_Dataset?(MatchQ[Normal@#,{_Association..}]&);

colPatt=_String|_ExtendedKey|{(_String|_ExtendedKey)..};


(*auxiliary function*)


multiColumns[tab:tabPatt,col:_String|_ExtendedKey]:=
	Normal@tab[[All,col]]

multiColumns[tab:tabPatt,cols_List]:=
	Transpose@Map[multiColumns[tab,#]&,cols]


(*warning message*)

AssociateColumns::DuplicateKeys=
"Warning: duplicate keys have been found. It is preferable to specify a merging function as third argument. Full list of duplicate keys: `1`.";

Options[AssociateColumns]={"DuplicatesWarning"->Automatic};



(*core function*)


associateColumnsCore[
	list:{_Rule..},
	options:OptionsPattern[AssociateColumns]]:=
		Block[{dfq,keys,grby},
			keys=Keys[list];
			dfq=DuplicateFreeQ[keys];
			If[!dfq,
			If[MemberQ[{Automatic,True},OptionValue["DuplicatesWarning"]],
				ResourceFunction["ResourceFunctionMessage"][
					AssociateColumns::DuplicateKeys,
					ResourceFunction["DuplicatesList"][keys]]];
			GroupBy[list,First->Last],
			Association[list]]]


associateColumnsCore[
	list:{_Rule..},
	fun:_Function|_Symbol,
	options:OptionsPattern[AssociateColumns]]:=
		Map[fun,
			associateColumnsCore[
				list,
				If[MemberQ[{Automatic,False},OptionValue["DuplicatesWarning"]],
					"DuplicatesWarning"->False,
					"DuplicatesWarning"->True]]]

associateColumnsCore[list:{_Rule..},
	fun:Automatic,
	options:OptionsPattern[AssociateColumns]]:=
	associateColumnsCore[list,Identity,options]


associateColumnsCore[
	rule:Rule[_List,_List],
	fun:___Function|___Symbol,
	options:OptionsPattern[AssociateColumns]]:=
			associateColumnsCore[{rule},fun,options]

associateColumnsCore[
	rule_Rule,
	fun:___Function|___Symbol,
	options:OptionsPattern[AssociateColumns]]:=
			associateColumnsCore[{rule},fun,options]



(*confirm merging function*)

confirmCore:=
If[!FreeQ[#,_associateColumnsCore],
	Return[Failure["MergingFailed",
				"The chosen merging functions are not allowed by the structure of the data."]],
	#]&



(*nesting function*)

nestCoreMap[arg_,fun___,options:OptionsPattern[AssociateColumns]]:=Map[arg,associateColumnsCore[#,fun,options]]&



(*main function*)

(*no nesting*)

AssociateColumns[tab:tabPatt,{colL1:colPatt,colL2:colPatt},fun:___Function|___Symbol,
				options:OptionsPattern[AssociateColumns]]:=
		associateColumnsCore[
					Thread[multiColumns[tab,colL1]->multiColumns[tab,colL2]],fun,options]

(*arbitrary nesting*)

AssociateColumns[tab:tabPatt,cols:{colPatt..},options:OptionsPattern[AssociateColumns]]:=
	AssociateColumns[tab,cols,Identity,options]

AssociateColumns[tab:tabPatt,cols:{colPatt..},fun:_Function|_Symbol,options:OptionsPattern[AssociateColumns]]:=
	AssociateColumns[tab,cols,Table[fun,Length[cols]-1],options]

AssociateColumns[tab:tabPatt,cols:{colPatt..},funL:{(_Function|_Symbol)..},options:OptionsPattern[AssociateColumns]]:=
	Block[{fold,grby,fL},

		fold=Fold[Thread[#1->multiColumns[tab,#2]]&,
					multiColumns[tab,cols[[1]]],
					cols[[2;;]]];

		grby=GroupBy[fold,
					Function[#[[Sequence@@Table[1,Length[cols]-1]]]]
					->Function[Fold[Rule[#2,#1]&,
									#[[2]],
									Table[
										#[[Sequence@@PadLeft[{2},i,1]]],
										{i,2,Length[cols]-1}]]]];

		fL=PadRight[funL,Length[cols]-1,Identity];

		Map[Fold[
			nestCoreMap[#1,#2,options]&,
			associateColumnsCore[#,fL[[-1]],options]&,
			Reverse@fL[[2;;-2]]],
			
			Map[fL[[1]],grby]]

		]//confirmCore

(*alternative syntax*)

ruleToList[nest_Rule]:=
	Block[{lev},
		lev=Length@Cases[nest,_Rule,{0,Infinity}]+1;
		Table[nest[[Sequence@@PadLeft[{1},n,2]]],{n,lev-1}]~Join~{nest[[Sequence@@Table[2,lev-1]]]}]

AssociateColumns[tab:tabPatt,nest_Rule,fun___,options:OptionsPattern[AssociateColumns]]:=
	AssociateColumns[tab,ruleToList[nest],fun,options]


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
