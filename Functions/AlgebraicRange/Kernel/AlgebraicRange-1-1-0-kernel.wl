(* ::Package:: *)

(* ::Title:: *)
(*AlgebraicRange (1.1.0)*)


(* ::Subtitle:: *)
(*Wolfram Resource Function contributed by: Daniele Gregori*)


(* ::Section:: *)
(*Package Header*)


BeginPackage["AlgebraicRange`"];


AlgebraicRange::usage=
"AlgebraicRange[x]
  gives the range of square roots Sqrt[Range[1, x^2]], for x >= 1.

AlgebraicRange[x, y]
  gives the range of square roots Sqrt[Range[x^2, y^2]], for 0 <= x <= y.

AlgebraicRange[x, y, s]
  generates steps bounded above by s, with 0 < s <= y.

AlgebraicRange[x, y, s, d]
  requires the steps to be bounded below by d, with 0 <= d < s.";


Begin["Private`"];


(* ::Section:: *)
(*Definition*)


(* ::Subsection:: *)
(*Helper functions*)


(* ::Subsubsection::Closed:: *)
(*FormulaComplexity*)


(* ::Input::Initialization:: *)
ClearAll[formulaComplexity,formulaComplexityHeuristic]

(*this option can be used for internal testing*)
(*Options[formulaComplexity]={Method->"Heuristic"};*)
(*the BuiltIn Method with SimplifyCount has the fundamental problem of not being continuous and thus of not allowing fine tuning*)

digitSum[int_Integer]:=If[$VersionNumber>=14,DigitSum[int],Total@IntegerDigits[int]]

formulaComplexityHeuristic[form_?NumericQ]:=
	N@Total[Cases[
			Inactivate[form]
		/.const_?(Quiet@MemberQ[Attributes[#],Constant]&):>1
			/.c_Complex:>ReIm[c]
				/.r:Rational[i1_Integer,i2_Integer]:>{i1,i2}
					/.Inactive[Sqrt][arg_]:>Inactive[Sqrt[{arg,arg}]]
						/.Alternatives[
							Inactive[Power][b_,Inactive[Times][m_,Inactive[Power][n_,-1]]|{m_,n_}],
							Inactive[Power][{b_},Inactive[Times][m_,Inactive[Power][n_,-1]]|{m_,n_}]]:>
								Table[b,Abs[n]+Abs[m]],
			_Integer,{0,Infinity}]/. j_Integer?NonPositive:>-j+1
				/.i_Integer:>Mean[1/2{5IntegerLength[i],digitSum[i],Total[Last/@FactorInteger[i]],Sqrt[Abs[N[i]]]}]]

formulaComplexity[form_?NumericQ]:=
	formulaComplexityHeuristic[form]		


(* ::Subsubsection::Closed:: *)
(*Utilities*)


(* ::Input::Initialization:: *)
realReplace[x_]:=If[Head[x]===Real,RootApproximant[x],x]


(* ::Subsubsection::Closed:: *)
(*Error management*)


(* ::Input::Initialization:: *)
failureNotReal=
Failure["NotReal",<|"MessageTemplate"->"The input parameters `nr` are not real numbers.","MessageParameters"-><|"nr"->#|>|>]&;
failureNotAlg=Failure["NotAlgebraic",<|"MessageTemplate"->"The input parameters `na` are not algebraic numbers.","MessageParameters"-><|"na"->#|>|>]&;
failureFareyStep=Failure["FareyStep",<|"MessageTemplate"->"The step parameter `s` is not allowed with the Farey range option.","MessageParameters"-><|"s"->#|>|>]&;
failureLowerBound=
	Failure["LowerBound",<|"MessageTemplate"->"The steps' lower bound parameter `d` cannot be negative.","MessageParameters"-><|"d"->#|>|>]&;
failureUpperBound=
Failure["UpperLowerBound",<|"MessageTemplate"->"The steps' upper bound `s` cannot be lower than the lower bound `d` in absolute value.","MessageParameters"-><|"s"->#1,"d"->#2|>|>]&;


(* ::Input::Initialization:: *)
failureThrow[arg_]:=
	If[MemberQ[arg,_Failure|$Failed,{0,Infinity}],
		Throw@First@Union@Cases[arg,_Failure|$Failed,{0,Infinity}],
		arg]


(* ::Subsection:: *)
(*Basic range*)


(* ::Subsubsection::Closed:: *)
(*Farey range*)


(* ::Input::Initialization:: *)
ClearAll[fareyRange]
fareyRange[r1_,r2_,r3_]:=
	Which[
		r3>=1,
			ResourceFunction["FareyRange"][r1,r2,r3],
		r3<=-1,
			Reverse[ResourceFunction["FareyRange"][r2,r1,-r3]],
		MatchQ[r3,Rational[1,_]],
			ResourceFunction["FareyRange"][r1,r2,1/r3],
		MatchQ[r3,Rational[-1,_]],
			Reverse[ResourceFunction["FareyRange"][r2,r1,-1/r3]],
		True,
			failureFareyStep[r3]]


(* ::Subsubsection::Closed:: *)
(*Elementary range*)


(* ::Input::Initialization:: *)
ClearAll[elemRange]

elemRange[{ord_},{r1_},opts:OptionsPattern[AlgebraicRange]]/;r1>=1:=
	Range[1,r1^ord]^(1/ord)
elemRange[{ord_},{r1_},opts:OptionsPattern[AlgebraicRange]]/;r1<1:=
	{}

elemRange[{ord_},{r1_,r2_},opts:OptionsPattern[AlgebraicRange]]/;0<=r1<=r2:=
	Range[r1^ord,r2^ord]^(1/ord)
elemRange[{ord_},{r1_,r2_},opts:OptionsPattern[AlgebraicRange]]/;r1<0&&r2>=0:=
	Join[
	-elemRange[{ord},{0,-r1},opts],
	elemRange[{ord},{0,r2},opts]
	]~cleanSort~OptionValue[WorkingPrecision]
elemRange[{ord_},{r1_,r2_},opts:OptionsPattern[AlgebraicRange]]/;r1<=r2<=0:=
	cleanSort[
	-elemRange[{ord},{-r2,-r1},opts],
	OptionValue[WorkingPrecision]]
elemRange[{ord_},{r1_,r2_},opts:OptionsPattern[AlgebraicRange]]/;r2<r1:=
	{}

elemRange[{ord_},{r1_,r2_,-1},opts:OptionsPattern[AlgebraicRange]]/;r1>=r2>=0:=
	Range[r1^ord,r2^ord,-1]^(1/ord)
elemRange[{ord_},{r1_,r2_,-1},opts:OptionsPattern[AlgebraicRange]]/;r2<0&&r1>=0:=
	Reverse@
	cleanSort[
		Join[
			-elemRange[{ord},{-r2,0,-1},opts],
			elemRange[{ord},{r1,0,-1},opts]],
		OptionValue[WorkingPrecision]]
elemRange[{ord_},{r1_,r2_,-1},opts:OptionsPattern[AlgebraicRange]]/;r2<=r1<=0:=
	Reverse@
	cleanSort[
		-elemRange[{ord},{-r2,-r1,-1},opts],
		OptionValue[WorkingPrecision]]
elemRange[{ord_},{r1_,r2_,-1},opts:OptionsPattern[AlgebraicRange]]/;r2>r1:=
	{}

(*the remaining definitions below are used only for the option "StepMethod"->"Root"*)

elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;0<=r1<=r2&&r3>0:=
	If[!OptionValue["FareyRange"],
		Range[r1^ord,r2^ord,r3^ord]^(1/ord),
		fareyRange[r1^ord,r2^ord,r3^ord]^(1/ord)]
		
elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r1<0&&r2>=0&&r3>0&&r3<=r2-r1:=
	cleanSort[
		Join[
			-elemRange[{ord},{0,-r1,r3},opts],
			elemRange[{ord},{0,r2,r3},opts]],
		OptionValue[WorkingPrecision]]

elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r1<0&&r2>=0&&r3>0&&r3>r2-r1:=
	{r1}

elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r1<=r2<=0&&r3>0:=
	-elemRange[{ord},{-r2,-r1,r3},opts]
	
elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;0<=r2<=r1&&r3<0:=
	Range[r1^ord,r2^ord,-(-r3)^ord]^(1/ord)

elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r2<0&&r1>=0&&r3<0&&Abs[r3]<=r1-r2:=
	Reverse@
		cleanSort[
			Join[
				-elemRange[{ord},{-r2,0,r3},opts],
				elemRange[{ord},{r1,0,r3},opts]],
			OptionValue[WorkingPrecision]]
			
elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r2<0&&r1>=0&&r3<0&&Abs[r3]>r1-r2:=
	{r1}

elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r2<=r1<=0&&r3<0:=
	-elemRange[{ord},{-r1,-r2,-r3},opts]

elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r2<r1&&r3>=0:=
	{}
elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r1<r2&&r3<=0:=
	{}


(* ::Subsubsection::Closed:: *)
(*Step range*)


(* ::Input::Initialization:: *)
ClearAll[factorRange]
factorRange[{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]:=
	Block[{max,as,one,zero,wp=OptionValue[WorkingPrecision]},
		max=Max[Abs[r1],Abs[r2]];
		as=Abs[r3];
		one=Max[1,as];
		zero=Which[
				r3>0&&r1>0,
					r1/max,
				r3>0&&r1<=0,
					0,
				r3<0&&r2>0,
					r2/max,
				r3<0&&r2<=0,
					0];
		If[!OptionValue["FareyRange"],
			If[r3>0,
				Join[
					Reverse@DeleteCases[Range[one,zero,-as],one],
					Range[one,max,as]],
				Join[
					Reverse@Range[one,max,as],
					DeleteCases[Range[one,zero,-as],one]]],
			If[IntegerQ[as],
				as=1/as];
			If[r3>0,
				Join[
					Reverse@DeleteCases[fareyRange[one,zero,-as],one],
					fareyRange[one,max,as]],
				Join[
					Reverse@fareyRange[one,max,as],
					DeleteCases[fareyRange[one,zero,-as],one]]]//failureThrow]]


(* ::Input::Initialization:: *)
ClearAll[outerRange]

outerRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r1<=r2&&r3>0&&r3<=Max[Abs[r1],Abs[r2]]:=
	Block[{elrg,fcrg,i,j,curr,first,last,rg,flo,fhi,wp=OptionValue[WorkingPrecision]},
	elrg=elemRange[{ord},{If[r3<=1,r1,r1/r3],r2},opts];
	fcrg=factorRange[{r1,r2,r3},opts];
	rg=CreateDataStructure["DynamicArray"];
	For[i=1,i<=Length[elrg],i++,
		curr=elrg[[i]];
		If[curr===0,rg["Append",0];Continue[]];
		If[curr>0,
			flo=r1/curr;fhi=r2/curr,
			flo=r2/curr;fhi=r1/curr];
		first=First@Nearest[fcrg->"Index",flo];
		last=Last@Nearest[fcrg->"Index",fhi];
		While[first<=Length[fcrg]&&fcrg[[first]]<flo,first++];
		While[last>=1&&fcrg[[last]]>fhi,last--];
		For[j=first,j<=last,j++,
			rg["Append",curr*fcrg[[j]]]]];
	SortBy[DeleteDuplicatesBy[rg//Normal,N[#,wp]&],N[#,wp]&]]

outerRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r2<=r1&&r3<0&&Abs[r3]<=Max[Abs[r1],Abs[r2]]:=
	Block[{elrg,fcrg,i,j,curr,first,last,rg,flo,fhi,wp=OptionValue[WorkingPrecision]},
	elrg=elemRange[{ord},{If[r3>=-1,r1,-r1/r3],r2,-1},opts];
	fcrg=factorRange[{r1,r2,r3},opts];
	rg=CreateDataStructure["DynamicArray"];
	For[i=1,i<=Length[elrg],i++,
		curr=elrg[[i]];
		If[curr===0,rg["Append",0];Continue[]];
		If[curr>0,
			flo=r2/curr;fhi=r1/curr,
			flo=r1/curr;fhi=r2/curr];
		first=First@Nearest[fcrg->"Index",fhi];
		last=Last@Nearest[fcrg->"Index",flo];
		While[first<=Length[fcrg]&&fcrg[[first]]>fhi,first++];
		While[last>=1&&fcrg[[last]]<flo,last--];
		For[j=first,j<=last,j++,
			rg["Append",curr*fcrg[[j]]]]];
	ReverseSortBy[DeleteDuplicatesBy[rg//Normal,N[#,wp]&],N[#,wp]&]]

outerRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r2<r1&&r3>=0:=
	{}
outerRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r1<=r2&&r3<=0:=
	{}
outerRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r1<=r2&&r3>0&&r3>Max[Abs[r1],Abs[r2]]:=
	{r1}
outerRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r2<=r1&&r3<0&&Abs[r3]>Max[Abs[r1],Abs[r2]]:=
	{r1}


(* ::Input::Initialization:: *)
ClearAll[stepRange]
stepRange[{ord_},{r1_,r2_,r3_:1},opts:OptionsPattern[AlgebraicRange]]:=
	Which[
		OptionValue["StepMethod"]==="Outer",
			outerRange[{ord},{r1,r2,r3},opts],	
		OptionValue["StepMethod"]==="Root",
			elemRange[{ord},{r1,r2,r3},opts]]


(* ::Subsubsection::Closed:: *)
(*Restricted range*)


cleanSort[list_List,wp_:MachinePrecision]:=SortBy[DeleteDuplicatesBy[list,N[#,wp]&],N[#,wp]&]


(* ::Input::Initialization:: *)
ClearAll[stepSelect,complexitySelect]

complexitySelect[list_List,c_]:=
	Select[list,formulaComplexity[#]<=c&]

stepSelect[list_List,d_]:=
	Block[{sel,eln,i},
	eln=list[[1]];
	sel={eln};
	
	For[i=2,i<=Length[list],i++,
		
		If[Abs[list[[i]]-eln]>=d,

			eln=list[[i]];
			AppendTo[sel,eln],
			
			Continue[]]];
	
	sel]~Quiet~N::meprec

stepSelect[{},d_,t_:0]:=
	{}


(* ::Input::Initialization:: *)
ClearAll[restrictRange]
restrictRange[main_,compl_,d_?NumericQ,wp_:MachinePrecision]/;d>0:=
	DeleteDuplicatesBy[stepSelect[complexitySelect[main,compl],d],N[#,wp]&]
restrictRange[main_,compl_,0,wp_:MachinePrecision]:=
	DeleteDuplicatesBy[complexitySelect[main,compl],N[#,wp]&]


(* ::Subsection::Closed:: *)
(*Main definition*)


(* ::Input::Initialization:: *)
ClearAll[AlgebraicRange,iAlgebraicRange]

Options[AlgebraicRange]={"RootOrder"->2,"FareyRange"->False,WorkingPrecision->MachinePrecision,"FormulaComplexity"->Infinity,"StepMethod"->"Outer","AlgebraicsOnly"->True};

(*internal main function*)

iAlgebraicRange[{ord_?NumericQ},{r1_,r2_,r3_:1},d_:0,opts:OptionsPattern[AlgebraicRange]]/;ord>=1&&NumericQ[r3]&&d>=0:=
	Block[{o,x,y,s,mainrange,fullrange},

		{o,x,y,s}=realReplace/@{ord,r1,r2,r3};

		If[!Element[{o,x,y,s},Reals],
			Failure["NotReal",
						failureNotReal[Select[{o,x,y,s},!Element[#,Reals]&]]]//failureThrow];

		If[!Element[{o,x,y,s},Algebraics]&&OptionValue["AlgebraicsOnly"],
			Failure["NotAlgebraic",
						failureNotAlg[Select[{o,x,y,s},!Element[#,Algebraics]&]]]//failureThrow];

		If[d>Abs[r3],
			failureUpperBound[r3,d]//failureThrow];
		
		mainrange=If[r3===1,
					elemRange[{o},{x,y}],
					stepRange[{o},{x,y,s},opts]];

		fullrange=mainrange
		(*in the extended paclet version here combinations of the basic range are made*);

		restrictRange[fullrange,OptionValue["FormulaComplexity"],d,OptionValue[WorkingPrecision]]//failureThrow]//Catch

iAlgebraicRange[ordL_List,rL_List,d_:0,opts:OptionsPattern[AlgebraicRange]]/;(Length[ordL]>=2&&d>=0):=
	Block[{stepNegQ,join,sort},
	stepNegQ=Length[rL]==3&&rL[[3]]<0;
	join=Join@@Map[failureThrow@iAlgebraicRange[{#},rL,d,opts]&,ordL];
	sort=If[stepNegQ,Reverse[#],#]&@cleanSort[join,OptionValue[WorkingPrecision]];
	If[d!=0,stepSelect[sort,d],sort]]//Catch

iAlgebraicRange[ord_Integer,rL_List,d_:0,opts:OptionsPattern[AlgebraicRange]]/;d>=0:=
	iAlgebraicRange[Range[2,ord],rL,d,opts]


(*external main function*)

AlgebraicRange[r1_?NumericQ,r2_?NumericQ,r3_:1,d_:0,opts:OptionsPattern[AlgebraicRange]]/;NumericQ[r3]&&d>=0:=
	iAlgebraicRange[OptionValue["RootOrder"],{r1,r2,r3},d,opts]

AlgebraicRange[r1_?NumericQ,opts:OptionsPattern[AlgebraicRange]]:=
	iAlgebraicRange[OptionValue["RootOrder"],{1,r1,1},0,opts]

AlgebraicRange[_,_,_,d_,opts:OptionsPattern[AlgebraicRange]]/;d<0:=
	failureLowerBound[d]


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
