(* ::Package:: *)

(* ::Title:: *)
(*SpreadsheetTrace (1.0.0)*)


(* ::Subtitle:: *)
(*Wolfram Resource Function contributed by Daniele Gregori*)


(* ::Section:: *)
(*Package Header*)


BeginPackage["SpreadsheetTrace`"];


SpreadsheetTrace::usage=
"SpreadsheetTrace[file,cell] trace the dependencies of a file in a spreadsheet cell.";


Begin["Private`"];


(* ::Section:: *)
(*Definition*)


(* ::Subsection:: *)
(*Helpers*)


(* ::Subsubsection::Closed:: *)
(*ImportOnce*)


importOnce=ResourceFunction["ImportOnce"];


(* ::Subsubsection::Closed:: *)
(*Cell resolution*)


(* ::Input::Initialization:: *)
ssInd2Pos=ResourceFunction["SpreadsheetIndexToPosition"];
pos2SsInd=ResourceFunction["PositionToSpreadsheetIndex"];


(* ::Input::Initialization:: *)
row2Ind=ToExpression@First@
		StringCases[#,NumberString]&;


(* ::Subsubsection::Closed:: *)
(*Cross-sheet resolution*)


(* ::Input::Initialization:: *)
cleanCellRef[cell_String]:=
	If[StringContainsQ[cell,"!"],Last@StringSplit[cell,"!"],cell]


cellSheetIndex[cell_String,sheets_List,default_Integer:1]:=
	If[StringContainsQ[cell,"!"],
		First[FirstPosition[sheets,First@StringSplit[cell,"!"]],default],
		default]


(* ::Subsection:: *)
(*Parsing*)


(* ::Subsubsection::Closed:: *)
(*Main patterns*)


cellPatt={LetterCharacter..~~DigitCharacter..,
			"$"~~LetterCharacter..~~DigitCharacter..,
			LetterCharacter..~~"$"~~DigitCharacter..,
			"$"~~LetterCharacter..~~"$"~~DigitCharacter..};


(* ::Input::Initialization:: *)
cellGenPatt=Map[{__~~"!"~~#,#}&,cellPatt]//Flatten;


(* ::Input::Initialization:: *)
colPatt=LetterCharacter..;


(* ::Subsubsection::Closed:: *)
(*Formula parser*)


(* ::Input::Initialization:: *)
ClearAll[spreadsheetFormulaParse]

spreadsheetFormulaParse["",___]:={}

spreadsheetFormulaParse[_?NumericQ,___]:={}

spreadsheetFormulaParse[form_String,sheets_List,nrows_:{}]:=

Block[

{elpatt,shpatt,colpatt,cshpatt,rowqpatt,nrowqpatt,
cellrgqF,colrgqF,repcellrg,repcolrg,sh="",sq=False},

(*patterns*)

elpatt=cellPatt;

colpatt=colPatt;

shpatt=Map[
		{#,Table[s~~"!"~~#,{s,sheets}]}&,
		elpatt]//Flatten;

cshpatt=Table[s~~"!"~~colpatt,{s,sheets}];

rowqpatt=_?(StringCases[#,NumberString]=!={}&);

nrowqpatt=_?(StringCases[#,NumberString]==={}&);

(*range q*)

cellrgqF=StringContainsQ[#,":"]&;

colrgqF=StringMatchQ[#,Table[___~~shp~~"!"~~colpatt~~":"~~colpatt,{shp,sheets}]]&;


(*replace cell range*)
repcellrg:={a:rowqpatt,b:rowqpatt}:>
				Table[StringDelete[a,NumberString]<>ToString[j],
						Evaluate@{j,row2Ind@a,row2Ind@b}];

(*replace column range*)
repcolrg:={a:nrowqpatt,b:nrowqpatt}:>
			With[
				{sc=ssInd2Pos[cleanCellRef[a]<>"1"][[2]],
				ec=ssInd2Pos[b<>"1"][[2]],
				nr=If[nrows=!={}&&MemberQ[sheets,sh],
						nrows[[First[FirstPosition[sheets,sh],1]]],
						0]},

				If[nr>0,

					Table[

					If[sh=!="",
						sh<>"!"<>#,
						#]&@
						pos2SsInd[{r,c}],

					{c,sc,ec},{r,1,nr}]//Flatten,

					{}]];

	(*main parsing*)
	Map[
	If[!sq(*no column only ranges*),

			StringCases[#,
		Join[elpatt,shpatt]],

			StringCases[#,
		Join[elpatt,shpatt,cshpatt]]]&,


	Map[

			Which[

				!cellrgqF[#],

				#,

				cellrgqF[#]&&!colrgqF[#],

				StringSplit[#,":"]/.repcellrg,

				cellrgqF[#]&&colrgqF[#],

				sh=StringCases[#,Alternatives@@sheets][[1]];
				sq=If[sh=!={},True,False];
				StringSplit[#,":"]/.repcellrg/.repcolrg]&,

	
	StringSplit[form,{"(",")",","}],
			
	{1}],
		{1}]

(*cleaning*)
//DeleteCases[#,Alternatives[{},{{}}],Infinity]&

(*delete dollar*)
//ReplaceAll[#,s_String:>StringDelete[s,"$"]]&]


(* ::Subsection:: *)
(*Tracing*)


(* ::Subsubsection::Closed:: *)
(*Operations*)


(* ::Input::Initialization:: *)
formulaQ[pos_,si_Integer,formulas_]:=
	Part[formulas[[si]],Sequence@@pos]=!=""


(* ::Input::Initialization:: *)
getFormula[fq_?BooleanQ,pos_,si_Integer,{data_,formulas_}]:=
	If[fq,
		Part[formulas[[si]],Sequence@@pos],
		Part[data[[si]],Sequence@@pos]]


(* ::Input::Initialization:: *)
getParsing[fq_?BooleanQ,form_,{sheets_,data_:{}},optdup_:True]:=
	With[{nrows=If[data=!={},Length/@data,{}]},
		If[!fq,
			Return[{}]];
		If[optdup,
			Identity,
			DeleteDuplicates]@Flatten@
				spreadsheetFormulaParse[form,sheets,nrows]]


getPosition[cell_String]:=
	ssInd2Pos@cleanCellRef[cell]


(* ::Subsubsection::Closed:: *)
(*Cell pipeline*)


cellPipeline[v_List,cell_String,si_,{sheets_,data_,formulas_},optdup_:True]:=
	Block[{vec=v,pos,dim,test,nsi,fq,form,parse},

		pos=getPosition[cell];
		nsi=cellSheetIndex[cell,sheets,si];
		dim=Dimensions[data[[nsi]]];
		test=Not[pos[[1]]<=dim[[1]]&&pos[[2]]<=dim[[2]]];
		If[test,
			Return@{{},{},si}];

		fq=formulaQ[pos,nsi,formulas];
		form=getFormula[fq,pos,nsi,{data,formulas}];
		parse=getParsing[fq,form,{sheets,data},optdup];

		AppendTo[vec,form];

		{vec,parse,nsi}]


(* ::Subsubsection:: *)
(*Core recursion*)


ClearAll[iSpreadsheetTrace]

iSpreadsheetTrace[v_List,cell_String,psi_Integer,{sheets_,data_,formulas_},optdup_:True]:=
	Block[{vec=v,parse,si,nvec,nparse,nsi,ncell,i},
	
		AppendTo[vec,cell];
		{vec,parse,si}=cellPipeline[vec,cell,psi,{sheets,data,formulas},optdup];

		Which[
				    
			Length@parse==1,								
				nvec=parse;
				ncell=parse[[1]];	
				{nvec,nparse,nsi}=cellPipeline[nvec,ncell,si,{sheets,data,formulas},optdup];		
				nvec=iSpreadsheetTrace[nvec,nparse,nsi,{sheets,data,formulas},optdup];			
				AppendTo[vec,nvec],
			
			Length@parse>=2,		
                For[i=1,i<=Length@parse,i++,
                    ncell=parse[[i]];
                    nvec=iSpreadsheetTrace[{},ncell,si,{sheets,data,formulas},optdup];           
				    AppendTo[vec,nvec]]];
				
		vec]
				
iSpreadsheetTrace[v_List,parse_List,si_Integer,{sheets_,data_,formulas_},optdup_:True]:=
	Block[{vec=v,i,ncell,nvec},
	
		Which[
		
			Length@parse==1,
				ncell=parse[[1]];
				nvec=iSpreadsheetTrace[ncell,si,{sheets,data,formulas},optdup];	
				AppendTo[vec,nvec],
		
			Length@parse>=2,
				For[i=1,i<=Length@parse,i++,
					ncell=parse[[i]];
					nvec=iSpreadsheetTrace[ncell,si,{sheets,data,formulas},optdup];
					AppendTo[vec,nvec]]];	
						
		vec]
	
iSpreadsheetTrace[cell_String,si_Integer,{sheets_,data_,formulas_},optdup_:True]:=
	iSpreadsheetTrace[{},cell,si,{sheets,data,formulas},optdup]
	
iSpreadsheetTrace[{},{},si_Integer,{sheets_,data_,formulas_},optdup_:True]:=
	Nothing


(* ::Subsection::Closed:: *)
(*Main*)


ClearAll[SpreadsheetTrace]

Options[SpreadsheetTrace]={"TraceDuplicates"->True};

SpreadsheetTrace[{sheets_List,data_List,formulas_List},cell_String,opts:OptionsPattern[SpreadsheetTrace]]/;
	Depth@sheets==2&&Depth@data>=4&&Depth@formulas>=4&&StringMatchQ[cell,cellGenPatt]:=
	
	Block[{si,optdup},
	
		si=cellSheetIndex[cell,sheets];	
		optdup=OptionValue["TraceDuplicates"];
		
		iSpreadsheetTrace[{},cell,si,{sheets,data,formulas},optdup]]

SpreadsheetTrace[file:_File|_String,cell_String,opts:OptionsPattern[SpreadsheetTrace]]/;
	FileExistsQ[file]&&StringMatchQ[cell,cellGenPatt]:=
	
	SpreadsheetTrace[
		importOnce[ExpandFileName@file,{{"Sheets","Data","Formulas"}}],cell,opts]


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
