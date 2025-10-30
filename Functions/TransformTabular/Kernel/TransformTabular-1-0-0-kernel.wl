(* ::Package:: *)

(* ::Title:: *)
(*TransformTabular (1.0.0)*)


(* ::Subtitle:: *)
(*Wolfram Resource Function contributed by: Daniele Gregori*)


(* ::Section:: *)
(*Package Header*)


BeginPackage["TransformTabular`"];


TransformTabular::usage=
"TransformTabular[tab, f]
  transforms all columns of a tabular through a single function.

TransformTabular[tab, f, i ;; j]
  transforms a span of columns of a tabular through a single function.

TransformTabular[tab, f, {col1, col2, \[Ellipsis]}]
  transforms a list of columns of a tabular through a single function.

TransformTabular[f, {col1, col2, \[Ellipsis]}]
  represents the operator form of TransformTabular.";


Begin["Private`"];


(* ::Section:: *)
(*Definition*)


ClearAll[TransformTabular]

TransformTabular[tab_Tabular,fun:_Function|_Symbol,cols_List]/;SubsetQ[ColumnKeys[tab],cols]:=
	Block[{schema},
	schema=KeyDrop[Normal[TabularSchema[tab]],"ColumnProperties"];
	Tabular[
		TransformColumns[tab, 
						Table[
							ckey->ReplaceAll[fun,Slot[1]->Slot[ckey]],
							{ckey,cols}]],
		schema]]
		

(*other possible column specifications:*)																																																																				

TransformTabular[tab_Tabular,fun:_Function|_Symbol,cols:_Span|{_Integer..}|All]:=
	TransformTabular[tab,fun,ColumnKeys[tab][[cols]]]
TransformTabular[tab_Tabular,fun:_Function|_Symbol,col_Integer]:=
	TransformTabular[tab,fun,ColumnKeys[tab][[{col}]]]
TransformTabular[tab_Tabular,fun:_Function|_Symbol,col_String]/;MemberQ[ColumnKeys[tab],col]:=
	TransformTabular[tab,fun,{col}]
	
(*all columns:*)	

TransformTabular[tab_Tabular,fun:_Function|_Symbol]:=
	TransformTabular[tab,fun,ColumnKeys[tab]]
	
(*operator forms:*)	

TransformTabular[fun:_Function|_Symbol,cols:_Span|_Integer|_String|_List|All][tab_Tabular]:=
	TransformTabular[tab,fun,cols]
TransformTabular[fun:_Function|_Symbol][tab_Tabular]:=
	TransformTabular[tab,fun]


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
