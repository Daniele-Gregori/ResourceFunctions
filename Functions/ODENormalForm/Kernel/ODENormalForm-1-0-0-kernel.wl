(* ::Package:: *)

(* ::Title:: *)
(*ODENormalForm (1.0.0)*)


(* ::Subtitle:: *)
(*Wolfram Resource Function contributed by: Daniele Gregori*)


(* ::Section:: *)
(*Package Header*)


BeginPackage["ODENormalForm`"];


ODENormalForm::usage=
"ODENormalForm[ode]
  returns the normal form of an ordinary differential equation.

ODENormalForm[ode, y]
  returns the normal form of an ordinary differential equation, with new dependent variable y.";


Begin["Private`"];


(* ::Section:: *)
(*Definition*)


ODENormalForm::usage=
"ODENormalForm[ODE] returns the normal form of an ordinary differential equation;
ODENormalForm[ODE,y] returns the normal form of an ordinary differential equation, with new dependent variable y.";

ODENormalForm::notde="The equality `1` is not a differential equation.";
ODENormalForm::multind="The differential equation `1` has more than one independent variable.";
ODENormalForm::multdep="The differential equation `1` has more than one dependent variable.";
ODENormalForm::baddep="The dependent variable `1` is confused with the indendent variable `2`.";
ODENormalForm::nlin0="The differential equation `1` is non-linear in the `2`-derivative.";
ODENormalForm::nlin1="The differential equation `1` is non-linear in the `2`-derivative.";

Options[ODENormalForm]={"SimplifyEquation"->False};

ODENormalForm[ode_Equal,options:OptionsPattern[ODENormalForm]]:=
	Block[{simpODE,odeE,rank,vI,vD,vA},
		simpODE=Simplify[ode];
		odeE=odeElements[ode,simpODE];
		If[And@@Map[!FailureQ[#]&,odeE],{rank,vI,vD}=odeE,Return[First@Select[odeE,FailureQ]]];
		vA=vDAuto[vI,vD];
		If[FailureQ[vA],Return[vA]];
		odeNormalFormMain[ode,vA,simpODE,rank,vI,vD,options]]

ODENormalForm[ode_Equal,y_Symbol,options:OptionsPattern[ODENormalForm]]:=
	Block[{simpODE,odeE,rank,vI,vD},
		simpODE=Simplify[ode];
		odeE=odeElements[ode,simpODE];
		If[And@@Map[!FailureQ[#]&,odeE],{rank,vI,vD}=odeE,Return[First@Select[odeE,FailureQ]]];
		odeNormalFormMain[ode,y,simpODE,rank,vI,vD,options]]

odeElements[ode_Equal,simpODE_Equal]:=
	Block[{rank,vIList,vDList,vI,vD},
		rank=Max@Flatten@Cases[simpODE,Derivative[n__][_][__]:>n,Infinity];
		If[rank<=0,
			Message[ODENormalForm::notde,ode];
			Failure["NotDiffEq",
						<|"MessageTemplate" -> ODENormalForm::notde,
						"MessageParameters"-> ode|>]];
		vIList=Union@Cases[simpODE,Derivative[__][_][x__]:>x,Infinity];
		vDList=Union@Cases[simpODE,Derivative[__][y_][__]:>y,Infinity];
		vI=If[Length@vIList<=1,
				First@vIList,
				Message[ODENormalForm::multind,ode];
				Failure["MultipleIndVar",
							<|"MessageTemplate" -> ODENormalForm::multind,
							"MessageParameters"-> ode|>]];
		vD=If[Length@vDList<=1,
				First@vDList,
				Message[ODENormalForm::multdep,ode];
				Failure["MultipleDepVar",
							<|"MessageTemplate" -> ODENormalForm::multdep,
							"MessageParameters"-> ode|>]];
		{rank,vI,vD}]
		
vDAuto[vI_,vD_]:=
	Block[{vDnFunU,vDnFunL},
		vDnFunU[v_]:=Symbol@ToUpperCase@ToString[v];
		vDnFunL[v_]:=Symbol@ToLowerCase@ToString[v];
		Which[
				vDnFunU[vD]=!=vD&&vDnFunU[vD]=!=vI,vDnFunU[vD],
				vDnFunL[vD]=!=vD&&vDnFunL[vD]=!=vI,vDnFunL[vD],
				vDnFunU[vD]===vI||vDnFunL[vD]===vI,
						Message[ODENormalForm::baddep,vD,vI];
						Failure["BadDepVar",
							<|"MessageTemplate" -> ODENormalForm::baddep,
							"MessageParameters"-> {vD,vI}|>]]]

odeNormalFormMain[ode_Equal,vDn_Symbol,simpODE_Equal,rank_Integer,vI_Symbol,vD_Symbol,options:OptionsPattern[ODENormalForm]]:=
	Block[{leftODE,c0List,c1List,c1Q,factorDer,fD,coeffOrd,multiplyPlus,trD,DSCV,collDFun,collD,finalODE,FSFun},
	
	FSFun:=If[!OptionValue["SimplifyEquation"],Simplify[#]&,FullSimplify[#]&];
	collDFun[odeq_Equal]:=Collect[odeq,Table[Derivative[n][vDn][vI],{n,0,rank}],FSFun];
	
	leftODE=Equal[(First[#]-Last[#])&@collDFun[simpODE],0];
	
	c0List=CoefficientList[leftODE[[1]],Derivative[rank][vD][vI]];
	c1List=CoefficientList[leftODE[[1]],Derivative[rank-1][vD][vI]];
	If[Length[c0List]>2||!FreeQ[Rest[c0List],vD],Message[ODENormalForm::nlin0,ode,rank];Return[ode]];
	If[Length[c1List]>2||!FreeQ[Rest[c1List],vD],Message[ODENormalForm::nlin1,ode,rank-1];Return[ode]];
	
	factorDer[coeff_]:=FSFun@Exp[-1/rank Integrate[coeff,vI]];
	coeffOrd[ord_]:=Coefficient[leftODE[[1]],Derivative[ord][vD][vI]];
	fD=factorDer[coeffOrd[rank-1]/coeffOrd[rank]];
	trD=vD[vI]==fD*vDn[vI];
	c1Q=!TrueQ[fD===1];
	
	DSCV=DSolveChangeVariables[Inactive[DSolve][leftODE,vD[vI],vI],vDn[vI],vI,trD];
	collD=collDFun[DSCV[[1]]];
	
	multiplyPlus[exp_,coeff_]:=If[Head[#]===Plus,Map[FSFun@Times[#,coeff]&,#],#]&@exp;
	
	finalODE=Equal[multiplyPlus[collD[[1]],1/Coefficient[collD[[1]],Derivative[rank][vDn][vI]]],0];
	
	If[c1Q,
			ConditionalExpression[finalODE,trD],
			finalODE/.vDn:>vD]]


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
