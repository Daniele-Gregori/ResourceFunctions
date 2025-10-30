(* ::Package:: *)

(* ::Title:: *)
(*ComplexRange (1.0.0)*)


(* ::Subtitle:: *)
(*Wolfram Resource Function contributed by: Daniele Gregori*)


(* ::Section:: *)
(*Package Header*)


BeginPackage["ComplexRange`"];


ComplexRange::usage=
"ComplexRange[z1]
  generates a rectangular range between 0 and the complex number z1.

ComplexRange[{z1}]
  generates a linear range between 0 and the complex number z1.

ComplexRange[z1, z2]
  generates a rectangular range between the complex numbers z1 and z2.

ComplexRange[{z1, z2}]
  generates a linear range between the complex numbers z1 and z2.

ComplexRange[z1, z2, z3]
  generates a rectangular range between the complex numbers z1 and z2, with real and imaginary steps Re[z3] and Im[z3] respectively.

ComplexRange[z1, z2, {\[CapitalDelta]zre, \[CapitalDelta]zim}]
  generates a rectangular range between the complex numbers z1 and z2, with real and imaginary steps \[CapitalDelta]zre and \[CapitalDelta]zim respectively.

ComplexRange[{z1, z2}, z3]
  generates a linear range between the complex numbers z1 and z2, with real and imaginary steps Re[z3] and Im[z3] respectively.

ComplexRange[{z1, z2}, {\[CapitalDelta]zre, \[CapitalDelta]zim}]
  generates a linear range between the complex numbers z1 and z2, with real and imaginary steps \[CapitalDelta]zre and \[CapitalDelta]zim respectively.";


Begin["Private`"];


(* ::Section:: *)
(*Definition*)


(* ::Input::Initialization:: *)
ClearAll[ComplexRange]

pattC=_Complex|_Real|_Rational|_Integer;
pattR=_Real|_Rational|_Integer;

fareyRange[arg1_,arg2_,arg3_]:=
	ResourceFunction["FareyRange"][
			arg1,
			arg2,
			If[IntegerQ@arg3,
				arg3,
				Throw@Failure["FareyFailed",
						<|"MessageTemplate"->
						"No Farey range with non-integer third argument `third` is allowed.",
						"MessageParameters"-><|"third"->arg3|>|>]]]


Options[ComplexRange]={"FareyRange"->False,"IncrementFirst"->Im};

ComplexRange::ReStep="The real part step specification `1` is not consistent with the real part bounds `2`, `3`";
ComplexRange::ImStep="The imaginary part step specification `1` is not consistent with the imaginary part bounds `2`, `3`";
ComplexRange::ReImStep="The real and imaginary steps specification `1` is not consistent with the bounds `2`, `3`";


preComplexRange[c1:pattC,c2:pattC,{r1:pattR,r2:pattR},options:OptionsPattern[ComplexRange]]:=
	Block[{res,ims,rgre,rgim,rg},
		
		res={Re[c1],Re[c2]};
		ims={Im[c1],Im[c2]};

		Which[r1==0&&r2!=0,If[Re[c1]!=Re[c2],
							ResourceFunction["ResourceFunctionMessage"][ComplexRange::ReStep,r1,Re[c1],Re[c2]];
							Throw[{}]],
			r2==0&&r1!=0,If[Im[c1]!=Im[c2],
							ResourceFunction["ResourceFunctionMessage"][ComplexRange::ImStep,r2,Im[c1],Im[c2]];
							Throw[{}]],
			r1==0&&r2==0,If[c1!=c2,
							ResourceFunction["ResourceFunctionMessage"][ComplexRange::ReImStep,{r1,r2},c1,c2];
							Throw[{}]]];
		
		rgre=If[!OptionValue["FareyRange"],
				Range[res[[1]],res[[2]],r1],
				fareyRange[res[[1]],res[[2]],r1]];
		rgim=I If[!OptionValue["FareyRange"],
				Range[ims[[1]],ims[[2]],r2],
				fareyRange[ims[[1]],ims[[2]],r2]];
		
		rg=Which[
			MemberQ[{Re,"Re"},OptionValue["IncrementFirst"]],{rgim,rgre},
			MemberQ[{Im,"Im"},OptionValue["IncrementFirst"]],{rgre,rgim},
			True,Throw@Failure["IncrementFirst",
					<|"MessageTemplate"->"IncrementFirst option value `opt` is not allowed: choose among Re or Im.",
					"MessageParameters"-><|"opt"->OptionValue["IncrementFirst"]|>|>]]]


ComplexRange[c1:pattC,c2:pattC,{r1:pattR,r2:pattR},options:OptionsPattern[ComplexRange]]:=
	Block[{rg},
		
		rg=preComplexRange[c1,c2,{r1,r2},options];

		Plus@@@Tuples[rg]]//Catch

ComplexRange[{c1:pattC,c2:pattC},{r1:pattR,r2:pattR},options:OptionsPattern[ComplexRange]]:=
	Block[{rg,dropF},
		
		rg=preComplexRange[c1,c2,{r1,r2},options];
		dropF=Take[#,Min[Length[rg[[1]]],Length[rg[[2]]]]]&;

		If[r1!=0&&r2!=0,
			MapThread[Plus,dropF/@rg],
			ComplexRange[c1,c2,{r1,r2},options]]]//Catch
	

ComplexRange[c1:pattC,c2:pattC,c3:pattC,options:OptionsPattern[ComplexRange]]:=
	ComplexRange[c1,c2,ReIm[c3],options]
ComplexRange[{c1:pattC,c2:pattC},c3:pattC,options:OptionsPattern[ComplexRange]]:=
	ComplexRange[{c1,c2},ReIm[c3],options]

ComplexRange[c1:pattC,c2:pattC,options:OptionsPattern[ComplexRange]]:=
	ComplexRange[c1,c2,{1,1},options]
ComplexRange[{c1:pattC,c2:pattC},options:OptionsPattern[ComplexRange]]:=
	ComplexRange[{c1,c2},{1,1},options]

ComplexRange[c2:pattC,options:OptionsPattern[ComplexRange]]:=
	ComplexRange[0,c2,options]
ComplexRange[{c2:pattC},options:OptionsPattern[ComplexRange]]:=
	ComplexRange[{0,c2},options]


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
