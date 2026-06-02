(* ::Package:: *)

(* ::Title:: *)
(*TranscendentalRange (1.0.0)*)


(* ::Subtitle:: *)
(*Wolfram Resource Function contributed by Daniele Gregori*)


(* ::Section:: *)
(*Package Header*)


BeginPackage["TranscendentalRange`"];


TranscendentalRange::usage=
"TranscendentalRange[x] gives all transcendental numbers of the form t = b\[CenterDot]e^a with 1 \[LessEqual] t \[LessEqual] x, where a and b are algebraics in Range[x];
TranscendentalRange[x, y] gives all transcendental numbers of the form t = b\[CenterDot]e^a with x \[LessEqual] t \[LessEqual] y, where a and b are algebraics in Range[x, y];
TranscendentalRange[x, y, s] gives all transcendental numbers of the form t = b\[CenterDot]e^a with x \[LessEqual] t \[LessEqual] y and s > 0, where a and b are algebraics in Range[x, y, s];
TranscendentalRange[x, y, s, d] requires a lower bound on the steps d.";


Begin["`Private`"];


(* ::Section:: *)
(*Definition*)


(* ::Subsection:: *)
(*Auxiliary functions*)


(* ::Subsubsection::Closed:: *)
(*FormulaComplexity*)


(* ::Input::Initialization:: *)
ClearAll[formulaComplexity]

digitSum[int_Integer]:=If[$VersionNumber>=14,DigitSum[int],Total@IntegerDigits[int]]

formulaComplexity[form_?NumericQ]:=
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


(* ::Subsubsection::Closed:: *)
(*Restricted range*)


(* ::Input::Initialization:: *)
complexitySelect[list_List,c_]:=
	Select[list,formulaComplexity[#]<=c&]

ClearAll[stepSelect]
stepSelect[list_List,d_]:=
	Block[{sel,eln,i},
	eln=list[[1]];
	sel=CreateDataStructure["DynamicArray"];
	sel["Append",eln];
	
	For[i=2,i<=Length[list],i++,
		
		If[Abs[list[[i]]-eln]>=d,

			eln=list[[i]];
			sel["Append",eln],
			
			Continue[]]];
	
	Normal@sel]~Quiet~N::meprec

stepSelect[{},d_]:=
	{}

stepSelect[{},d_,t_:0]:=
	{}


(* ::Input::Initialization:: *)
restrictRange[main_,compl_,d_:0]:=
	If[d!=0,stepSelect[#,d],#]&[complexitySelect[main,compl]]


(* ::Subsection:: *)
(*Generator ranges*)


(* ::Subsubsection::Closed:: *)
(*AlgebraicRange*)


(* ::Input::Initialization:: *)
ClearAll[algebraicRange]
algebraicRange[args__]:=ResourceFunction["AlgebraicRange"][args];


(* ::Subsubsection::Closed:: *)
(*FareyRange*)


(* ::Input::Initialization:: *)
ClearAll[fareyRange]
fareyRange[r1_,r2_,r3_]:=
	If[r3>=1,
		ResourceFunction["FareyRange"][r1,r2,r3],
		Which[(*intuitive alternative reciprocal step*)
			MatchQ[r3,Rational[1,_]],
				ResourceFunction["FareyRange"][r1,r2,1/r3],
			MatchQ[r3,Rational[-1,_]],
				Reverse[ResourceFunction["FareyRange"][r2,r1,-1/r3]],
			True,
				failureFareyStep[r3]]]


(* ::Subsubsection::Closed:: *)
(*Basic range*)


(* ::Input::Initialization:: *)
range[x_,y_,z_,opt_String]:=
Switch[opt,
		"Rational",
			Range[x,y,z],
		"Algebraic",
			algebraicRange[x,y,z],
		"RationalFarey",
			fareyRange[x,y,z],
		"AlgebraicFarey",
			algebraicRange[x,y,z,"FareyRange"->True]]


(* ::Subsubsection::Closed:: *)
(*Argument failures*)


(* ::Input::Initialization:: *)
failureNotAlgebraics=
Failure["ArgsNotAlgebraic",<|"MessageTemplate"->"The range arguments provided `ls` are not all algebraic numbers.","MessageParameters"-><|"ls"->#|>|>]&;


(* ::Input::Initialization:: *)
failureFareyStep=Failure["FareyStep",<|"MessageTemplate"->"The step parameter `s` is not allowed with the Farey range option.","MessageParameters"-><|"s"->#|>|>]&;


(* ::Subsection:: *)
(*Methods generalities*)


(* ::Subsubsection::Closed:: *)
(*Transcendental types*)


(* ::Text:: *)
(*All possible methods include the following transcendental functions types:*)


(* ::Input::Initialization:: *)
$trig={Sin,Cos,Tan,Cot,Sec,Csc};
$hyp={Sinh,Cosh,Tanh,Coth,Sech,Csch};
$invtrig={ArcSin,ArcCos,ArcTan,ArcCot,ArcSec,ArcCsc};
$invhyp={ArcSinh,ArcCosh,ArcTanh,ArcCoth,ArcSech,ArcCsch};
$trsctypes=Join[{Exp,Log,Power},$trig,$hyp,$invtrig,$invhyp];


(* ::Subsubsection::Closed:: *)
(*Domains*)


(* ::Text:: *)
(*Domains for the transcendental functions (namely, for the second arguments of Outer or monotonicOuter):*)


(* ::Input::Initialization:: *)
ClearAll[domain]
domain[_]=True&; 
domain[Log]=#>0&;
domain[Power]=#>0&;
domain[Coth]=#!=0&;
domain[Csch]=#!=0&;
domain[ArcCosh]=#>=1&;
domain[ArcTanh]=-1<#<1&;
domain[ArcCoth]=Abs[#]>1&;
domain[ArcSech]=0<#<=1&;
domain[ArcCsch]=#!=0&;
domain[Tan]=Abs@FractionalPart[#/\[Pi]]!=1/2&;
domain[Sec]=Abs@FractionalPart[#/\[Pi]]!=1/2&;
domain[Cot]=FractionalPart[#/\[Pi]]!=0&;
domain[Csc]=FractionalPart[#/\[Pi]]!=0&;
domain[ArcSin]=Abs[#]<=1&;
domain[ArcCos]=Abs[#]<=1&;
domain[ArcCot]=#!=0&;
domain[ArcSec]=Abs[#]>=1&;
domain[ArcCsc]=Abs[#]>=1&;


(* ::Subsubsection::Closed:: *)
(*General testing method*)


(* ::Text:: *)
(*The following general method is simpler to implement but also "naive" in the sense that it uses the default inefficient version of Outer. Then it can be used as a method for testing the more sophisticated efficient implementation with monotonicOuter.*)


(* ::Text:: *)
(*(It is also currently the default method for direct trigonometric functions.)*)


(* ::Input::Initialization:: *)
(*elementary testing range with only one function at a time*)

ClearAll[elemNaiveRange]

elemNaiveRange[x_,y_,z_:1,fun:_Symbol|_String:Exp,opt_String:"Rational"]/;NumericQ[z]:=
Block[
{rgmain,min=If[x<y,x,y],max=If[x<y,y,x]},

(*arguments basic range, to be restricted below*)
rgmain=range[x,y,z,opt];

DeleteCases[
Select[

Outer[

(*function with two arguments*)
Which[
MemberQ[{Exp,Log,Splice@Join[$trig,$hyp,$invtrig,$invhyp]},fun],
	#1 fun[#2],
fun===Power,
	#2^#1,
True,
	$Failed]&,

(*first argument*)
Which[
	MemberQ[{Exp,Log,Splice@Join[$trig,$hyp,$invtrig,$invhyp]},fun],
		rgmain,
	fun===Power,
			DeleteCases[rgmain,_Rationals]],

(*second argument*)
Which[
		
		MemberQ[{Log,Power,Coth,Csch,ArcCosh,ArcTanh,ArcCoth,ArcSech,ArcCsch,Tan,Sec,Cot,Csc,ArcSin,ArcCos,ArcCot,ArcSec,ArcCsc},fun],
			Select[rgmain,domain[fun]],

		True,
			rgmain
		]]//Flatten,
min<=#<=max&],
_?(Element[#,Algebraics]&)]]


(* ::Code::Initialization:: *)
ClearAll[combinedNaiveRange];

Options[combinedNaiveRange]={WorkingPrecision->MachinePrecision,"GeneratorsDomain"->Rationals};

combinedNaiveRange[x_,y_,z_:1,funs_List,opts:OptionsPattern[combinedNaiveRange]]/;NumericQ[z]:=
	Block[{funL,patf,extrarg,prec=OptionValue[WorkingPrecision],optalg=optGenerators[OptionValue["GeneratorsDomain"]]},
		funL=If[funs=!={All},
			Flatten@funs,
			$trsctypes];

		patf=_?(MemberQ[$trsctypes,#]&);
		extrarg=#/.Times[a_, patf[arg_]]|patf[arg_]:>Abs@N[arg,prec]&;

		
Values@Map[First@SortBy[#,extrarg]&,GroupBy[Join@@Map[elemNaiveRange[x,y,z,#,optalg]&,funL],N[#,prec]&]]]


sortNaiveRange[x_,y_,z_:1,fun:_Symbol|_String|_List|All,opts:OptionsPattern[combinedNaiveRange]]/;NumericQ[z]:=
	If[z>0,SortBy,ReverseSortBy][combinedNaiveRange[x,y,z,{fun},opts],N[#,OptionValue[WorkingPrecision]]&]


(* ::Subsubsection::Closed:: *)
(*Monotonic outer*)


(* ::Input::Initialization:: *)
monotonicOuter[fun_Function,{min_,max_},ls1_List,ls2_List,{mi_,mj_},sign_]:=
	Block[{i,j,new,begin,end,rgQ,outer},
		
		outer=CreateDataStructure["DynamicArray"];				

		For[
			Switch[mi,
					1,i=1,
					-1,i=Length[ls1]],
			Switch[mi,
					1,i<=Length[ls1],
					-1,i>=1],
			Switch[mi,
					1,i++,
					-1,i--],

			begin=True;

			end=False;

			For[

				Switch[mj,
					1,j=1,
					-1,j=Length[ls2]],
				Switch[mj,
					1,j<=Length[ls2],
					-1,j>=1],
				Switch[mj,
					1,j++,
					-1,j--],

				

				new=fun[ls1[[i]],ls2[[j]]];
				
				rgQ=min<=new<=max;
				
				If[rgQ,
					begin=False];

				Which[new>max&&sign===1,
						end=True,
					new<min&&sign===-1,
						end=True];
				
				Which[
					rgQ&&!begin,
						outer["Append",new],
					begin&&!end,
						(*this should be avoided with better splitting*)
						Echo[{"redundant",ls1[[i]],ls2[[j]]}];
						Continue[],
					True,
						Break[]]]];

		Normal@outer]//QuietEcho


(* ::Subsubsection::Closed:: *)
(*Range preprocessing*)


(* ::Input::Initialization:: *)
(*splitRange:split a sorted list into segments at given points*)
ClearAll[splitRange]
splitRange[list_List,splitPts_List,z_,segs_,count_]:=Block[{pts,bounds,n,seg},pts=Sort[splitPts];
bounds=Join[{-Infinity},pts,{Infinity}];
n=Length[bounds]-1;
count=n;
Do[seg=Select[list,bounds[[k]]<=#<=bounds[[k+1]]&];
segs[k]=If[z>0,seg,Reverse[seg]],{k,n}];]


(* ::Input::Initialization:: *)
(*preprRange:prepare coefficient and argument ranges for monotonicOuter.
#1 (coefficient) takes values in the whole range[x,y,z].
#2 (argument to f) takes values only where f is defined.
Each range is split independently at its own critical points for efficient Break[] in monotonicOuter.*)
ClearAll[preprRange]

preprRange[
{x_,y_,z_,opt_},
{cAlg_,cSing_,cSplit_},
{aDom_,aAlg_,aSing_,aSplit_},
{rc_,ra_,cs_,as_,ncs_,nas_}]:=

Block[{base},

base=range[x,y,z,opt];

(*Coefficient range:full range minus algebraic/singular points*)
rc=base;
If[cAlg=!=None,rc=DeleteCases[rc,cAlg]];
If[Length[cSing]>0,rc=DeleteCases[rc,Alternatives@@cSing]];

(*Argument range:domain-restricted,minus algebraic/singular*)
ra=Select[base,aDom];
If[aAlg=!=None,ra=DeleteCases[ra,aAlg]];
If[Length[aSing]>0,ra=DeleteCases[ra,Alternatives@@aSing]];

splitRange[rc,cSplit,z,cs,ncs];
splitRange[ra,aSplit,z,as,nas];]


(* ::Subsection:: *)
(*Methods implementations*)


(* ::Subsubsection::Closed:: *)
(*Exp*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{Exp[x],x Exp[x]},{x,-2,1},Epilog->{PointSize@Large,Point@{-1,-Exp[-1]}}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:Exp,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],0,{},{-1}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[2],as[1],{1,-1},1],monotonicOuter[fun,{min,max},cs[2],as[2],{1,1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[1],as[1],{-1,-1},-1],monotonicOuter[fun,{min,max},cs[1],as[2],{-1,1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*Log*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{Log[x],x Log[x]},{x,0,2},Epilog->{PointSize@Large,Point@{1/E,-1/E}}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:Log,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],1,{},{1/E,1}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[1],as[1],{-1,1},1],monotonicOuter[fun,{min,max},cs[1],as[2],{-1,-1},1],
monotonicOuter[fun,{min,max},cs[2],as[3],{1,1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[2],as[1],{1,-1},-1],monotonicOuter[fun,{min,max},cs[2],as[2],{1,1},-1],monotonicOuter[fun,{min,max},cs[1],as[3],{-1,1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*Sinh*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{Sinh[x],x Sinh[x]},{x,-2,2},Epilog->{PointSize@Large,Point@{0,0}}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:Sinh,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],0,{},{0}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[1],as[1],{-1,-1},1],
monotonicOuter[fun,{min,max},cs[2],as[2],{1,1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[2],as[1],{1,-1},-1],monotonicOuter[fun,{min,max},cs[1],as[2],{-1,1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*Cosh*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{Cosh[x],x Cosh[x]},{x,-2,2},Epilog->{PointSize@Large,Point@{0,0}}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:Cosh,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],0,{},{0}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[2],as[2],{1,1},1],
monotonicOuter[fun,{min,max},cs[2],as[1],{1,-1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[1],as[2],{-1,1},-1],monotonicOuter[fun,{min,max},cs[1],as[1],{-1,-1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*Tanh*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{Tanh[x],x Tanh[x]},{x,-2,2},Epilog->{PointSize@Large,Point@{0,0}}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:Tanh,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],0,{},{0}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[2],as[2],{1,1},1],
monotonicOuter[fun,{min,max},cs[1],as[1],{-1,-1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[1],as[2],{-1,1},-1],monotonicOuter[fun,{min,max},cs[2],as[1],{1,-1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*Coth*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{Coth[x],x Coth[x]},{x,-2,2},Epilog->{PointSize@Large,Point@{0,1}}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:Coth,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],0,{0},{0}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[2],as[2],{1,-1},1],
monotonicOuter[fun,{min,max},cs[1],as[1],{-1,1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[1],as[2],{-1,-1},-1],monotonicOuter[fun,{min,max},cs[2],as[1],{1,1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*Sech*)


(* ::Item:: *)
(*Turning point*)


(* ::Input::Initialization:: *)
turning[Sech,2]=Entity["MathematicalConstant","CothFixedPointConstant"][EntityProperty["MathematicalConstant","NumericalApproximation"]];


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*With[{turn=turning[Sech,2]},*)
(*Plot[{Sech[x],x Sech[x]},{x,-2,2},Epilog->{{{PointSize@Large,Point@{-turn,-turn Sech[turn]},{PointSize@Large,Point@{turn,turn Sech[turn]}}}}}]]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:Sech,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn,turn=turning[f,2]},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],0,{},{-turn,0,turn}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[2],as[4],{1,1},1],
monotonicOuter[fun,{min,max},cs[2],as[3],{1,1},1],
monotonicOuter[fun,{min,max},cs[2],as[2],{1,-1},1],
monotonicOuter[fun,{min,max},cs[2],as[1],{1,-1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[1],as[4],{-1,1},-1],
monotonicOuter[fun,{min,max},cs[1],as[3],{-1,1},-1],
monotonicOuter[fun,{min,max},cs[1],as[2],{-1,-1},-1],
monotonicOuter[fun,{min,max},cs[1],as[1],{-1,-1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*Csch*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{Csch[x],x Csch[x]},{x,-2,2},Epilog->{PointSize@Large,Point@{0,1}}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:Csch,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],0,{0},{0}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[2],as[2],{1,-1},1],
monotonicOuter[fun,{min,max},cs[1],as[1],{-1,1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[1],as[2],{-1,-1},-1],monotonicOuter[fun,{min,max},cs[2],as[1],{1,1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*ArcSinh*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{ArcSinh[x],x ArcSinh[x]},{x,-2,2},Epilog->{PointSize@Large,Point@{0,0}}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:ArcSinh,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],0,{},{0}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[1],as[1],{-1,-1},1],
monotonicOuter[fun,{min,max},cs[2],as[2],{1,1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[2],as[1],{1,-1},-1],monotonicOuter[fun,{min,max},cs[1],as[2],{-1,1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*ArcCosh*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{ArcCosh[x],x ArcCosh[x]},{x,0,2},Epilog->{PointSize@Large,Point@{1/E,-1/E}}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:ArcCosh,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],1,{},{}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[
monotonicOuter[fun,{min,max},cs[2],as[1],{1,1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[1],as[1],{-1,1},-1]];

Which[0<=x<=y||0<=y<=x,outp,x<=y<=0||y<=x<=0,outn,x<=0&&y>=0,outn~Join~outp,y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*ArcTanh*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{ArcTanh[x],x ArcTanh[x]},{x,-2,2},Epilog->{PointSize@Large,Point@{0,0}}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:ArcTanh,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],0,{},{0}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[1],as[1],{-1,-1},1],
monotonicOuter[fun,{min,max},cs[2],as[2],{1,1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[2],as[1],{1,-1},-1],monotonicOuter[fun,{min,max},cs[1],as[2],{-1,1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*ArcCoth*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{ArcCoth[x],x ArcCoth[x]},{x,-2,2}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:ArcCoth,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],0,{-1,1},{-1,1}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[2],as[3],{1,-1},1],
monotonicOuter[fun,{min,max},cs[1],as[1],{-1,1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[1],as[3],{-1,-1},-1],monotonicOuter[fun,{min,max},cs[2],as[1],{1,1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*ArcSech*)


(* ::Item:: *)
(*Turning point*)


(* ::Input::Initialization:: *)
rooteq[ArcSech,2]=D[x ArcSech[x],x]==0//PowerExpand//Simplify;
turning[ArcSech,2]=With[{prec=1000},FindRoot[rooteq[ArcSech,2],{x,0.5},PrecisionGoal->prec,WorkingPrecision->prec][[1,2]]];


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*With[{turn=turning[ArcSech,2]},Plot[{ArcSech[x],x ArcSech[x]},{x,0,2},Epilog->{PointSize@Large,Point@{turn,turn ArcSech[turn]}}]]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:ArcSech,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn,turn=turning[f,2]},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],1,{0},{turn}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[
monotonicOuter[fun,{min,max},cs[2],as[1],{1,-1},1],
monotonicOuter[fun,{min,max},cs[2],as[2],{1,-1},1]];

outn:=Join[
monotonicOuter[fun,{min,max},cs[1],as[1],{-1,-1},-1],
monotonicOuter[fun,{min,max},cs[1],as[2],{-1,-1},-1]];

Which[0<=x<=y||0<=y<=x,outp,x<=y<=0||y<=x<=0,outn,x<=0&&y>=0,outn~Join~outp,y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*ArcCsch*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{ArcCsch[x],x ArcCsch[x]},{x,-2,2},Epilog->{PointSize@Large,Point@{0,0}}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:ArcCsch,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],0,{0},{0}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[2],as[2],{1,-1},1],
monotonicOuter[fun,{min,max},cs[1],as[1],{-1,1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[1],as[2],{-1,-1},-1],monotonicOuter[fun,{min,max},cs[2],as[1],{1,1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*ArcSin*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{ArcSin[x],x ArcSin[x]},{x,-2,2},Epilog->{PointSize@Large,Point@{0,0}}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:ArcSin,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],0,{},{0}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[1],as[1],{-1,-1},1],
monotonicOuter[fun,{min,max},cs[2],as[2],{1,1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[2],as[1],{1,-1},-1],monotonicOuter[fun,{min,max},cs[1],as[2],{-1,1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*ArcCos*)


(* ::Item:: *)
(*Turning point*)


(* ::Input::Initialization:: *)
rooteq[ArcCos,2]=D[x ArcCos[x],x]==0//PowerExpand//Simplify;
turning[ArcCos,2]=With[{prec=1000},FindRoot[rooteq[ArcCos,2],{x,0.5},PrecisionGoal->prec,WorkingPrecision->prec][[1,2]]];


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*With[{turn=turning[ArcCos,2]},Plot[{ArcCos[x],x ArcCos[x]},{x,-2,2},Epilog->{PointSize@Large,Point@{turn,turn ArcCos[turn]}}]]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:ArcCos,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn,turn=turning[f,2]},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],1,{},{turn}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[
monotonicOuter[fun,{min,max},cs[2],as[2],{1,-1},1],
monotonicOuter[fun,{min,max},cs[2],as[1],{1,-1},1]];

outn:=Join[
monotonicOuter[fun,{min,max},cs[1],as[2],{-1,-1},-1],
monotonicOuter[fun,{min,max},cs[1],as[1],{-1,-1},-1]];

Which[0<=x<=y||0<=y<=x,outp,x<=y<=0||y<=x<=0,outn,x<=0&&y>=0,outn~Join~outp,y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*ArcTan*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{ArcTan[x],x ArcTan[x]},{x,-2,2},Epilog->{PointSize@Large,Point@{0,0}}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:ArcTan,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],0,{},{0}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[1],as[1],{-1,-1},1],
monotonicOuter[fun,{min,max},cs[2],as[2],{1,1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[2],as[1],{1,-1},-1],monotonicOuter[fun,{min,max},cs[1],as[2],{-1,1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*ArcCot*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{ArcCot[x],x ArcCot[x]},{x,-20,20},Epilog->{PointSize@Large,Point@{0,0}}]]*)


(* ::Item:: *)
(*Definition*)


coreRange[{f : ArcCot, 2}, x_, y_, z_ : 1, opt_String : "Rational"] := 
Block[{fun = # f[#2] &, min = If[z > 0, x, y], max = If[z > 0, y, x], rc, ra, cs, as, ncs, nas, outp, outn},
  
  preprRange[
   {x, y, z, opt},
   {0, {}, {0}},
   {domain[f], 0, {0}, {0}},
   {rc, ra, cs, as, ncs, nas}];
  
  outp := Join[monotonicOuter[fun, {min, max}, cs[2], as[2], {1, -1}, 1],
    monotonicOuter[fun, {min, max}, cs[1], as[1], {-1, 1}, 1]];
  
  outn := Join[monotonicOuter[fun, {min, max}, cs[1], as[2], {-1, -1}, -1], 
  monotonicOuter[fun, {min, max}, cs[2], as[1], {1, 1}, -1]];
  
  Which[
   0 <= x <= y || 0 <= y <= x, outp,
   x <= y <= 0 || y <= x <= 0, outn,
   x <= 0 && y >= 0, outn~Join~outp,
   y <= 0 && x >= 0, outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*ArcSec*)


(* ::Item:: *)
(*Turning point*)


(* ::Input::Initialization:: *)
rooteq[ArcSec,2]=D[ x ArcSec[x],x]==0//PowerExpand//Simplify;
turning[ArcSec,2]=With[{prec=1000},FindRoot[rooteq[ArcSec,2],{x,-10},PrecisionGoal->prec,WorkingPrecision->prec][[1,2]]];


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*With[{turn=turning[ArcSec,2]},*)
(*Plot[{ArcSec[x],x ArcSec[x]},{x,-2,2},Epilog->{PointSize@Large,Point@{turn,turn ArcSec[turn]}}]]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:ArcSec,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn,
turn=turning[f,2]},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],1,{},{turn,-1,1}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[2],as[4],{1,1},1],
monotonicOuter[fun,{min,max},cs[2],as[2],{1,1},1],
monotonicOuter[fun,{min,max},cs[2],as[1],{1,1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[1],as[4],{-1,1},-1],
monotonicOuter[fun,{min,max},cs[1],as[2],{-1,1},-1],
monotonicOuter[fun,{min,max},cs[1],as[1],{-1,1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*ArcCsc*)


(* ::Item:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*Plot[{ArcCsc[x],x ArcCsc[x]},{x,-2,2}]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f:ArcCsc,2},x_,y_,z_:1,opt_String:"Rational"]:=Block[{fun=# f[#2]&,min=If[z>0,x,y],max=If[z>0,y,x],rc,ra,cs,as,ncs,nas,outp,outn},

preprRange[
{x,y,z,opt},
{0,{},{0}},
{domain[f],0,{},{-1,1}},
{rc,ra,cs,as,ncs,nas}];

outp:=Join[monotonicOuter[fun,{min,max},cs[2],as[3],{1,-1},1],
monotonicOuter[fun,{min,max},cs[1],as[1],{-1,1},1]];

outn:=Join[monotonicOuter[fun,{min,max},cs[1],as[3],{-1,-1},-1],monotonicOuter[fun,{min,max},cs[2],as[1],{1,1},-1]];

Which[
0<=x<=y||0<=y<=x,outp,
x<=y<=0||y<=x<=0,outn,
x<=0&&y>=0,outn~Join~outp,
y<=0&&x>=0,outp~Join~outn]]


(* ::Subsubsection::Closed:: *)
(*Power*)


(* ::Item:: *)
(*Turning point*)


(* ::Input::Initialization:: *)
rooteq[Power,2]=D[ (-x)^x,x]==0//Simplify;
turning[Power,2]=With[{prec=1000},FindRoot[rooteq[Power,2],{x,-0.1},PrecisionGoal->prec,WorkingPrecision->prec][[1,2]]];


(* ::Item::Initialization:: *)
(*Plot*)


(* ::Input:: *)
(*If[$Notebooks,*)
(*With[{turn = turning[Power, 2]}, Plot[{Power[2,x], Power[Abs[x],x]}, {x, -2, 2}, Epilog -> {PointSize@Large, Point@{turn,  Power[Abs[turn],turn]}}]]]*)


(* ::Item:: *)
(*Definition*)


(* ::Input::Initialization:: *)
coreRange[{f : Power, 2}, x_, y_, z_ : 1, opt_String : "Rational"] := Block[{fun = #1^#2 &, min = If[z > 0, x, y], max = If[z > 0, y, x], rc, ra, cs, as, ncs, nas, outp, outn,
turn=turning[Power,2]},
  
  preprRange[
   {x, y, z, opt},
   {0, {}, {turn,0}},
   {domain[f], 1, {}, {1}},
   {rc, ra, cs, as, ncs, nas}];
 

cs[1]=Select[cs[1],!Element[#,Rationals]&];
cs[2]=Select[cs[2],!Element[#,Rationals]&];
cs[3]=Select[cs[3],!Element[#,Rationals]&];

outp := 
Select[Join[monotonicOuter[fun, {min, max},as[1], cs[3],  {1, 1}, 1],
monotonicOuter[fun, {min, max},as[2], cs[3],  {1, 1}, 1],
monotonicOuter[fun, {min, max},  as[1],cs[2], {1,-1}, 1],
monotonicOuter[fun, {min, max},as[2], cs[2],  {1,- 1}, 1],
monotonicOuter[fun, {min, max},  as[1],cs[1], {1,- 1}, 1],
monotonicOuter[fun, {min, max},as[2], cs[1],  {1, -1}, 1]
    ],True&];
  
  outn := 
{};
  
  Which[
   0 <= x <= y || 0 <= y <= x, outp,
   x <= y <= 0 || y <= x <= 0, outn,
   x <= 0 && y >= 0, outn~Join~outp,
   y <= 0 && x >= 0, outp~Join~outn]]


(* ::Subsection:: *)
(*Main definition*)


(* ::Subsubsection::Closed:: *)
(*Options*)


(* ::Input::Initialization:: *)
ClearAll[TranscendentalRange]

Options[TranscendentalRange]={Method->Exp,"GeneratorsDomain"->Rationals,"FareyRange"->False,"FormulaComplexity"->Infinity,WorkingPrecision->MachinePrecision,"Test"->False(*developer only option*)};


(* ::Input::Initialization:: *)
ClearAll[optGenerators]
optGenerators[opts:OptionsPattern[TranscendentalRange]]:=
	Block[{plain},
		plain=Switch[OptionValue["GeneratorsDomain"],
						Rationals|{Rationals,Reals},
							"Rational",
						Algebraics|{Algebraics,Reals},
							"Algebraic"];
		If[!OptionValue["FareyRange"],
				plain,
				plain<>"Farey"]]
optGenerators[str_String]:=str


(* ::Subsubsection::Closed:: *)
(*Combined range*)


(* ::Input::Initialization:: *)
ClearAll[combineMethod]
combineMethod[funL_List,x_,y_,z_,d_,opts:OptionsPattern[TranscendentalRange]]:=
	With[{prec=OptionValue[WorkingPrecision]},SortBy[DeleteDuplicatesBy[Join@@Map[TranscendentalRange[x,y,z,d,Method->#,opts]&,funL],
N[#,prec]&],N[#,prec]&]]


(* ::Subsubsection::Closed:: *)
(*Semifinal range*)


ClearAll[transcendentalRange]

Options[transcendentalRange]=Options[TranscendentalRange];

transcendentalRange[{f_,i_},x_,y_,z_:1,opts:OptionsPattern[transcendentalRange]]:=

Block[{prec=OptionValue[WorkingPrecision],rg,rpl,sby,ddby},
		
		(*raw redundant range*)
		rg=coreRange[{f,i},x,y,z,optGenerators[opts]];
	
		(*delete duplicates by N + choose the one with minimal argument*)
		rpl=Switch[i,
					1,f[arg_]:>Abs@N[arg,prec],
					2,Times[a_, f[arg_]]|f[arg_]:>Abs@N[arg,prec]];
		ddby=Values@Map[
			First@MinimalBy[#,#/.rpl&,1]&,	
			
			GroupBy[rg,N[#,prec]&]];

		(*(rev)sort by N*)
		sby=If[z>0,SortBy,ReverseSortBy];
		sby[ddby,N[#,prec]&]]


(* ::Subsubsection::Closed:: *)
(*Final range*)


(* ::Input::Initialization:: *)
Clear[TranscendentalRange]

TranscendentalRange[x_,opts:OptionsPattern[TranscendentalRange]]:=
	Block[{optcompl,optalg,fullrange,restrcompl},

		If[!Element[{x},Algebraics],
			Return@failureNotAlgebraics[{x}]];

		optcompl=OptionValue["FormulaComplexity"];
		optalg=optGenerators[opts];

		fullrange=Which[

	MemberQ[Join[{Exp,Log,Power},$hyp,$invhyp,$invtrig],OptionValue[Method]]&&!OptionValue["Test"],
			transcendentalRange[{OptionValue[Method],2},1,x,1,opts],

	MemberQ[$trig,OptionValue[Method]]&&!OptionValue["Test"],
			sortNaiveRange[1,x,1,OptionValue[Method],
				"GeneratorsDomain"->optalg,WorkingPrecision->OptionValue[WorkingPrecision]],

	ListQ[OptionValue[Method]],
			combineMethod[OptionValue[Method],1,x,1,0,opts],
						
	OptionValue[Method]===All,
			combineMethod[$trsctypes,1,x,1,0,opts],
						
	MemberQ[$trsctypes,OptionValue[Method]]||OptionValue["Test"],
			sortNaiveRange[1,x,1,OptionValue[Method],
				"GeneratorsDomain"->optalg,WorkingPrecision->OptionValue[WorkingPrecision]],
						
	True,
			$Failed];

		restrcompl=If[optcompl<Infinity,
			complexitySelect[fullrange,optcompl],
			fullrange]]


TranscendentalRange[x_,y_,z_:1,d_:0,opts:OptionsPattern[TranscendentalRange]]/;NumericQ[d]&&NumericQ[z]:=
	Block[{optcompl,optalg,fullrange,restrcompl,restrstep},

		If[!Element[{x,y,z},Algebraics],
			Return@failureNotAlgebraics[{x,y,z}]];

		optcompl=OptionValue["FormulaComplexity"];
		optalg=optGenerators[opts];

		fullrange=Which[

	MemberQ[Join[{Exp,Log,Power},$hyp,$invhyp,$invtrig],OptionValue[Method]]&&!OptionValue["Test"],
			transcendentalRange[{OptionValue[Method],2},x,y,z,opts],
						
	MemberQ[$trig,OptionValue[Method]]&&!OptionValue["Test"],
			sortNaiveRange[x,y,z,OptionValue[Method],"GeneratorsDomain"->optalg],
						
	ListQ[OptionValue[Method]],
			combineMethod[OptionValue[Method],x,y,z,d,opts],
						
	OptionValue[Method]===All,
			combineMethod[$trsctypes,x,y,z,d,opts],
						
	MemberQ[$trsctypes,OptionValue[Method]]||OptionValue["Test"],
			sortNaiveRange[x,y,z,OptionValue[Method],
				"GeneratorsDomain"->optalg,WorkingPrecision->OptionValue[WorkingPrecision]],
						
	True,
			$Failed];

		restrcompl=If[optcompl<Infinity,
			complexitySelect[fullrange,optcompl],
			fullrange];

		restrstep=If[d>0,
			stepSelect[restrcompl,d],
			restrcompl]]


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
