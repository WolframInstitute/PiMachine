(* ::Package:: *)

BeginPackage["Wolfram`PiMachine`"];

ClearAll[
    PiTerm, PiTermQ,
	PiOne, PiChoice, PiHole, PiFrame, PiBottom
]

Begin["`Private`"];


term_PiTerm /; System`Private`HoldNotValidQ[term] && MatchQ[Unevaluated[term], HoldPattern[
	PiTerm[PiOne, PiUnit, ___] |
	(PiTerm[PiChoice[i_Integer][x_ ? PiTermQ], PiPlus[ts__] ? PiTypeQ, ___] /; 1 <= i <= Length[{ts}] && x["Type"] === {ts}[[i]]) |
	(PiTerm[CirclePlus[xs__ ? PiTermQ], t : HoldPattern @ PiFunction[PiPlus[ts__], PiPlus[us__]] ? PiTypeQ, ___] /; Length[{xs}] == Length[{ts}] == Length[{us}] && Comap[{xs}, "Type"] === MapThread[PiFunction, {{ts}, {us}}]) |
	
	(PiTerm[{xs__ ? PiTermQ}, PiTimes[ts__] ? PiTypeQ, ___] /; Length[{xs}] == Length[{ts}] && Comap[{xs}, "Type"] === {ts}) |
	(PiTerm[{xs__ ? PiTermQ}, t : HoldPattern @ PiFunction[PiTimes[ts__], PiTimes[us__]] ? PiTypeQ, ___] /; Length[{xs}] == Length[{ts}] == Length[{us}] && Comap[{xs}, "Type"] === MapThread[PiFunction, {{ts}, {us}}]) |
	
	PiTerm[_Rule | _RuleDelayed | {(_Rule | _RuleDelayed) ...}, _PiFunction ? PiTypeQ, ___] |
	(PiTerm[RightComposition[fs__ ? PiTermQ], PiFunction[a_, b_] ? PiTypeQ, ___] /;
		MatchQ[Comap[{fs}, "Type"],
			{PiFunction[Verbatim[a], c_], ts___PiFunction, PiFunction[d_, Verbatim[b]]} /;
				AllTrue[Partition[Append[d] @ Prepend[c] @ Catenate[List @@@ {ts}], 2], Apply[SameQ]]
		]) |

	PiTerm[PiHole, _PiContinuation ? PiTypeQ, ___] |
	(PiTerm[PiFrame[PiHole /* c2_ ? PiTermQ, k_ ? PiTermQ], t_PiContinuation ? PiTypeQ, ___] /; MatchQ[k["Type"], PiContinuation @@ (PiFunction @@ t) /* c2["Type"]]) |
	(PiTerm[PiFrame[c1_ ? PiTermQ /* PiHole, k_ ? PiTermQ], t_PiContinuation ? PiTypeQ, ___] /; MatchQ[k["Type"], PiContinuation @@ c1["Type"] /* (PiFunction @@ t)]) |
	
	(PiTerm[PiFrame[CirclePlus[c1_ ? PiTermQ, PiHole], k_ ? PiTermQ], t_PiContinuation ? PiTypeQ, ___] /; MatchQ[k["Type"], PiContinuation @@ PiPlus[c1["Type"], PiFunction @@ t]]) |
	(PiTerm[PiFrame[CirclePlus[PiHole, c2_ ? PiTermQ], k_ ? PiTermQ], t_PiContinuation ? PiTypeQ, ___] /; MatchQ[k["Type"], PiContinuation @@ PiPlus[PiFunction @@ t, c2["Type"]]]) |
	
	(PiTerm[PiFrame[CircleTimes[{c1_ ? PiTermQ, x_ ? PiTermQ}, PiHole], k_ ? PiTermQ], t_PiContinuation ? PiTypeQ, ___] /; MatchQ[c1["Type"], PiFunction[_, Verbatim[x["Type"]]]] && k["Type"] === PiContinuation @@ PiTimes[c1["Type"], PiFunction @@ t]) |
	(PiTerm[PiFrame[CircleTimes[PiHole, {c2_ ? PiTermQ, y_ ? PiTermQ}], k_ ? PiTermQ], t_PiContinuation ? PiTypeQ, ___] /; MatchQ[c2["Type"], PiFunction[Verbatim[y["Type"]], _]] && k["Type"] === PiContinuation @@ PiTimes[PiFunction @@ t, c2["Type"]]) |
	
	PiTerm[- PiTerm[_, a_, ___], PiMinus[a_] ? PiTypeQ, ___] | 
	PiTerm[Right[PiTerm[_, a_, ___] ? PiTermQ], PiForward[a_] ? PiTypeQ, ___] |
	PiTerm[Left[PiTerm[_, a_, ___] ? PiTermQ], PiBackward[a_] ? PiTypeQ, ___] |
	PiTerm[PiBottom, _PiInverse ? PiTypeQ, ___]
	
]] := (System`Private`HoldSetValid[term]; System`Private`HoldSetNoEntry[term]; term)

PiTermQ[term_PiTerm] := System`Private`ValidQ[term]
PiTermQ[___] := False

HoldPattern[PiTerm[term_, ___] ? PiTermQ]["Term"] := term
HoldPattern[PiTerm[_, type_, ___] ? PiTermQ]["Type"] := type
HoldPattern[PiTerm[_, _, args___] ? PiTermQ]["Arguments"] := {args}

PiTerm[PiOne] := PiTerm[PiOne, PiUnit]
PiTerm[xs_List] := Enclose @ With[{terms = ConfirmBy[PiTerm[#], PiTermQ] & /@ xs},
	PiTerm[If[Length[xs] == 1, PiTerm[First[terms], #], MapThread[PiTerm, {terms, List @@ Replace[#, HoldPattern @ PiFunction[PiTimes[as__], PiTimes[bs__]] :> MapThread[PiFunction, {{as}, {bs}}]]}]], #] & @ ConfirmBy[PiTimes @@ Comap[terms, "Type"], PiTypeQ]
]
PiTerm[xs_CirclePlus] := Enclose @ With[{terms = ConfirmBy[PiTerm[#], PiTermQ] & /@ List @@ xs},
	PiTerm[If[Length[xs] == 1, PiTerm[First[terms], #], CirclePlus @@ MapThread[PiTerm, {terms, List @@ Replace[#, HoldPattern @ PiFunction[PiPlus[as__], PiPlus[bs__]] :> MapThread[PiFunction, {{as}, {bs}}]]}]], #] & @ ConfirmBy[PiPlus @@ Comap[terms, "Type"], PiTypeQ]
]
PiTerm[PiChoice[i_Integer][x_] /; ! PiTermQ[x], type : HoldPattern[PiPlus[ts__]] ? PiTypeQ, args___] /; 1 <= i <= Length[{ts}] :=
	Enclose @ PiTerm[PiChoice[i][ConfirmBy[PiTerm[x, {ts}[[i]]], PiTermQ]], type, args]
PiTerm[PiChoice[i_Integer][x_]] := Enclose @ With[{term = PiTerm[x]}, PiTerm[PiChoice[i][term], ConfirmBy[PiPlus @@ ReplacePart[ConstantArray[PiZero, Max[i, 2]], i -> term["Type"]], PiTypeQ]]]

PiTerm[HoldPattern[RightComposition[fs__ ? PiTermQ]]] := With[{types = UnifyFunctionTypes @ (List @@@ Comap[{fs}, "Type"])},
	PiTerm[
		RightComposition @@ MapThread[PiTerm[#1, #2, Sequence @@ #3] &, {{fs}, PiFunction @@@ types, Comap[{fs}, "Arguments"]}],
		PiFunction[types[[1, 1]], types[[-1, 2]]]
	] /; MatchQ[types, {{_, _} ..}] && AllTrue[Partition[Most @ Rest @ Catenate[types], 2], Apply[SameQ]]
]

PiTerm[HoldPattern @ PiFrame[PiHole /* PiTerm[c2_, PiFunction[a_, b_], args1___] ? PiTermQ, PiTerm[k_, PiContinuation[c_, d_], args2___] ? PiTermQ]] :=
	Enclose[PiTerm[PiFrame[PiHole /* PiTerm[c2, PiFunction[a /. #, b /. #], args1], PiTerm[k, PiContinuation[c /. #, d /. #], args2]], PiContinuation[c, a]] & @ Confirm[MostGeneralUnifier[b, d]]]
PiTerm[HoldPattern @ PiFrame[PiTerm[c1_, PiFunction[a_, b_], args1___] ? PiTermQ /* PiHole, PiTerm[k_, PiContinuation[c_, d_], args2___] ? PiTermQ]] :=
	Enclose[PiTerm[PiFrame[PiTerm[c1, PiFunction[a /. #, b /. #], args1] /* PiHole, PiTerm[k, PiContinuation[c /. #, d /. #], args2]], PiContinuation[b, d]] & @ Confirm[MostGeneralUnifier[a, c]]]

PiTerm[frame : HoldPattern @ PiFrame[CirclePlus[PiTerm[_, PiFunction[a_, b_], ___] ? PiTermQ, PiHole], PiTerm[_, PiContinuation[PiPlus[a_, c__], PiPlus[b_, d__]], ___] ? PiTermQ]] :=
	PiTerm[frame, PiContinuation[PiPlus[c], PiPlus[d]]]
PiTerm[frame : HoldPattern @ PiFrame[CirclePlus[PiHole, PiTerm[_, PiFunction[a_, b_], ___] ? PiTermQ], PiTerm[_, PiContinuation[PiPlus[c__, a_], PiPlus[d__, b_]], ___] ? PiTermQ]] :=
	PiTerm[frame, PiContinuation[PiPlus[c], PiPlus[d]]]

PiTerm[frame : HoldPattern @ PiFrame[CircleTimes[{PiTerm[_, PiFunction[a_, b_], ___] ? PiTermQ, PiTerm[_, b_, ___] ? PiTermQ}, PiHole], PiTerm[_, PiContinuation[PiTimes[a_, c__], PiTimes[b_, d__]], ___] ? PiTermQ]] :=
	PiTerm[frame, PiContinuation[PiTimes[c], PiTimes[d]]]
PiTerm[frame : HoldPattern @ PiFrame[CircleTimes[PiHole, {PiTerm[_, PiFunction[a_, b_], ___] ? PiTermQ, PiTerm[_, a_, ___] ? PiTermQ}], PiTerm[_, PiContinuation[PiTimes[c__, a_], PiTimes[d__, b_]], ___] ? PiTermQ]] :=
	PiTerm[frame, PiContinuation[PiTimes[c], PiTimes[d]]]

PiTerm[- x_ /; ! PiTermQ[x], type : HoldPattern[PiMinus[a_]] ? PiTypeQ] := With[{term = PiTerm[x]}, PiTerm[- term, type] /; term["Type"] === a]
PiTerm[- x_] := With[{term = PiTerm[x]}, PiTerm[- term, PiMinus[term["Type"]]]]
PiTerm[- (PiTerm[- x_, PiMinus[a_], ___] ? PiTermQ)] := PiTerm[x, a]

PiTerm[Right[x_]] := With[{term = PiTerm[x]}, PiTerm[Right[term], PiForward[term["Type"]]]]
PiTerm[Left[x_]] := With[{term = PiTerm[x]}, PiTerm[Left[term], PiBackward[term["Type"]]]]


PiTerm[term_PiTerm ? PiTermQ] := term
PiTerm[term_PiTerm ? PiTermQ, type_ ? PiTypeQ] := Enclose[
	PiTerm[TypeSubstitute[term["Term"], First @ Confirm[unify[term["Type"], type]]], type, ##] & @@ term["Arguments"]
]
PiTerm[term_PiTerm ? PiTermQ, type_ ? PiTypeQ, args__] := PiTerm[PiTerm[term, type]["Term"], type, args]


(* Term equality *)

PiTerm /: Equal[ts__PiTerm] := Equal @@ Through[{ts}["Term"]] && Equal @@ Through[{ts}["Type"]]


(* Formatting *)

Format[PiOne] = "1"
Format[PiChoice] = "inj"
Format[PiHole] = "\[Square]"
Format[PiBottom] = "\[Perpendicular]"

PiTerm /: MakeBoxes[term_PiTerm ? PiTermQ, form_] :=
	InterpretationBox[#, term] & @ TooltipBox[
		If[MatchQ[term["Type"], _PiFunction | _PiContinuation], StyleBox[#, Bold] &, FrameBox[#, FrameMargins -> Tiny] &] @
			Replace[term["Arguments"], {{label_, ___} :> ToBoxes[label, form], {} :> Replace[term["Term"], {
				PiOne -> ToBoxes[Style[PiOne, Bold], form],
				PiChoice[i : 1 | 2][_] /; term["Type"] === PiPlus[PiUnit, PiUnit] :> Switch[i, 1, "\[DoubleStruckCapitalF]", 2, "\[DoubleStruckCapitalT]"],
				PiChoice[i_][t_] :> ToBoxes[Superscript[t, i], form],
				HoldPattern[RightComposition[xs__]] :> ToBoxes[Row[{xs}, ";"], form],
				(* TODO: Parenthesize properly *)
				PiFrame[x_, y_] :> RowBox[Riffle[Replace[{x, y}, {t : Except[PiTerm[PiHole, __]] :> With[{expr = Replace[t, RightComposition[a_, b_] :> Row[{"(", a, ";", b, ")"}]]}, Parenthesize[expr, form, Times]], t_ :> ToBoxes[t, form]}, 1], "\[FilledSmallCircle]"]],
				Right[x_] :> ToBoxes[Subscript[x, "\[RightTriangle]"], form],
				Left[x_] :> ToBoxes[Subscript[x, "\[LeftTriangle]"], form],
				x_ :> ToBoxes[x, form]
			}]}
		],
		ToBoxes[term["Type"], TraditionalForm]
	]

End[];

EndPackage[]; 