(* ::Package:: *)

BeginPackage["Wolfram`PiMachine`"];

ClearAll[
    PiTerm, HoldPiTermQ, PiTermQ,
	PiOne, PiChoice, PiHole, PiFrame, PiBottom
]

Begin["`Private`"];


piTermQ[term_PiTerm] := MatchQ[Unevaluated[term], HoldPattern[
	PiTerm[PiOne, PiUnit, ___] |
	(PiTerm[PiChoice[i_Integer][x_ ? HoldPiTermQ], PiPlus[ts__] ? HoldPiTypeQ, ___] /; 1 <= i <= Length[{ts}] && x["Type"] === {ts}[[i]]) |
	(PiTerm[CirclePlus[xs__ ? HoldPiTermQ], t : HoldPattern @ PiFunction[PiPlus[ts__], PiPlus[us__]] ? HoldPiTypeQ, ___] /; Length[{xs}] == Length[{ts}] == Length[{us}] && Comap[{xs}, "Type"] === MapThread[PiFunction, {{ts}, {us}}]) |
	
	(PiTerm[CircleTimes[xs__ ? HoldPiTermQ], PiTimes[ts__] ? HoldPiTypeQ, ___] /; Length[{xs}] == Length[{ts}] && Comap[{xs}, "Type"] === {ts}) |
	(PiTerm[CircleTimes[xs__ ? HoldPiTermQ], t : HoldPattern @ PiFunction[PiTimes[ts__], PiTimes[us__]] ? HoldPiTypeQ, ___] /; Length[{xs}] == Length[{ts}] == Length[{us}] && Comap[{xs}, "Type"] === MapThread[PiFunction, {{ts}, {us}}]) |
	
	PiTerm[_Rule | _RuleDelayed | {(_Rule | _RuleDelayed) ...}, _PiFunction ? HoldPiTypeQ, ___] |
	(PiTerm[CircleDot[fs__ ? HoldPiTermQ], PiFunction[a_, b_] ? HoldPiTypeQ, ___] /;
		MatchQ[Comap[{fs}, "Type"],
			{PiFunction[Verbatim[a], c_], ts___PiFunction, PiFunction[d_, Verbatim[b]]} /;
				AllTrue[Partition[Append[d] @ Prepend[c] @ Catenate[List @@@ {ts}], 2], Apply[SameQ]]
		]) |

	PiTerm[PiHole, _PiContinuation ? HoldPiTypeQ, ___] |
	(PiTerm[PiFrame[CircleDot[PiHole, c2_ ? HoldPiTermQ], k_ ? HoldPiTermQ], t_PiContinuation ? HoldPiTypeQ, ___] /; MatchQ[k["Type"], PiContinuation @@ (PiFunction @@ t) /* c2["Type"]]) |
	(PiTerm[PiFrame[CircleDot[c1_ ? HoldPiTermQ, PiHole], k_ ? HoldPiTermQ], t_PiContinuation ? HoldPiTypeQ, ___] /; MatchQ[k["Type"], PiContinuation @@ c1["Type"] /* (PiFunction @@ t)]) |
	
	(PiTerm[PiFrame[CirclePlus[c1_ ? HoldPiTermQ, PiHole], k_ ? HoldPiTermQ], t_PiContinuation ? HoldPiTypeQ, ___] /; MatchQ[k["Type"], PiContinuation @@ PiPlus[c1["Type"], PiFunction @@ t]]) |
	(PiTerm[PiFrame[CirclePlus[PiHole, c2_ ? HoldPiTermQ], k_ ? HoldPiTermQ], t_PiContinuation ? HoldPiTypeQ, ___] /; MatchQ[k["Type"], PiContinuation @@ PiPlus[PiFunction @@ t, c2["Type"]]]) |
	
	(PiTerm[PiFrame[CircleTimes[{c1_ ? HoldPiTermQ, x_ ? HoldPiTermQ}, PiHole], k_ ? HoldPiTermQ], t_PiContinuation ? HoldPiTypeQ, ___] /; MatchQ[c1["Type"], PiFunction[_, Verbatim[x["Type"]]]] && k["Type"] === PiContinuation @@ PiTimes[c1["Type"], PiFunction @@ t]) |
	(PiTerm[PiFrame[CircleTimes[PiHole, {c2_ ? HoldPiTermQ, y_ ? HoldPiTermQ}], k_ ? HoldPiTermQ], t_PiContinuation ? HoldPiTypeQ, ___] /; MatchQ[c2["Type"], PiFunction[Verbatim[y["Type"]], _]] && k["Type"] === PiContinuation @@ PiTimes[PiFunction @@ t, c2["Type"]]) |
	
	PiTerm[- PiTerm[_, a_, ___], PiMinus[a_] ? HoldPiTypeQ, ___] | 
	PiTerm[Right[PiTerm[_, a_, ___] ? HoldPiTermQ], PiForward[a_] ? HoldPiTypeQ, ___] |
	PiTerm[Left[PiTerm[_, a_, ___] ? HoldPiTermQ], PiBackward[a_] ? HoldPiTypeQ, ___] |
	PiTerm[PiBottom, _PiInverse ? PiTypeQ, ___] |
	PiTerm[_ ? (HoldFunction[FailureQ]), _PiError ? HoldPiTypeQ | PiZero, ___]
]]
piTermQ[___] := False

PiTermQ[term_PiTerm] := System`Private`HoldValidQ[term] || piTermQ[Unevaluated[term]]
PiTermQ[___] := False

HoldPiTermQ = HoldFunction[PiTermQ]

term_PiTerm /; System`Private`HoldNotValidQ[term] && piTermQ[Unevaluated[term]] := (System`Private`HoldSetValid[term]; System`Private`HoldSetNoEntry[term])


HoldPattern[PiTerm[term_, ___] ? PiTermQ]["Term"] := term
HoldPattern[PiTerm[_, type_, ___] ? PiTermQ]["Type"] := type
HoldPattern[PiTerm[_, _, args___] ? PiTermQ]["Arguments"] := {args}

PiTerm[PiOne] := PiTerm[PiOne, PiUnit]
PiTerm[xs : _List | _CircleTimes] := Enclose @ With[{terms = ConfirmBy[PiTerm[#], PiTermQ] & /@ List @@ xs},
	PiTerm[Switch[Length[xs], 0, PiOne, 1, PiTerm[First[terms], #], _, CircleTimes @@ MapThread[PiTerm, {terms, List @@ Replace[#, HoldPattern @ PiFunction[PiTimes[as__], PiTimes[bs__]] :> MapThread[PiFunction, {{as}, {bs}}]]}]], #] & @ ConfirmBy[PiTimes @@ Comap[terms, "Type"], PiTypeQ]
]
PiTerm[xs_List, type_PiTimes, args___] := PiTerm[CircleTimes @@ xs, type, args]

PiTerm[xs_CirclePlus] := Enclose @ With[{terms = ConfirmBy[PiTerm[#], PiTermQ] & /@ List @@ xs},
	PiTerm[Switch[Length[xs], 0, $Failed, 1, PiTerm[First[terms], #], _, CirclePlus @@ MapThread[PiTerm, {terms, List @@ Replace[#, HoldPattern @ PiFunction[PiPlus[as__], PiPlus[bs__]] :> MapThread[PiFunction, {{as}, {bs}}]]}]], #] & @ ConfirmBy[PiPlus @@ Comap[terms, "Type"], PiTypeQ]
]
PiTerm[PiChoice[i_Integer][x_] /; ! PiTermQ[x], type : HoldPattern[PiPlus[ts__]] ? PiTypeQ, args___] /; 1 <= i <= Length[{ts}] :=
	Enclose @ PiTerm[PiChoice[i][ConfirmBy[PiTerm[x, {ts}[[i]]], PiTermQ]], type, args]
PiTerm[PiChoice[i_Integer][x_]] := Enclose @ With[{term = PiTerm[x]}, PiTerm[PiChoice[i][term], ConfirmBy[PiPlus @@ ReplacePart[ConstantArray[PiZero, Max[i, 2]], i -> term["Type"]], PiTypeQ]]]

PiTerm[CircleDot[t_ ? PiTermQ]] := t

PiTerm[(CircleDot | RightComposition)[fs__ ? PiTermQ]] := With[{types = UnifyFunctionTypes @ (List @@@ Comap[{fs}, "Type"])},
	PiTerm[
		CircleDot @@ MapThread[PiTerm[#1, #2, Sequence @@ #3] &, {{fs}, PiFunction @@@ types, Comap[{fs}, "Arguments"]}],
		PiFunction[types[[1, 1]], types[[-1, 2]]]
	] /; MatchQ[types, {{_, _} ..}] && AllTrue[Partition[Most @ Rest @ Catenate[types], 2], Apply[SameQ]]
]

PiTerm[HoldPattern @ PiFrame[CircleDot[PiHole, PiTerm[c2_, PiFunction[a_, b_], args1___] ? PiTermQ], PiTerm[k_, PiContinuation[c_, d_], args2___] ? PiTermQ]] :=
	Enclose[PiTerm[PiFrame[CircleDot[PiHole, PiTerm[c2, PiFunction[a /. #, b /. #], args1]], PiTerm[k, PiContinuation[c /. #, d /. #], args2]], PiContinuation[c, a]] & @ Confirm[MostGeneralUnifier[b, d]]]
PiTerm[HoldPattern @ PiFrame[CircleDot[PiTerm[c1_, PiFunction[a_, b_], args1___] ? PiTermQ, PiHole], PiTerm[k_, PiContinuation[c_, d_], args2___] ? PiTermQ]] :=
	Enclose[PiTerm[PiFrame[CircleDot[PiTerm[c1, PiFunction[a /. #, b /. #], args1], PiHole], PiTerm[k, PiContinuation[c /. #, d /. #], args2]], PiContinuation[b, d]] & @ Confirm[MostGeneralUnifier[a, c]]]

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
PiTerm[term_PiTerm ? PiTermQ, Automatic, args___] := PiTerm[term["Term"], term["Type"], args]

PiTerm[term_PiTerm ? PiTermQ ^ n_Integer] := Which[n == 0, PiTerm[PiUnit], n > 0, PiTerm[ConstantArray[term, n]], True, PiTerm[ConstantArray[PiBottom, - n], ConstantArray[PiInverse[term], - n]]]


(* Term equality *)

PiTerm /: Equal[ts__PiTerm] := Equal @@ Through[{ts}["Term"]] && Equal @@ Through[{ts}["Type"]]


(* Formatting *)

Format[PiOne] = "1"
Format[PiChoice] = "inj"
Format[PiHole] = "\[Square]"
Format[PiBottom] = "\[Perpendicular]"

PiTerm /: MakeBoxes[term_PiTerm ? HoldPiTermQ, form_] :=
	InterpretationBox[#, term] & @ TooltipBox[
		If[MatchQ[term["Type"], _PiFunction | _PiContinuation], StyleBox[#, Bold] &, FrameBox[#, FrameMargins -> Tiny] &] @
			Replace[term["Arguments"], {{label_, ___} :> ToBoxes[label, form], {} :> Replace[term["Term"], {
				PiOne -> ToBoxes[Style[PiOne, Bold], form],
				PiChoice[i : 1 | 2][_] /; term["Type"] === PiPlus[PiUnit, PiUnit] :> Switch[i, 1, "\[DoubleStruckCapitalF]", 2, "\[DoubleStruckCapitalT]"],
				PiChoice[i_][t_] :> ToBoxes[Superscript[t, i], form],
				HoldPattern[CircleDot[xs__]] :> ToBoxes[Row[{"(", Row[{xs}, ";"], ")"}], form],
				(* TODO: Parenthesize properly *)
				PiFrame[x_, y_] :> RowBox[{"(", ##, ")"} & @@ Riffle[Replace[{x, y}, {t : Except[PiTerm[PiHole, __]] :> With[{expr = Replace[t, CircleDot[a_, b_] :> Row[{"(", a, ";", b, ")"}]]}, Parenthesize[expr, form, Times]], t_ :> ToBoxes[t, form]}, 1], "\[FilledSmallCircle]"]],
				Right[x_] :> ToBoxes[Subscript[x, "\[RightTriangle]"], form],
				Left[x_] :> ToBoxes[Subscript[x, "\[LeftTriangle]"], form],
				_ ? FailureQ :> "error",
				x_ :> ToBoxes[x, form]
			}]}
		],
		ToBoxes[term["Type"], TraditionalForm]
	]

End[];

EndPackage[]; 