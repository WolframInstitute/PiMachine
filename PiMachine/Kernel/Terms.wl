(* ::Package:: *)

BeginPackage["Wolfram`PiMachine`"];

ClearAll[
    PiTerm, PiTermQ
]

Begin["`Private`"];

term_PiTerm /; System`Private`HoldNotValidQ[term] && MatchQ[Unevaluated[term], HoldPattern[
	PiTerm["tt", PiUnit, ___] |
	(PiTerm["inj"[i_Integer][x_ ? PiTermQ], PiPlus[ts__] ? PiTypeQ, ___] /; 1 <= i <= Length[{ts}] && x["Type"] === {ts}[[i]]) |
	(PiTerm[CirclePlus[xs__ ? PiTermQ], t : HoldPattern @ PiFunction[PiPlus[ts__], PiPlus[us__]] ? PiTypeQ, ___] /; Length[{xs}] == Length[{ts}] == Length[{us}] && Comap[{xs}, "Type"] === MapThread[PiFunction, {{ts}, {us}}]) |
	
	(PiTerm[{xs__ ? PiTermQ}, PiTimes[ts__] ? PiTypeQ, ___] /; Length[{xs}] == Length[{ts}] && Comap[{xs}, "Type"] === {ts}) |
	(PiTerm[{xs__ ? PiTermQ}, t : HoldPattern @ PiFunction[PiTimes[ts__], PiTimes[us__]] ? PiTypeQ, ___] /; Length[{xs}] == Length[{ts}] == Length[{us}] && Comap[{xs}, "Type"] === MapThread[PiFunction, {{ts}, {us}}]) |
	
	PiTerm[_Rule | _RuleDelayed | {(_Rule | _RuleDelayed) ..}, _PiFunction ? PiTypeQ, ___] |
	(PiTerm[RightComposition[fs__ ? PiTermQ], PiFunction[a_, b_] ? PiTypeQ, ___] /;
		MatchQ[Comap[{fs}, "Type"],
			{PiFunction[Verbatim[a], c_], ts___PiFunction, PiFunction[d_, Verbatim[b]]} /;
				AllTrue[Partition[Append[d] @ Prepend[c] @ Catenate[List @@@ {ts}], 2], Apply[SameQ]]
		]) |

	PiTerm["\[Square]", _PiContinuation ? PiTypeQ, ___] |
	(PiTerm[PiFrame["\[Square]" /* c2_ ? PiTermQ, k_ ? PiTermQ], t_PiContinuation ? PiTypeQ, ___] /; k["Type"] === PiContinuation @@ (PiFunction @@ t) /* c2["Type"]) |
	(PiTerm[PiFrame[c1_ ? PiTermQ /* "\[Square]", k_ ? PiTermQ], t_PiContinuation ? PiTypeQ, ___] /; k["Type"] === PiContinuation @@ c1["Type"] /* (PiFunction @@ t)) |
	
	(PiTerm[PiFrame[c1_ ? PiTermQ \[CirclePlus] "\[Square]", k_ ? PiTermQ], t_PiContinuation ? PiTypeQ, ___] /; k["Type"] === PiContinuation @@ PiPlus[c1["Type"], PiFunction @@ t]) |
	(PiTerm[PiFrame["\[Square]" \[CirclePlus] c2_ ? PiTermQ, k_ ? PiTermQ], t_PiContinuation ? PiTypeQ, ___] /; k["Type"] === PiContinuation @@ PiPlus[PiFunction @@ t, c2["Type"]]) |
	
	(PiTerm[PiFrame[{c1_ ? PiTermQ, x_ ? PiTermQ} \[CircleTimes] "\[Square]", k_ ? PiTermQ], t_PiContinuation ? PiTypeQ, ___] /; MatchQ[c1["Type"], PiFunction[_, Verbatim[x["Type"]]]] && k["Type"] === PiContinuation @@ PiTimes[c1["Type"], PiFunction @@ t]) |
	(PiTerm[PiFrame["\[Square]" \[CircleTimes] {c2_ ? PiTermQ, y_ ? PiTermQ}, k_ ? PiTermQ], t_PiContinuation ? PiTypeQ, ___] /; MatchQ[c2["Type"], PiFunction[Verbatim[y["Type"]], _]] && k["Type"] === PiContinuation @@ PiTimes[PiFunction @@ t, c2["Type"]]) |
	
	PiTerm[Minus[_ ? PiTermQ], PiMinus] | 
	PiTerm["↻", __]
	
]] := (System`Private`HoldSetValid[term]; System`Private`HoldSetNoEntry[term]; term)

PiTermQ[term_PiTerm] := System`Private`ValidQ[term]
PiTermQ[___] := False

HoldPattern[PiTerm[term_, ___] ? PiTermQ]["Term"] := term
HoldPattern[PiTerm[_, type_, ___] ? PiTermQ]["Type"] := type
HoldPattern[PiTerm[_, _, args___] ? PiTermQ]["Arguments"] := {args}

PiTerm["tt"] := PiTerm["tt", PiUnit]
PiTerm[xs_List] := Enclose @ With[{terms = ConfirmBy[PiTerm[#], PiTermQ] & /@ xs},
	PiTerm[If[Length[xs] == 1, First, Identity] @ MapThread[PiTerm, {terms, List @@ Replace[#, HoldPattern @ PiFunction[PiTimes[as__], PiTimes[bs__]] :> MapThread[PiFunction, {{as}, {bs}}]]}], #] & @ ConfirmBy[PiTimes @@ Comap[terms, "Type"], PiTypeQ]
]
PiTerm[xs_CirclePlus] := Enclose @ With[{terms = ConfirmBy[PiTerm[#], PiTermQ] & /@ List @@ xs},
	PiTerm[If[Length[xs] == 1, First, Identity][CirclePlus @@ MapThread[PiTerm, {terms, List @@ Replace[#, HoldPattern @ PiFunction[PiPlus[as__], PiPlus[bs__]] :> MapThread[PiFunction, {{as}, {bs}}]]}]], #] & @ ConfirmBy[PiPlus @@ Comap[terms, "Type"], PiTypeQ]
]
PiTerm["inj"[i_Integer][x_] /; ! PiTermQ[x], type : HoldPattern[PiPlus[ts__]] ? PiTypeQ] /; 1 <= i <= Length[{ts}] :=
	Enclose @ PiTerm["inj"[i][ConfirmBy[PiTerm[x, {ts}[[i]]], PiTermQ]], type]
PiTerm["inj"[i_Integer][x_]] := Enclose @ With[{term = PiTerm[x]}, PiTerm["inj"[i][term], ConfirmBy[PiPlus @@ ReplacePart[ConstantArray[PiZero, Max[i, 2]], i -> term["Type"]], PiTypeQ]]]

PiTerm[term : HoldPattern[RightComposition[fs__ ? PiTermQ]]] := With[{types = UnifyFunctionTypes @ (List @@@ Comap[{fs}, "Type"])},
	PiTerm[
		RightComposition @@ MapThread[PiTerm[#1, #2, Sequence @@ #3] &, {Comap[{fs}, "Term"], PiFunction @@@ types, Comap[{fs}, "Arguments"]}],
		PiFunction[types[[1, 1]], types[[-1, 2]]]
	] /; MatchQ[types, {{_, _} ..}] && AllTrue[Partition[Most @ Rest @ Catenate[types], 2], Apply[SameQ]]
]

PiTerm[HoldPattern @ PiFrame["\[Square]" /* PiTerm[c2_, PiFunction[a_, b_], args1___] ? PiTermQ, PiTerm[k_, PiContinuation[c_, d_], args2___] ? PiTermQ]] :=
	Enclose[PiTerm[PiFrame["\[Square]" /* PiTerm[c2, PiFunction[a /. #, b /. #], args1], PiTerm[k, PiContinuation[c /. #, d /. #], args2]], PiContinuation[c, a]] & @ Confirm[ResourceFunction["MostGeneralUnifier"][b, d]]]
PiTerm[HoldPattern @ PiFrame[PiTerm[c1_, PiFunction[a_, b_], args1___] ? PiTermQ /* "\[Square]", PiTerm[k_, PiContinuation[c_, d_], args2___] ? PiTermQ]] :=
	Enclose[PiTerm[PiFrame[PiTerm[c1, PiFunction[a /. #, b /. #], args1] /* "\[Square]", PiTerm[k, PiContinuation[c /. #, d /. #], args2]], PiContinuation[b, d]] & @ Confirm[ResourceFunction["MostGeneralUnifier"][a, c]]]

PiTerm[frame : HoldPattern @ PiFrame[CirclePlus[PiTerm[_, PiFunction[a_, b_], ___] ? PiTermQ, "\[Square]"], PiTerm[_, PiContinuation[PiPlus[a_, c__], PiPlus[b_, d__]], ___] ? PiTermQ]] :=
	PiTerm[frame, PiContinuation[PiPlus[c], PiPlus[d]]]
PiTerm[frame : HoldPattern @ PiFrame[CirclePlus["\[Square]", PiTerm[_, PiFunction[a_, b_], ___] ? PiTermQ], PiTerm[_, PiContinuation[PiPlus[c__, a_], PiPlus[d__, b_]], ___] ? PiTermQ]] :=
	PiTerm[frame, PiContinuation[PiPlus[c], PiPlus[d]]]

PiTerm[frame : HoldPattern @ PiFrame[CircleTimes[{PiTerm[_, PiFunction[a_, b_], ___] ? PiTermQ, PiTerm[_, b_, ___] ? PiTermQ}, "\[Square]"], PiTerm[_, PiContinuation[PiTimes[a_, c__], PiTimes[b_, d__]], ___] ? PiTermQ]] :=
	PiTerm[frame, PiContinuation[PiTimes[c], PiTimes[d]]]
PiTerm[frame : HoldPattern @ PiFrame[CircleTimes["\[Square]", {PiTerm[_, PiFunction[a_, b_], ___] ? PiTermQ, PiTerm[_, a_, ___] ? PiTermQ}], PiTerm[_, PiContinuation[PiTimes[c__, a_], PiTimes[d__, b_]], ___] ? PiTermQ]] :=
	PiTerm[frame, PiContinuation[PiTimes[c], PiTimes[d]]]

PiTerm[term_PiTerm ? PiTermQ] := term
PiTerm[term_PiTerm ? PiTermQ, type_ ? PiTypeQ] := Enclose[
	PiTerm[term["Term"] /. First @ Confirm[unify[term["Type"], type]], type, ##] & @@ term["Arguments"]
]
PiTerm[term_PiTerm ? PiTermQ, type_ ? PiTypeQ, args__] := PiTerm[PiTerm[term["Term"], type]["Term"], type, args]

PiTerm[comp_RightComposition, _PiFunction, ___][x_PiTerm ? PiTermQ] := comp[x]
PiTerm[rules_, PiFunction[a_, b_], ___][x_PiTerm ? PiTermQ] := Enclose @ ConfirmBy[Replace[ConfirmBy[x, MatchQ[#["Type"], a] &], rules], MatchQ[#["Type"], b] &]


(* Formatting *)

PiTerm /: MakeBoxes[term_PiTerm ? PiTermQ, form_] :=
	InterpretationBox[#, term] & @ TooltipBox[
		ToBoxes[
			If[MatchQ[term["Type"], _PiFunction | _PiContinuation], Style[#, Bold] &, Framed] @
				Replace[term["Arguments"], {{label_, ___} :> label, {} :> Replace[term["Term"], {
					"tt" -> Style["tt", Bold],
					"inj"[i_][t_] :> Style[Subscript["inj", i], Bold][t],
					PiFrame[x_, y_] :> Row[Replace[{x, y}, t : Except[PiTerm["\[Square]", __]] :> Row[{"(", Replace[t, RightComposition[a_, b_] :> Row[{a, ";", b}]], ")"}], 1], "\[FilledSmallCircle]"]
				}]}],
			form
		],
		ToBoxes[term["Type"], TraditionalForm]
	]

End[];

EndPackage[]; 