(* ::Package:: *)

BeginPackage["Wolfram`PiMachine`"];

ClearAll[
    PiState, PiStateQ, PiRun
]

Begin["`Private`"];


(* State *)

PiStateQ[
    HoldPattern[PiState[PiTerm[_, PiFunction[a_, b_], ___] ? PiTermQ, _ ? PiTermQ, PiTerm[_, PiContinuation[a_, b_], ___] ? PiTermQ, _ ? BooleanQ, _ ? BooleanQ]] |
    PiState[$Failed | _Failure | _Missing]
] := True
PiStateQ[___] := False

PiState[c_, v_] := PiState[c, v, Automatic]
PiState[c_, v_, k_] := PiState[c, v, k, True]
PiState[c_, v_, k_, t_] := PiState[c, v, k, t, True]
PiState[c : PiTerm[_, PiFunction[a_, b_], ___] ? PiTermQ, v_, Automatic, t_, d_] := PiState[c, v, PiTerm[PiHole, PiContinuation[a, b]], t, d]


(* State run *)

PiRun[PiState[PiTerm[RightComposition[c1__, c2_], __], v_, k_, True, dir_] ? PiStateQ] := PiState[PiTerm[RightComposition[c1]], v, PiTerm[PiFrame[PiHole /* c2, k]], True, dir]
PiRun[PiState[PiTerm[cs_CirclePlus, __], PiTerm[PiChoice[i_][x_], _PiPlus, ___] ? PiTermQ, k_, True, dir_] ? PiStateQ] := PiState[PiTerm[cs[[i]]], x, PiTerm[PiFrame[ReplacePart[cs, i -> PiHole], k]], True, dir]
PiRun[PiState[PiTerm[{c1__, c2_}, __], PiTerm[{xs__, y_}, _PiTimes, ___] ? PiTermQ, k_, True, dir_] ? PiStateQ] := PiState[PiTerm[{c1}], PiTerm[{xs}], PiTerm[PiFrame[CircleTimes[PiHole, {c2, y}], k]], True, dir]
PiRun[PiState[PiTerm[c1_, __], v_, PiTerm[PiFrame[RightComposition[PiHole, c2__], k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[RightComposition[c2]], v, PiTerm[PiFrame[c1 /* PiHole, k]], True, dir]
PiRun[PiState[PiTerm[c1_, __], x_, PiTerm[PiFrame[CircleTimes[PiHole, {c2_, y_}], k_], __], False, dir_] ? PiStateQ] := PiState[c2, y, PiTerm[PiFrame[CircleTimes[{c1, x}, PiHole], k]], True, dir]
PiRun[PiState[PiTerm[c2_, __], y_, PiTerm[PiFrame[CircleTimes[{c1_, x_}, PiHole], k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[{c1, c2}], PiTerm[{x, y}], k, False, dir]
PiRun[PiState[PiTerm[c2_, __], v_, PiTerm[PiFrame[c1_ /* PiHole, k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[c1 /* c2], v, k, False, dir]
PiRun[PiState[PiTerm[c1_, __], x_, PiTerm[PiFrame[CirclePlus[PiHole, c2_], k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[CirclePlus[c1, c2]], PiTerm[PiChoice[1][x]], k, False, dir]
PiRun[PiState[PiTerm[c2_, __], y_, PiTerm[PiFrame[CirclePlus[c1_, PiHole], k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[CirclePlus[c1, c2]], PiTerm[PiChoice[2][y]], k, False, dir]


PiRun[PiState[cap : PiTerm[_, PiFunction[PiPlus[a_, PiMinus[a_]], PiZero], ___], PiTerm[PiChoice[1][v : PiTerm[_, b_, ___]], ___], k_, True, True] ? PiStateQ] /; MatchQ[b, a] :=
    PiState[cap, PiTerm[PiChoice[2][- v]], k, True, False]
PiRun[PiState[cap : PiTerm[_, PiFunction[PiPlus[a_, PiMinus[a_]], PiZero], ___], PiTerm[PiChoice[2][v : PiTerm[_, PiMinus[b_], ___]], ___], k_, True, True] ? PiStateQ] /; MatchQ[b, a] :=
    PiState[cap, PiTerm[PiChoice[1][- v]], k, True, False]

PiRun[PiState[cup : PiTerm[_, PiFunction[PiZero, PiPlus[a_, PiMinus[a_]]], ___], PiTerm[PiChoice[1][v : PiTerm[_, b_, ___]], ___], k_, False, False] ? PiStateQ] /; MatchQ[b, a] :=
    PiState[cup, PiTerm[PiChoice[2][- v]], k, False, True]
PiRun[PiState[cup : PiTerm[_, PiFunction[PiZero, PiPlus[a_, PiMinus[a_]]], ___], PiTerm[PiChoice[2][v : PiTerm[_, PiMinus[b_], ___]], ___], k_, False, False] ? PiStateQ] /; MatchQ[b, a] :=
    PiState[cup, PiTerm[PiChoice[1][- v]], k, False, True]


PiRun[PiState[c_, v_, k_, True, dir_] ? PiStateQ] := PiState[c, c[v], k, False, dir]


(* Eval *)

(* Forward *)

PiEval[c : PiTerm[_, a_, ___] ? PiTermQ, v : PiTerm[_, a_, ___] ? PiTermQ, True] :=
    Replace[PiRun[PiState[c, v, Automatic, True, True]], {PiState[_, w_, _, False, True] ? PiStateQ :> w, _ -> $Failed}]

(* Backward *)

PiEval[c_, v_, False]


(* Apply *)

PiTerm[comp_RightComposition, _PiFunction, ___][x_PiTerm ? PiTermQ] := comp[x]
PiTerm[rules_, PiFunction[a_, b_], ___][x_PiTerm ? PiTermQ] := Enclose @ ConfirmBy[Replace[ConfirmBy[x, MatchQ[#["Type"], a] &], rules], MatchQ[#["Type"], b] &]


(* Formatting *)

PiState /: MakeBoxes[PiState[c_, v_, k_, t_, d_] ? PiStateQ, form_] :=
    InterpretationBox[#, PiState[c, v, k, t, d]] & @ SubscriptBox[
        RowBox[If[t, {"\[LeftAngleBracket]", ##, "\[RightAngleBracket]"}, {"[", ##, "]"}] & @@ (Riffle[MakeBoxes[#, form] & /@ {c, v, k}, "|"])],
        If[d, "\[RightTriangle]", "\[LeftTriangle]"]
    ]

PiState /: MakeBoxes[PiState[f_ ? FailureQ] ? PiStateQ, _] :=
    InterpretationBox["⊠", PiState[f]]


End[];

EndPackage[]; 