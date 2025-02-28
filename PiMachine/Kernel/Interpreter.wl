(* ::Package:: *)

BeginPackage["Wolfram`PiMachine`"];

ClearAll[
    PiState, PiStateQ, PiEval
]

Begin["`Private`"];

PiStateQ[HoldPattern[PiState[PiTerm[_, PiFunction[a_, b_], ___] ? PiTermQ, _ ? PiTermQ, PiTerm[_, PiContinuation[a_, b_], ___] ? PiTermQ, _ ? BooleanQ, _ ? BooleanQ]]] := True
PiStateQ[___] := False

PiState[c_, v_, k_] := PiState[c, v, k, True, True]
PiState[c_, v_, k_, t_] := PiState[c, v, k, t, True]



PiEval[PiState[PiTerm[RightComposition[c1__, c2_], __], v_, k_, True, dir_] ? PiStateQ] := PiState[PiTerm[RightComposition[c1]], v, PiTerm[PiFrame[PiHole /* c2, k]], True, dir]
PiEval[PiState[PiTerm[cs_CirclePlus, __], PiTerm[PiChoice[i_][x_], _PiPlus, ___] ? PiTermQ, k_, True, dir_] ? PiStateQ] := PiState[PiTerm[cs[[i]]], x, PiTerm[PiFrame[ReplacePart[cs, i -> PiHole], k]], True, dir]
PiEval[PiState[PiTerm[{c1__, c2_}, __], PiTerm[{xs__, y_}, _PiTimes, ___] ? PiTermQ, k_, True, dir_] ? PiStateQ] := PiState[PiTerm[{c1}], PiTerm[{xs}], PiTerm[PiFrame[CircleTimes[PiHole, {c2, y}], k]], True, dir]
PiEval[PiState[PiTerm[c1_, __], v_, PiTerm[PiFrame[RightComposition[PiHole, c2__], k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[RightComposition[c2]], v, PiTerm[PiFrame[c1 /* PiHole, k]], True, dir]
PiEval[PiState[PiTerm[c1_, __], x_, PiTerm[PiFrame[CircleTimes[PiHole, {c2_, y_}], k_], __], False, dir_] ? PiStateQ] := PiState[c2, y, PiTerm[PiFrame[CircleTimes[{c1, x}, PiHole], k]], True, dir]
PiEval[PiState[PiTerm[c2_, __], y_, PiTerm[PiFrame[CircleTimes[{c1_, x_}, PiHole], k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[{c1, c2}], PiTerm[{x, y}], k, False, dir]
PiEval[PiState[PiTerm[c2_, __], v_, PiTerm[PiFrame[c1_ /* PiHole, k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[c1 /* c2], v, k, False, dir]
PiEval[PiState[PiTerm[c1_, __], x_, PiTerm[PiFrame[CirclePlus[PiHole, c2_], k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[CirclePlus[c1, c2]], PiTerm[PiChoice[1][x]], k, False, dir]
PiEval[PiState[PiTerm[c2_, __], y_, PiTerm[PiFrame[CirclePlus[c1_, PiHole], k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[CirclePlus[c1, c2]], PiTerm[PiChoice[2][y]], k, False, dir]

PiEval[PiState[cup : PiTerm[_, PyFunction[PiZero, PiSum[a_, PiMinu[a_]]], ___], PiTerm[PiChoice[1][v_], ___], k_, True, True] ? PiStateQ] := PiState[cup, PiTerm[PiChoice[2][-v]], k, False, dir]

PiEval[PiState[c_, v_, k_, True, dir_] ? PiStateQ] := PiState[c, c[v], k, False, dir]


(* Formatting *)

PiState /: MakeBoxes[PiState[c_, v_, k_, t_, d_] ? PiStateQ, form_] :=
    InterpretationBox[#, PiState[c, v, k, t, d]] & @ SubscriptBox[RowBox[If[t, {"\[LeftAngleBracket]", ##, "\[RightAngleBracket]"}, {"[", ##, "]"}] & @@ (Riffle[MakeBoxes[#, form] & /@ {c, v, k}, "|"])], If[d, "\[Rule]", "\[LeftArrow]"]]


End[];

EndPackage[]; 