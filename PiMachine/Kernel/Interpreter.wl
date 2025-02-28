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



PiEval[PiState[PiTerm[RightComposition[c1__, c2_], __], v_, k_, True, dir_] ? PiStateQ] := PiState[PiTerm[RightComposition[c1]], v, PiTerm[PiFrame["\[Square]" /* c2, k]], True, dir]
PiEval[PiState[PiTerm[cs_CirclePlus, __], PiTerm["inj"[i_][x_], _PiPlus, ___] ? PiTermQ, k_, True, dir_] ? PiStateQ] := PiState[PiTerm[cs[[i]]], x, PiTerm[PiFrame[ReplacePart[cs, i -> "\[Square]"], k]], True, dir]
PiEval[PiState[PiTerm[{c1__, c2_}, __], PiTerm[{xs__, y_}, _PiTimes, ___] ? PiTermQ, k_, True, dir_] ? PiStateQ] := PiState[PiTerm[{c1}], PiTerm[{xs}], PiTerm[PiFrame[CircleTimes["\[Square]", {c2, y}], k]], True, dir]
PiEval[PiState[PiTerm[c1_, __], v_, PiTerm[PiFrame[RightComposition["\[Square]", c2__], k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[RightComposition[c2]], v, PiTerm[PiFrame[c1 /* "\[Square]", k]], True, dir]
PiEval[PiState[PiTerm[c1_, __], x_, PiTerm[PiFrame[CircleTimes["\[Square]", {c2_, y_}], k_], __], False, dir_] ? PiStateQ] := PiState[c2, y, PiTerm[PiFrame[CircleTimes[{c1, x}, "\[Square]"], k]], True, dir]
PiEval[PiState[PiTerm[c2_, __], y_, PiTerm[PiFrame[CircleTimes[{c1_, x_}, "\[Square]"], k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[{c1, c2}], PiTerm[{x, y}], k, False, dir]
PiEval[PiState[PiTerm[c2_, __], v_, PiTerm[PiFrame[c1_ /* "\[Square]", k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[c1 /* c2], v, k, False, dir]
PiEval[PiState[PiTerm[c1_, __], x_, PiTerm[PiFrame[CirclePlus["\[Square]", c2_], k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[CirclePlus[c1, c2]], PiTerm["inj"[1][x]], k, False, dir]
PiEval[PiState[PiTerm[c2_, __], y_, PiTerm[PiFrame[CirclePlus[c1_, "\[Square]"], k_], __], False, dir_] ? PiStateQ] := PiState[PiTerm[CirclePlus[c1, c2]], PiTerm["inj"[2][y]], k, False, dir]
PiEval[PiState[c_, v_, k_, True, dir_] ? PiStateQ] := PiState[c, c[v], k, False, dir]


(* Formatting *)

PiState /: MakeBoxes[PiState[c_, v_, k_, t_, d_] ? PiStateQ, form_] :=
    InterpretationBox[#, PiState[c, v, k, t, d]] & @ SubscriptBox[RowBox[If[t, {"\[LeftAngleBracket]", ##, "\[RightAngleBracket]"}, {"[", ##, "]"}] & @@ (Riffle[MakeBoxes[#, form] & /@ {c, v, k}, "|"])], If[d, "\[Rule]", "\[LeftArrow]"]]


End[];

EndPackage[]; 