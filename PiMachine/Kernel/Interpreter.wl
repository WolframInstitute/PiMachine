(* ::Package:: *)

BeginPackage["Wolfram`PiMachine`"];

ClearAll[
    PiState, PiStateQ,
    PiReduce,
    PiEval, PiEvalTrace
]

Begin["`Private`"];


(* State *)

(* PiState[combinator, term, continutation, enter/return, forward/backward] *)

PiStateQ[
    (HoldPattern[PiState[PiTerm[_, PiFunction[a_, b_], ___] ? PiTermQ, PiTerm[_, t_, ___] ? PiTermQ, PiTerm[_, PiContinuation[a_, b_], ___] ? PiTermQ, s_ ? BooleanQ, _ ? BooleanQ]] /;
        s && t === a || ! s && t === b
    ) |
    PiState[$Failed | _Failure | _Missing]
] := True
PiStateQ[___] := False

PiState[c_, v_] := PiState[c, v, Automatic]
PiState[c_, v_, k_] := PiState[c, v, k, True]
PiState[c_, v_, k_, s_] := PiState[c, v, k, s, True]
PiState[c : PiTerm[_, PiFunction[a_, b_], ___] ? PiTermQ, v_, Automatic, s_, d_] := PiState[c, v, PiTerm[PiHole, PiContinuation[a, b]], s, d]

PiState[c : PiTerm[_, ct : PiFunction[a_, b_], ___] ? PiTermQ, v : PiTerm[_, t_, ___] ? PiTermQ, k : PiTerm[_, PiContinuation[a_, b_], ___] ? PiTermQ, s_ ? BooleanQ, d_] /;
    Not[s && t === a || ! s && t === b] := Enclose @ With[{type = ct /. First @ Confirm @ unify[If[s, a, b], t]},
        ConfirmBy[PiState[PiTerm[c, type], v, PiTerm[k, PiContinuation @@ type], s, d], PiStateQ]
    ]


(* State update rules *)

(* rule 3 *)
PiReduce[PiState[PiTerm[RightComposition[c1__, c2_], __], v_, k_, True, True] ? PiStateQ] := PiState[PiTerm[RightComposition[c1]], v, PiTerm[PiFrame[PiHole /* PiTerm[c2], k]], True, True]
(* rule 4 and 5 *)
PiReduce[PiState[PiTerm[cs_CirclePlus, __], PiTerm[PiChoice[i_][x_], _PiPlus, ___] ? PiTermQ, k_, True, True] ? PiStateQ] := PiState[cs[[i]], x, PiTerm[PiFrame[ReplacePart[cs, i -> PiHole], k]], True, True]
(* rule 6 *)
PiReduce[PiState[PiTerm[{c1__, c2_ ? PiTermQ}, ___], PiTerm[{xs__, y_}, _PiTimes, ___] ? PiTermQ, k_, True, True] ? PiStateQ] := PiState[PiTerm[{c1}], PiTerm[{xs}], PiTerm[PiFrame[CircleTimes[PiHole, {c2, y}], k]], True, True]

(* rule 7 *)
PiReduce[PiState[c1_, v_, PiTerm[PiFrame[RightComposition[PiHole, c2__], k_], __], False, True] ? PiStateQ] := PiState[PiTerm[RightComposition[c2]], v, PiTerm[PiFrame[c1 /* PiHole, k]], True, True]
(* rule 8 *)
PiReduce[PiState[c1_, x_, PiTerm[PiFrame[CircleTimes[PiHole, {c2_, y_}], k_], __], False, True] ? PiStateQ] := PiState[c2, y, PiTerm[PiFrame[CircleTimes[{c1, x}, PiHole], k]], True, True]
(* rule 9 *)
PiReduce[PiState[c2_, y_, PiTerm[PiFrame[CircleTimes[{c1_, x_}, PiHole], k_], __], False, True] ? PiStateQ] := PiState[PiTerm[{c1, c2}, PiFunction @@ k["Type"]], PiTerm[{x, y}], k, False, True]
(* rule 10 *)
PiReduce[PiState[c2_, v_, PiTerm[PiFrame[c1_ /* PiHole, k_], __], False, True] ? PiStateQ] := PiState[PiTerm[c1 /* c2, PiFunction @@ k["Type"]], v, k, False, True]
(* rule 11 *)
PiReduce[PiState[c1_, x_, PiTerm[PiFrame[CirclePlus[PiHole, c2_], k_], __], False, True] ? PiStateQ] := PiState[PiTerm[CirclePlus[c1, c2], PiFunction @@ k["Type"]], PiTerm[PiChoice[1][x],  PiPlus[x["Type"], k["Type"][[2, 2]]]], k, False, True]
(* rule 12 *)
PiReduce[PiState[c2_, y_, PiTerm[PiFrame[CirclePlus[c1_, PiHole], k_], __], False, True] ? PiStateQ] := PiState[PiTerm[CirclePlus[c1, c2], PiFunction @@ k["Type"]], PiTerm[PiChoice[2][y], PiPlus[k["Type"][[2, 1]], y["Type"]]], k, False, True]

(* rule 13 *)
PiReduce[PiState[cap : PiTerm[_, PiFunction[PiPlus[PiMinus[a_], a_], PiZero], ___], PiTerm[PiChoice[2][v : PiTerm[_, b_, ___]], ___], k_, True, True] ? PiStateQ] /; MatchQ[b, a] :=
    PiState[cap, PiTerm[PiChoice[1][PiTerm[- v]], PiPlus[PiMinus[b], b]], k, True, False]
(* rule 14 *)
PiReduce[PiState[cap : PiTerm[_, PiFunction[PiPlus[PiMinus[a_], a_], PiZero], ___], PiTerm[PiChoice[1][v : PiTerm[_, PiMinus[b_], ___]], ___], k_, True, True] ? PiStateQ] /; MatchQ[b, a] :=
    PiState[cap, PiTerm[PiChoice[2][PiTerm[- v]], PiPlus[PiMinus[b], b]], k, True, False]

(* rule 15 *)
PiReduce[PiState[cup : PiTerm[_, PiFunction[PiZero, PiPlus[PiMinus[a_], a_]], ___], PiTerm[PiChoice[1][v : PiTerm[_, PiMinus[b_], ___]], ___], k_, False, False] ? PiStateQ] /; MatchQ[b, a] :=
    PiState[cup, PiTerm[PiChoice[2][PiTerm[- v]], PiPlus[PiMinus[b], b]], k, False, True]
(* rule 16 *)
PiReduce[PiState[cup : PiTerm[_, PiFunction[PiZero, PiPlus[PiMinus[a_], a_]], ___], PiTerm[PiChoice[2][v : PiTerm[_, b_, ___]], ___], k_, False, False] ? PiStateQ] /; MatchQ[b, a] :=
    PiState[cup, PiTerm[PiChoice[1][PiTerm[- v]], PiPlus[PiMinus[b], b]], k, False, True]

(* fractional rules *)
PiReduce[PiState[cup : PiTerm[_, PiFunction[PiUnit, PiTimes[PiInverse[v : PiTerm[_, a_, ___]], a_]], ___], PiTerm[PiOne, PiUnit, ___], k_, True, True] ? PiStateQ] := PiState[cup, PiTerm[{PiTerm[PiBottom, PiInverse[v]], v}], k, False, True]
PiReduce[PiState[cap : PiTerm[_, PiFunction[PiTimes[PiInverse[v : PiTerm[_, a_, ___]], a_], PiUnit], ___], PiTerm[{PiTerm[PiBottom, ___], v_}, PiTimes[_PiInverse, _], ___], k_, True, True] ? PiStateQ] := PiState[cap, PiTerm[PiOne], k, False, True]
PiReduce[PiState[cap : PiTerm[_, PiFunction[PiTimes[PiInverse[PiTerm[_, a_, ___]], a_], PiUnit], ___], PiTerm[{PiTerm[PiBottom, ___], _}, PiTimes[_PiInverse, _], ___], _, True, True] ? PiStateQ] := PiState[$Failed]

(* rule 1 and 2 *)
PiReduce[PiState[c_, v_, k_, True, True] ? PiStateQ] := PiState[c, c[v], k, False, True]


(* Reverse rules *)

(* rule 3 *)
PiReduce[PiState[c1_, v_, PiTerm[PiFrame[PiHole /* c2_, k_], __], True, False] ? PiStateQ] := PiState[PiTerm[RightComposition[c1, c2]], v, k, True, False]
(* rule 4 and 5 *)
PiReduce[PiState[c1_, x_, PiTerm[PiFrame[CirclePlus[c2___, PiHole, c3___], k_], __], True, False] ? PiStateQ] := PiState[PiTerm[CirclePlus[c2, c1, c3]], PiTerm[PiChoice[Length[{c2}] + 1][x], k["Type"][[1]]], k, True, False]
(* rule 6 *)
PiReduce[PiState[c1_, x_, PiTerm[PiFrame[CircleTimes[PiHole, {c2_, y_}], k_], __], True, False] ? PiStateQ] := PiState[PiTerm[{c1, c2}], PiTerm[{x, y}], k, True, False]
(* rule 7 *)
PiReduce[PiState[c2_, v_, PiTerm[PiFrame[c1_ /* PiHole, k_], __], True, False] ? PiStateQ] := PiState[c1, v, PiTerm[PiFrame[PiHole /* c2, k]], False, False]
(* rule 8 *)
PiReduce[PiState[c2_, y_, PiTerm[PiFrame[CircleTimes[{c1_, x_}, PiHole], k_], __], True, False] ? PiStateQ] := PiState[c1, x, PiTerm[PiFrame[CircleTimes[PiHole, {c2, y}], k]], False, False]
(* rule 9 *)
PiReduce[PiState[PiTerm[{c1_, c2__}, __], PiTerm[{x_, ys__}, __], k_, False, False] ? PiStateQ] := PiState[PiTerm[{c2}], PiTerm[{ys}], PiTerm[PiFrame[CircleTimes[{c1, x}, PiHole], k]], False, False]
(* rule 10 *)
PiReduce[PiState[PiTerm[RightComposition[c1_, c2__], __], v_, k_, False, False] ? PiStateQ] := PiState[PiTerm[RightComposition[c2]], v, PiTerm[PiFrame[PiTerm[c1] /* PiHole, k]], False, False]
(* rule 11 and 12 *)
PiReduce[PiState[PiTerm[cs_CirclePlus, __], PiTerm[PiChoice[i_][x_], _PiPlus, ___] ? PiTermQ, k_, False, False] ? PiStateQ] := PiState[cs[[i]], x, PiTerm[PiFrame[ReplacePart[cs, i -> PiHole], k]], False, False]

(* rule 13 *)
PiReduce[PiState[cap : PiTerm[_, PiFunction[PiPlus[PiMinus[a_], a_], PiZero], ___], PiTerm[PiChoice[1][v : PiTerm[_, PiMinus[b_], ___]], ___], k_, True, False] ? PiStateQ] /; MatchQ[b, a] :=
    PiState[cap, PiTerm[PiChoice[2][PiTerm[- v]], PiPlus[PiMinus[b], b]], k, True, True]
(* rule 14 *)
PiReduce[PiState[cap : PiTerm[_, PiFunction[PiPlus[PiMinus[a_], a_], PiZero], ___], PiTerm[PiChoice[2][v : PiTerm[_, b_, ___]], ___], k_, True, False] ? PiStateQ] /; MatchQ[b, a] :=
    PiState[cap, PiTerm[PiChoice[1][PiTerm[- v]], PiPlus[PiMinus[b], b]], k, True, True]

(* rule 15 *)
PiReduce[PiState[cup : PiTerm[_, PiFunction[PiZero, PiPlus[PiMinus[a_], a_]], ___], PiTerm[PiChoice[2][v : PiTerm[_, b_, ___]], ___], k_, False, True] ? PiStateQ] /; MatchQ[b, a] :=
    PiState[cup, PiTerm[PiChoice[1][PiTerm[- v]], PiPlus[PiMinus[b], b]], k, False, False]
(* rule 16 *)
PiReduce[PiState[cup : PiTerm[_, PiFunction[PiZero, PiPlus[PiMinus[a_], a_]], ___], PiTerm[PiChoice[1][v : PiTerm[_, PiMinus[b_], ___]], ___], k_, False, True] ? PiStateQ] /; MatchQ[b, a] :=
    PiState[cup, PiTerm[PiChoice[2][PiTerm[- v]], PiPlus[PiMinus[b], b]], k, False, False]

(* fractional rules *)
PiReduce[PiState[cup : PiTerm[_, PiFunction[PiUnit, PiTimes[PiInverse[v : PiTerm[_, a_, ___]], a_]], ___], PiTerm[{PiTerm[PiBottom, __], v_}, PiTimes[_PiInverse, _], ___], k_, False, False] ? PiStateQ] := PiState[cup, PiTerm[PiOne], k, True, False]
PiReduce[PiState[cup : PiTerm[_, PiFunction[PiUnit, PiTimes[PiInverse[v : PiTerm[_, a_, ___]], a_]], ___], PiTerm[{PiTerm[PiBottom, __], _}, PiTimes[_PiInverse, _], ___], k_, False, False] ? PiStateQ] := PiState[$Failed]
PiReduce[PiState[cap : PiTerm[_, PiFunction[PiTimes[PiInverse[v : PiTerm[_, a_, ___]], a_], PiUnit], ___], PiTerm[PiOne, ___], k_, False, False] ? PiStateQ] := PiState[cap, PiTerm[{PiTerm[PiBottom, PiInverse[v]], v}], k, True, False]


(* rule 1 and 2 *)
PiReduce[PiState[c_, v_, k_, False, False] ? PiStateQ] := PiState[c, PiCombinatorInverse[c][v], k, True, False]


(* Eval *)

PiEval[state_ ? PiStateQ] := NestWhile[PiReduce, state, PiStateQ, 1, Infinity, -1]

PiEvalTrace[state_ ? PiStateQ] := NestWhileList[PiReduce, state, PiStateQ, 1, Infinity, -1]

PiEval[c_, PiTerm[Right[x_], PiForward[t_], args___] ? PiTermQ, dir : _ ? BooleanQ : True] := Replace[
    PiEval[PiState[c, PiTerm[x, t, args], Automatic, dir, dir]],
    {
        PiState[_, w_, PiTerm[PiHole, ___], _, d_] :> PiTerm[If[d == dir, Right, Left][w]],
        PiState[$Failed] -> PiTerm[$Failed, PiError[c["Type"][[2]]]]
    }
]

PiEval[c_, PiTerm[Left[x_], PiBackward[t_], args___] ? PiTermQ, dir : _ ? BooleanQ : True] := Replace[
    PiEval[PiState[c, PiTerm[x, t, args], Automatic, ! dir, ! dir]],
    {
        PiState[_, w_, PiTerm[PiHole, ___], _, d_] :> PiTerm[If[d == dir, Right, Left][w]],
        PiState[$Failed] -> PiTerm[$Failed, PiError[c["Type"][[2]]]]
    }
]

PiEval[c_, term_ ? PiTermQ] := PiEval[c, PiTerm[Right[term], PiForward[term["Type"]]]]


(* Apply *)

PiTerm[comp_RightComposition, _PiFunction, ___][x_PiTerm ? PiTermQ] := comp[x]
PiTerm[choice_CirclePlus, _PiFunction, ___][PiTerm[PiChoice[i_][x_ ? PiTermQ], t_PiPlus, ___] ? PiTermQ] /; 1 <= i Length[choice] := With[{u = choice[[i]][x]}, PiTerm[PiChoice[i][u], ReplacePart[t, i -> u["Type"]]]]
PiTerm[fs : {__PiTerm}, _PiFunction, ___][PiTerm[xs : {__PiTerm ? PiTermQ}, _PiTimes, ___] ? PiTermQ] /; Length[fs] == Length[xs] := PiTerm[MapThread[Construct, {fs, xs}]]
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