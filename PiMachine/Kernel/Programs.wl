(* ::Package:: *)

BeginPackage["Wolfram`PiMachine`"];

ClearAll[
    PiBool, PiTrue, PiFalse,
    PiNot, PiCNot, PiIf, PiToffoli,
    PiCopy,
    PiZigZag,
    PiPlusTrace, PiTimesTrace
]

Begin["`Private`"];


id = PiCombinator["Identity"]

zeroi = PiCombinator["ZeroIntroduction"] 
zeroe = PiCombinator["ZeroElimination"]
swap = PiCombinator["PlusSwap"]
assocl = PiCombinator["PlusLeftAssociation"]
assocr = PiCombinator["PlusRightAssociation"]

uniti = PiCombinator["UnitIntroduction"]
unite = PiCombinator["UnitElimination"]
swapt = PiCombinator["TimesSwap"]
assoclt = PiCombinator["TimesLeftAssociation"]
assocrt = PiCombinator["TimesRightAssociation"]

dist = PiCombinator["Distribution"]
fact = PiCombinator["Factorization"]

eta = PiCombinator["PlusCup"]
eps = PiCombinator["PlusCap"]



PiBool[0] := PiUnit
PiBool[1] := PiPlus[PiUnit, PiUnit]
PiBool[n_Integer] := PiTimes @@ Table[PiBool[1], n]

BoolId[n_Integer ? NonNegative] := PiTerm[id, PiFunction[PiBool[n], PiBool[n]]]

PiFalse = PiTerm[PiChoice[1][PiOne], PiBool[1]]
PiTrue = PiTerm[PiChoice[2][PiOne], PiBool[1]]

PiNot = PiTerm[swap, PiFunction[PiBool[1], PiBool[1]], "not"]

PiCNot = PiTerm[
    PiTerm[
        dist /* PiTerm[CirclePlus[id, PiTerm[{id, swap}]]] /* fact],
        PiFunction[PiBool[2], PiBool[2]
    ],
    "cnot"
]

PiIf[c1_, c2_] := PiTerm[dist /* PiTerm[CirclePlus[PiTerm[{BoolId[0], c1}], PiTerm[{BoolId[0], c2}]]] /* fact]

PiToffoli[0] := BoolId[0]
PiToffoli[1] := PiTerm[swap, PiFunction[PiBool[1], PiBool[1]]]
PiToffoli[n_Integer ? Positive] := PiIf[id, PiToffoli[n - 1]]

PiCopy[0] := boolId
PiCopy[1] := PiTerm[PiTerm[swapt /* PiCNot /* swapt], PiFunction[PiBool[2], PiBool[2]]]
PiCopy[n_Integer ? Positive] := PiTerm[assoclt /* PiTerm[{PiCopy[n - 1], id}] /* assocrt]


PiZigZag = PiTerm[zeroi /* PiTerm[CirclePlus[eta, id]] /* assocr /* PiTerm[CirclePlus[id, swap]] /* assocl /* PiTerm[CirclePlus[eps, id]] /* zeroe]


PiPlusTrace[f_] := PiTerm[zeroi /* PiTerm[CirclePlus[eta, id]] /* assocr /* PiTerm[CirclePlus[id, f]] /* assocl /* PiTerm[CirclePlus[eps, id]] /* zeroe]

PiTimesTrace[v_, f_] := PiTerm[uniti /* PiTerm[{PiCombinator["TimesCup"[v]], id}] /* assocrt /* PiTerm[{id, f}] /* assoclt /* PiTerm[{PiCombinator["TimesCap"[v]], id}] /* unite]


End[];

EndPackage[]; 