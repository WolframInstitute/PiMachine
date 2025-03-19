(* ::Package:: *)

BeginPackage["`Programs`", "WolframInstitute`PiMachine`"];

bool = PiPlus[PiUnit, PiUnit]
false = PiTerm[PiChoice[1][PiOne], bool]
true = PiTerm[PiChoice[2][PiOne], bool]

id = PiCombinator["Identity"]

zeroi = PiCombinator["ZeroIntroduction"] 
zeroe = PiCombinator["ZeroElimination"]
swap = PiCombinator["PlusSwap"]
assocl = PiCombinator["PlusLeftAssociation"]
assocr = PiCombinator["PlusRightAssociation"]

absorbz = PiCombinator["ZeroAbsorb"]
factorz = PiCombinator["ZeroFactor"]

uniti = PiCombinator["UnitIntroduction"]
unite = PiCombinator["UnitElimination"]
swapt = PiCombinator["TimesSwap"]
assoclt = PiCombinator["TimesLeftAssociation"]
assocrt = PiCombinator["TimesRightAssociation"]

dist = PiCombinator["Distribution"]
factor = PiCombinator["Factorization"]

eta = PiCombinator["PlusCup"]
eps = PiCombinator["PlusCap"]

etat[v_] := PiCombinator["TimesCup"[v]]
epst[v_] := PiCombinator["TimesCap"[v]]

zeroer = PiTerm[swap /* zeroe]

zeroir = PiTerm[zeroi /* swap]

uniter = PiTerm[swapt /* unite]

unitir = PiTerm[uniti /* swapt]

absorbzr = PiTerm[swapt /* absorbz]

factorzr = PiTerm[factorz /* swapt]

distl = PiTerm[swapt /* dist /* PiTerm[CirclePlus[swapt, swapt]]]

factorl = PiTerm[PiTerm[CirclePlus[swapt, swapt]] /* factor /* swapt]

etar = PiTerm[eta /* swap]
epsr = PiTerm[swap /* eps]

inv = PiCombinatorInverse

EndPackage[];

BeginPackage["WolframInstitute`PiMachine`", "WolframInstitute`PiMachine`Programs`"];

ClearAll[
    PiBool, PiTrue, PiFalse, PiBoolId,
    PiNot, PiCNot, PiIf, PiToffoli, PiToffoli0,
    PiFalseTuple, PiBoolTerms,
    PiCopy, PiReset,
    PiRotateLeft, PiRotateRight,
    PiIncrement,
    PiZigZag,
    PiPlusTrace, PiPlusTraceRight, PiTimesTrace, PiTimesTraceRight,
    PiLoop,
    PiAnd, PiNand, PiNor, PiOr, PiXor,
    PiMerge, PiSplit, PiFNot, PiSAT
]

Begin["`Private`"];


PiBool[0] := PiUnit
PiBool[1] := bool
PiBool[n_Integer] := PiTimes[bool, PiBool[n - 1]]

PiBoolId[n_Integer ? NonNegative] := PiTerm[id, PiFunction[PiBool[n], PiBool[n]]]

PiFalse = false
PiTrue = true

PiNot = PiTerm[swap, PiFunction[PiBool[1], PiBool[1]]]

PiCNot = PiTerm[
    PiTerm[
        dist /* PiTerm[CirclePlus[id, PiTerm[{id, swap}]]] /* factor],
        PiFunction[PiBool[2], PiBool[2]
    ],
    "cnot"
]

PiIf[c1_, c2_] := PiTerm[dist /* PiTerm[CirclePlus[PiTerm[{PiBoolId[0], c1}], PiTerm[{PiBoolId[0], c2}]]] /* factor]

PiToffoli[0] := PiBoolId[0]
PiToffoli[1] := PiTerm[swap, PiFunction[PiBool[1], PiBool[1]]]
PiToffoli[n_Integer ? Positive] := PiIf[id, PiToffoli[n - 1]]

PiToffoli0[0] := PiBoolId[0]
PiToffoli0[1] := PiTerm[swap, PiFunction[PiBool[1], PiBool[1]]]
PiToffoli0[n_Integer ? Positive] := PiIf[PiToffoli0[n - 1], id]

PiFalseTuple[n_Integer] := PiTerm @ ReplaceRepeated[ConstantArray[PiFalse, n], xs_List /; Length[xs] > 2 :> TakeDrop[xs, 1]]

PiBoolTerms[n_Integer] := PiTerm @* ReplaceRepeated[xs_List /; Length[xs] > 2 :> TakeDrop[xs, 1]] /@ Tuples[{PiTrue, PiFalse}, n]

PiCopy[0] := PiBoolId[0]
PiCopy[1] := PiTerm[PiTerm[swapt /* PiCNot /* swapt], PiFunction[PiBool[2], PiBool[2]]]
PiCopy[n_Integer ? Positive] := PiTerm[assoclt /* PiTerm[{PiCopy[1], PiBoolId[n - 1]}] /* assocrt]


swapl = PiTerm[assocl /* PiTerm[CirclePlus[swap, id]] /* assocr]
swapr = PiTerm[assocr /* PiTerm[CirclePlus[id, swap]] /* assocl]
swaplt = PiTerm[assoclt /* PiTerm[{swapt, id}] /* assocrt]
swaprt = PiTerm[assocrt /* PiTerm[{id, swapt}] /* assoclt]


PiReset[0] := PiBoolId[1]
PiReset[1] := PiTerm[swapt /* PiCNot /* swapt]
PiReset[n_Integer ? Positive] := PiTerm[swaplt /* PiIf[PiReset[n - 1], PiTerm[{swap, id}]] /* swaplt]


PiRotateLeft[0] := PiBoolId[0]
PiRotateLeft[1] := PiBoolId[1]
PiRotateLeft[2] := PiTerm[swapt, PiFunction[PiBool[2], PiBool[2]]]
PiRotateLeft[n_Integer ? Positive] := PiTerm[swaplt /* PiTerm[{PiBoolId[1], PiRotateLeft[n - 1]}]]

PiRotateRight[n_] := PiCombinatorInverse[PiRotateLeft[n]]


PiIncrement[0] := PiBoolId[0]
PiIncrement[1] := PiTerm[swap, PiFunction[PiBool[1], PiBool[1]]]
PiIncrement[n_Integer ? Positive] := PiTerm[PiTerm[{id, PiIncrement[n - 1]}] /* PiRotateLeft[n] /* PiToffoli0[n] /* PiRotateRight[n]]


PiPlusTrace[f_] := PiTerm[zeroi /* PiTerm[CirclePlus[eta, id]] /* assocr /* PiTerm[CirclePlus[id, f]] /* assocl /* PiTerm[CirclePlus[eps, id]] /* zeroe]

PiPlusTraceRight[f_] := PiTerm[zeroir /* PiTerm[CirclePlus[id, etar]] /* assocl /* PiTerm[CirclePlus[f, id]] /* assocr /* PiTerm[CirclePlus[id, epsr]] /* zeroer]

PiTimesTrace[v_, f_] := PiTerm[uniti /* PiTerm[{PiCombinator["TimesCup"[v]], id}] /* assocrt /* PiTerm[{id, f}] /* assoclt /* PiTerm[{PiCombinator["TimesCap"[v]], id}] /* unite]

PiTimesTraceRight[v_, f_] := PiTerm[unitir /* PiTerm[{id, PiTerm[PiCombinator["TimesCup"[v]] /* swapt]}] /* assoclt /* PiTerm[{f, id}] /* assocrt /* PiTerm[{id, PiTerm[swapt /* PiCombinator["TimesCap"[v]]]}] /* uniter]

PiZigZag = PiPlusTrace[swap]


PiLoop[0, _] := PiBoolId[0]
PiLoop[1, f_] := PiTerm[{PiBoolId[1], f}]
PiLoop[n_Integer ? Positive, f_] :=
    PiTerm[PiPlusTraceRight[PiTerm[
        PiTerm[CirclePlus[dist, id]] /* swapr /* PiTerm[CirclePlus[factor, id]] /*
        PiTerm[CirclePlus[PiTerm[PiReset[n] /* PiTerm[{id, f}] /* PiCopy[n] /* PiTerm[{id, PiCombinatorInverse[f]}]], id]] /*
        PiTerm[CirclePlus[dist, id]] /* swapr /* PiTerm[CirclePlus[factor, PiTerm[{id, PiIncrement[n]}]]]
    ]], PiFunction[PiBool[n + 1], PiBool[n + 1]], "loop"]



PiAnd = PiTerm[PiRotateLeft[3] /* dist /* PiTerm[CirclePlus[id, PiTerm[{id, PiTerm[dist /* PiTerm[CirclePlus[id, PiTerm[{id, swap}]]] /* factor]}]]] /* factor /* PiRotateRight[3]]

PiNand = PiTerm[PiAnd /* PiTerm[{PiNot, id}]]

PiOr = PiTerm[PiRotateLeft[3] /* dist /* PiTerm[CirclePlus[PiTerm[{id, PiTerm[dist /* PiTerm[CirclePlus[id, PiTerm[{id, swap}]]] /* factor]}], PiTerm[{id, PiTerm[{id, swap}]}]]] /* factor /* PiRotateRight[3]]

PiNor = PiTerm[PiOr /* PiTerm[{PiNot, id}]]

PiXor = PiTerm[PiTerm[distl /* PiTerm[CirclePlus[id, PiTerm[{swap, id}]]] /* factorl], PiFunction[PiBool[2], PiBool[2]]]


PiMerge[0, m_] := PiTerm[unite, PiFunction[PiTimes[PiUnit, PiBool[m]], PiBool[m]]]
PiMerge[1, 0] := PiTerm[uniter, PiFunction[PiTimes[PiBool[1], PiUnit], PiBool[1]]]
(* PiMerge[1, 1] := PiTerm[id, PiFunction[PiBool[2], PiBool[2]]] *)
PiMerge[1, m_] := PiTerm[id, PiFunction[PiTimes[PiBool[1], PiBool[m]], PiBool[m + 1]]]
PiMerge[n_, m_] := PiTerm[assocrt /* {id, PiMerge[n - 1, m]}]

PiSplit[n_, m_] := PiCombinatorInverse[PiMerge[n, m]]

PiFNot[f : PiTerm[_, PiFunction[PiBool[1], PiBool[1]], ___] ? PiTermQ] := f
PiFNot[f : PiTerm[_, PiFunction[a_PiTimes, a_PiTimes], ___] ? PiTermQ] := PiTerm[f /* {PiNot, id}]

PiSAT[f : PiTerm[_, PiFunction[a_, a_], ___] ? PiTermQ] := Enclose @ With[{n = ConfirmBy[Log2[PiCardinality[a]], IntegerQ] - 1},
    PiTimesTraceRight[
        PiFalseTuple[n + 3],
        PiTerm[
            {PiBoolId[0], {id, PiLoop[n + 1, PiFNot[f]] /* {id, PiSplit[1, n]}} /*
                 {id, assoclt /* {PiCopy[n - 1], id} /* assocrt} /*
                 assoclt /* {swapt, id} /* assocrt /*
                 {id, {id, PiMerge[1, n]} /* PiCombinatorInverse[PiLoop[n + 1, PiFNot[f]]]}
            }
        ]
    ]
]

End[];

EndPackage[];


BeginPackage["`SAT`", {"WolframInstitute`PiMachine`", "WolframInstitute`PiMachine`Programs`"}];

(* Ex₁(𝔽,a,b) = ((a∧b) xor (a∧b),_,_) *)

Ex1 = PiTimesTraceRight[PiFalse, PiTerm[
    swapt /*
    {id, PiAnd} /* assoclt /* {swapt, id} /* assocrt /*
    {id, PiAnd} /* assoclt /* {PiXor, id} /* assocrt /*
    {id, inv[PiAnd]} /* assoclt /* {swapt, id} /* assocrt /*
    swapt
]]

(* Ex₂(𝔽,a,b) = ((a∧b) xor (a∨b),_,_) *)

Ex2 = PiTimesTraceRight[PiFalse, PiTerm[
    swapt /*
    {id, PiAnd} /* assoclt /* {swapt, id} /* assocrt /*
    {id, PiOr} /* assoclt /* {PiXor, id} /* assocrt /*
    {id, inv[PiOr]} /* assoclt /* {swapt, id} /* assocrt /*
    swapt
]]


(* Ex₃(𝔽,a,b) = (((a∧b) ∧ (a xor b)),_,_) *)

Ex3 = With[{F = PiTerm[PiAnd /* {id, PiXor}]},
    PiTimesTraceRight[PiFalse, PiTerm[
        swapt /*
        assoclt /* {swapt, id} /* assocrt /*
        {id, F} /*
        {id, assoclt} /* assoclt /*
        {PiAnd, id} /*
        assocrt /* {id, assocrt} /* 
        {id, inv[F]} /*
        assoclt /* {swapt, id} /* assocrt /*
        swapt
    ]]
]

(* Ex₄(𝔽,a,b) = (((a∨b) ∧ (a xor b)),_,_) *)

Ex4 = With[{F = PiTerm[PiOr /* {id, PiXor}]},
    PiTimesTraceRight[PiFalse, PiTerm[
        swapt /*
        assoclt /* {swapt, id} /* assocrt /*
        {id, F} /*
        {id, assoclt} /* assoclt /*
        {PiAnd, id} /*
        assocrt /* {id, assocrt} /*
        {id, inv[F]} /*
        assoclt /* {swapt, id} /* assocrt /*
        swapt
    ]]
]

EndPackage[];

