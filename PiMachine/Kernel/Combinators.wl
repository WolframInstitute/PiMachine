(* ::Package:: *)

BeginPackage["Wolfram`PiMachine`"];

ClearAll[
    PiCombinator
]

Begin["`Private`"];


PiCombinator["Identity"] := PiTerm[x_ :> x, PiFunction[\[FormalCapitalA]_, \[FormalCapitalA]_], "id\[TwoWayRule]"]
PiCombinator["ZeroElimination"] := PiTerm[HoldPattern[PiTerm["inj"[2][x_], PiPlus[PiZero, _], ___]] :> x, PiFunction[PiPlus[PiZero, \[FormalCapitalA]_], \[FormalCapitalA]_], "\!\(\*SubscriptBox[\(unite\), \(+\)]\)l"]
PiCombinator["ZeroIntroduction"] := PiTerm[x_ ? PiTermQ :> PiTerm["inj"[2][x], PiPlus[PiZero, x["Type"]]], PiFunction[\[FormalCapitalA]_, PiPlus[PiZero, \[FormalCapitalA]_]], "\!\(\*SubscriptBox[\(uniti\), \(+\)]\)l"]
PiCombinator["PlusSwap"] := PiTerm[HoldPattern[PiTerm["inj"[1][x_], PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], ___]] :> PiTerm["inj"[2][x], PiPlus[B, A]], PiFunction[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], PiPlus[\[FormalCapitalB]_, \[FormalCapitalA]_]], "\!\(\*SubscriptBox[\(swap\), \(+\)]\)"]
PiCombinator["PlusLeftAssociation"] := PiTerm[{
	HoldPattern[PiTerm["inj"[1][x_], PiPlus[\[FormalCapitalA]_, PiPlus[\[FormalCapitalB]_, \[FormalCapitalC]_]], ___]] :> PiTerm["inj"[1][PiTerm["inj"[1][x]]], PiPlus[PiPlus[A, B], C]],
	HoldPattern[PiTerm["inj"[2][PiTerm["inj"[1][x_], _]], PiPlus[\[FormalCapitalA]_, PiPlus[\[FormalCapitalB]_, \[FormalCapitalC]_]], ___]] :> PiTerm["inj"[1][PiTerm["inj"[2][x]]], PiPlus[PiPlus[A, B], C]],
	HoldPattern[PiTerm["inj"[2][PiTerm["inj"[2][x_], _]], PiPlus[\[FormalCapitalA]_, PiPlus[\[FormalCapitalB]_, \[FormalCapitalC]_]], ___]] :> PiTerm["inj"[2][x], PiPlus[PiPlus[A, B], C]]
},
	PiFunction[PiPlus[\[FormalCapitalA]_, PiPlus[\[FormalCapitalB]_, \[FormalCapitalC]_]], PiPlus[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_]],
	"\!\(\*SubscriptBox[\(assocl\), \(+\)]\)"
]

PiCombinator["PlusRightAssociation"] := PiTerm[{
	HoldPattern[PiTerm["inj"[2][x_], PiPlus[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_], ___]] :> PiTerm["inj"[2][PiTerm["inj"[2][x]]], PiPlus[A, PiPlus[B, C]]],
	HoldPattern[PiTerm["inj"[1][PiTerm["inj"[1][x_], _]], PiPlus[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_], ___]] :> PiTerm["inj"[1][x], PiPlus[A, PiPlus[B, C]]],
	HoldPattern[PiTerm["inj"[1][PiTerm["inj"[2][x_], _]], PiPlus[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_], ___]] :> PiTerm["inj"[2][PiTerm["inj"[1][x]]], PiPlus[A, PiPlus[B, C]]]
},
	PiFunction[PiPlus[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_], PiPlus[\[FormalCapitalA]_, PiPlus[\[FormalCapitalB]_, \[FormalCapitalC]_]]],
	"\!\(\*SubscriptBox[\(assocr\), \(+\)]\)"
]

PiCombinator["UnitElimination"] := PiTerm[HoldPattern[PiTerm[{_, x_}, PiTimes[PiUnit, _], ___]] :> x,  PiFunction[PiTimes[PiUnit, \[FormalCapitalA]_], \[FormalCapitalA]_], "\!\(\*SubscriptBox[\(unite\), \(*\)]\)l"]
PiCombinator["UnitIntroduction"] := PiTerm[x_ :> PiTerm[{"tt", x}], PiFunction[\[FormalCapitalA]_, PiTimes[PiUnit, \[FormalCapitalA]_]], "\!\(\*SubscriptBox[\(uniti\), \(*\)]\)l"]

PiCombinator["TimesSwap"] := PiTerm[PiTerm[{x_, y_}, __] :> PiTerm[{y, x}], PiFunction[PiTimes[\[FormalCapitalA]_, \[FormalCapitalB]_], PiTimes[\[FormalCapitalB]_, \[FormalCapitalA]_]], "\!\(\*SubscriptBox[\(swap\), \(*\)]\)"]

PiCombinator["TimesLeftAssociation"] := PiTerm[HoldPattern[PiTerm[{x_, PiTerm[{y_, z_}, _]}, __]] :> PiTerm[{PiTerm[{x, y}], z}], PiFunction[PiTimes[\[FormalCapitalA]_, PiTimes[\[FormalCapitalB]_, \[FormalCapitalC]_]], PiTimes[PiTimes[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_]], "\!\(\*SubscriptBox[\(assocl\), \(*\)]\)"]
PiCombinator["TimesRightAssociation"] := PiTerm[HoldPattern[PiTerm[{PiTerm[{x_, y_}, _], z_}, __]] :> PiTerm[{x, PiTerm[{y, z}]}], PiFunction[PiTimes[PiTimes[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_], PiTimes[\[FormalCapitalA]_, PiTimes[\[FormalCapitalB]_, \[FormalCapitalC]_]]], "\!\(\*SubscriptBox[\(assocr\), \(*\)]\)"]

PiCombinator["Distribution"] := PiTerm[{
	HoldPattern[PiTerm[{PiTerm["inj"[1][x_], __], z_}, PiTimes[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_], ___]] :> PiTerm["inj"[1][{x, z}], PiPlus[PiTimes[A, C], PiTimes[B, C]]],
	HoldPattern[PiTerm[{PiTerm["inj"[2][y_], _], z_}, PiTimes[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_]]] :> PiTerm["inj"[2][{y, z}], PiPlus[PiTimes[A, C], PiTimes[B, C]]]
},
	PiFunction[PiTimes[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_], PiPlus[PiTimes[\[FormalCapitalA]_, \[FormalCapitalC]_], PiTimes[\[FormalCapitalB]_, \[FormalCapitalC]_]]],
	"dist"
]

PiCombinator["Factorization"] := PiTerm[{
	HoldPattern[PiTerm["inj"[1][PiTerm[{x_, z_}, _]], PiPlus[PiTimes[\[FormalCapitalA]_, \[FormalCapitalC]_], PiTimes[\[FormalCapitalB]_, \[FormalCapitalC]_]]]] :> PiTerm[{PiTerm["inj"[1][x], PiPlus[A, B]], z}],
	HoldPattern[PiTerm["inj"[2][PiTerm[{y_, z_}, _]], PiPlus[PiTimes[\[FormalCapitalA]_, \[FormalCapitalC]_], PiTimes[\[FormalCapitalB]_, \[FormalCapitalC]_]]]] :> PiTerm[{PiTerm["inj"[2][y], PiPlus[A, B]], z}]
},
	PiFunction[PiPlus[PiTimes[\[FormalCapitalA]_, \[FormalCapitalC]_], PiTimes[\[FormalCapitalB]_, \[FormalCapitalC]_]], PiTimes[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_]],
	"factor"
]

PiCombinator["PlusCup"] := PiTerm[Except[_] :> PiTerm["tt"], PiFunction[PiZero, PiPlus[\[FormalCapitalA]_, PiMinus[\[FormalCapitalA]_]]], "\!\(\*SubscriptBox[\(\[Eta]\), \(+\)]\)"]
PiCombinator["PlusCap"] := PiTerm[HoldPattern[PiTerm["inj"[_][x_], __] ? PiTermQ] :> $Failed, PiFunction[PiPlus[\[FormalCapitalA]_, PiMinus[\[FormalCapitalA]_]], PiZero], "\!\(\*SubscriptBox[\(\[CurlyEpsilon]\), \(+\)]\)"]

ResourceFunction["AddCodeCompletion"]["PiCombinator"][DownValues[PiCombinator][[All, 1, 1, 1]]];

End[];

EndPackage[]; 