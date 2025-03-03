(* ::Package:: *)

BeginPackage["Wolfram`PiMachine`"];

ClearAll[
    PiCombinator, PiCombinatorInverse
]

Begin["`Private`"];

$PiCombinatorLabels = <|
	"Identity" -> "id",
	"ZeroElimination" -> Row[{Subscript["unite", "+"], "l"}],
	"ZeroIntroduction" -> Row[{Subscript["uniti", "+"], "l"}],
	"PlusSwap" -> Subscript["swap", "+"],
	"PlusLeftAssociation" -> Subscript["assocl", "+"],
	"PlusRightAssociation" -> Subscript["assocr", "+"],
	"UnitElimination" -> Row[{Subscript["unite", "*"], "l"}],
	"UnitIntroduction" -> Row[{Subscript["uniti", "*"], "l"}],
	"TimesSwap" -> Subscript["swap", "*"],
	"TimesLeftAssociation" -> Subscript["assocl", "*"],
	"TimesRightAssociation" -> Subscript["assocr", "*"],
	"Distribution" -> "dist",
	"Factorization" -> "factor",
	"PlusCup" -> Subscript["\[Eta]", "+"],
	"PlusCap" -> Subscript["\[Epsilon]", "+"],
	"TimesCup" -> Subscript["\[Eta]", "*"],
	"TimesCap" -> Subscript["\[Epsilon]", "*"]
|>


PiCombinator["Identity"] := PiTerm[{}, PiFunction[\[FormalCapitalA]_, \[FormalCapitalA]_], $PiCombinatorLabels["Identity"]]
PiCombinator["ZeroElimination"] := PiTerm[HoldPattern[PiTerm[PiChoice[2][x_], PiPlus[PiZero, _], ___]] :> x, PiFunction[PiPlus[PiZero, \[FormalCapitalA]_], \[FormalCapitalA]_], $PiCombinatorLabels["ZeroElimination"]]
PiCombinator["ZeroIntroduction"] := PiTerm[x_ :> PiTerm[PiChoice[2][x], PiPlus[PiZero, x["Type"]]], PiFunction[\[FormalCapitalA]_, PiPlus[PiZero, \[FormalCapitalA]_]], $PiCombinatorLabels["ZeroIntroduction"]]
PiCombinator["PlusSwap"] := PiTerm[HoldPattern[PiTerm[PiChoice[i_][x_], PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], ___]] :> PiTerm[PiChoice[3 - i][x], PiPlus[\[FormalCapitalB], \[FormalCapitalA]]], PiFunction[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], PiPlus[\[FormalCapitalB]_, \[FormalCapitalA]_]], $PiCombinatorLabels["PlusSwap"]]
PiCombinator["PlusLeftAssociation"] := PiTerm[{
	HoldPattern[PiTerm[PiChoice[1][x_], PiPlus[\[FormalCapitalA]_, PiPlus[\[FormalCapitalB]_, \[FormalCapitalC]_]], ___]] :> PiTerm[PiChoice[1][PiTerm[PiChoice[1][x], PiPlus[\[FormalCapitalA], \[FormalCapitalB]]]], PiPlus[PiPlus[\[FormalCapitalA], \[FormalCapitalB]], \[FormalCapitalC]]],
	HoldPattern[PiTerm[PiChoice[2][PiTerm[PiChoice[1][x_], _]], PiPlus[\[FormalCapitalA]_, PiPlus[\[FormalCapitalB]_, \[FormalCapitalC]_]], ___]] :> PiTerm[PiChoice[1][PiTerm[PiChoice[2][x], PiPlus[\[FormalCapitalA], \[FormalCapitalB]]]], PiPlus[PiPlus[\[FormalCapitalA], \[FormalCapitalB]], \[FormalCapitalC]]],
	HoldPattern[PiTerm[PiChoice[2][PiTerm[PiChoice[2][x_], _]], PiPlus[\[FormalCapitalA]_, PiPlus[\[FormalCapitalB]_, \[FormalCapitalC]_]], ___]] :> PiTerm[PiChoice[2][x], PiPlus[PiPlus[\[FormalCapitalA], \[FormalCapitalB]], \[FormalCapitalC]]]
},
	PiFunction[PiPlus[\[FormalCapitalA]_, PiPlus[\[FormalCapitalB]_, \[FormalCapitalC]_]], PiPlus[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_]],
	$PiCombinatorLabels["PlusLeftAssociation"]
]

PiCombinator["PlusRightAssociation"] := PiTerm[{
	HoldPattern[PiTerm[PiChoice[2][x_], PiPlus[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_], ___]] :> PiTerm[PiChoice[2][PiTerm[PiChoice[2][x], PiPlus[\[FormalCapitalB], \[FormalCapitalC]]]], PiPlus[\[FormalCapitalA], PiPlus[\[FormalCapitalB], \[FormalCapitalC]]]],
	HoldPattern[PiTerm[PiChoice[1][PiTerm[PiChoice[1][x_], _]], PiPlus[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_], ___]] :> PiTerm[PiChoice[1][x], PiPlus[\[FormalCapitalA], PiPlus[\[FormalCapitalB], \[FormalCapitalC]]]],
	HoldPattern[PiTerm[PiChoice[1][PiTerm[PiChoice[2][x_], _]], PiPlus[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_], ___]] :> PiTerm[PiChoice[2][PiTerm[PiChoice[1][x], PiPlus[\[FormalCapitalB], \[FormalCapitalC]]]], PiPlus[\[FormalCapitalA], PiPlus[\[FormalCapitalB], \[FormalCapitalC]]]]
},
	PiFunction[PiPlus[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_], PiPlus[\[FormalCapitalA]_, PiPlus[\[FormalCapitalB]_, \[FormalCapitalC]_]]],
	$PiCombinatorLabels["PlusRightAssociation"]
]

PiCombinator["UnitElimination"] := PiTerm[HoldPattern[PiTerm[{_, x_}, PiTimes[PiUnit, _], ___]] :> x,  PiFunction[PiTimes[PiUnit, \[FormalCapitalA]_], \[FormalCapitalA]_], $PiCombinatorLabels["UnitElimination"]]
PiCombinator["UnitIntroduction"] := PiTerm[x_ :> PiTerm[{PiOne, x}], PiFunction[\[FormalCapitalA]_, PiTimes[PiUnit, \[FormalCapitalA]_]], $PiCombinatorLabels["UnitIntroduction"]]

PiCombinator["TimesSwap"] := PiTerm[PiTerm[{x_, y_}, __] :> PiTerm[{y, x}], PiFunction[PiTimes[\[FormalCapitalA]_, \[FormalCapitalB]_], PiTimes[\[FormalCapitalB]_, \[FormalCapitalA]_]], $PiCombinatorLabels["TimesSwap"]]

PiCombinator["TimesLeftAssociation"] := PiTerm[HoldPattern[PiTerm[{x_, PiTerm[{y_, z_}, __]}, __]] :> PiTerm[{PiTerm[{x, y}], z}], PiFunction[PiTimes[\[FormalCapitalA]_, PiTimes[\[FormalCapitalB]_, \[FormalCapitalC]_]], PiTimes[PiTimes[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_]], $PiCombinatorLabels["TimesLeftAssociation"]]
PiCombinator["TimesRightAssociation"] := PiTerm[HoldPattern[PiTerm[{PiTerm[{x_, y_}, __], z_}, __]] :> PiTerm[{x, PiTerm[{y, z}]}], PiFunction[PiTimes[PiTimes[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_], PiTimes[\[FormalCapitalA]_, PiTimes[\[FormalCapitalB]_, \[FormalCapitalC]_]]], $PiCombinatorLabels["TimesRightAssociation"]]

PiCombinator["Distribution"] := PiTerm[{
	HoldPattern[PiTerm[{PiTerm[PiChoice[1][x_], __], z_}, PiTimes[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_], ___]] :> PiTerm[PiChoice[1][{x, z}], PiPlus[PiTimes[\[FormalCapitalA], \[FormalCapitalC]], PiTimes[\[FormalCapitalB], \[FormalCapitalC]]]],
	HoldPattern[PiTerm[{PiTerm[PiChoice[2][y_], __], z_}, PiTimes[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_]]] :> PiTerm[PiChoice[2][{y, z}], PiPlus[PiTimes[\[FormalCapitalA], \[FormalCapitalC]], PiTimes[\[FormalCapitalB], \[FormalCapitalC]]]]
},
	PiFunction[PiTimes[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_], PiPlus[PiTimes[\[FormalCapitalA]_, \[FormalCapitalC]_], PiTimes[\[FormalCapitalB]_, \[FormalCapitalC]_]]],
	$PiCombinatorLabels["Distribution"]
]

PiCombinator["Factorization"] := PiTerm[{
	HoldPattern[PiTerm[PiChoice[1][PiTerm[{x_, z_}, __]], PiPlus[PiTimes[\[FormalCapitalA]_, \[FormalCapitalC]_], PiTimes[\[FormalCapitalB]_, \[FormalCapitalC]_]]]] :> PiTerm[{PiTerm[PiChoice[1][x], PiPlus[\[FormalCapitalA], \[FormalCapitalB]]], z}],
	HoldPattern[PiTerm[PiChoice[2][PiTerm[{y_, z_}, __]], PiPlus[PiTimes[\[FormalCapitalA]_, \[FormalCapitalC]_], PiTimes[\[FormalCapitalB]_, \[FormalCapitalC]_]]]] :> PiTerm[{PiTerm[PiChoice[2][y], PiPlus[\[FormalCapitalA], \[FormalCapitalB]]], z}]
},
	PiFunction[PiPlus[PiTimes[\[FormalCapitalA]_, \[FormalCapitalC]_], PiTimes[\[FormalCapitalB]_, \[FormalCapitalC]_]], PiTimes[PiPlus[\[FormalCapitalA]_, \[FormalCapitalB]_], \[FormalCapitalC]_]],
	$PiCombinatorLabels["Factorization"]
]

PiCombinator["PlusCup"] := PiTerm[Except[_] :> PiTerm[PiChoice[2][PiOne]], PiFunction[PiZero, PiPlus[PiMinus[\[FormalCapitalA]_], \[FormalCapitalA]_]], $PiCombinatorLabels["PlusCup"]]
PiCombinator["PlusCap"] := PiTerm[HoldPattern[PiTerm[PiChoice[_][_], __] ? PiTermQ] :> PiTerm[PiBottom, PiZero], PiFunction[PiPlus[PiMinus[\[FormalCapitalA]_], \[FormalCapitalA]_], PiZero], $PiCombinatorLabels["PlusCap"]]

PiCombinator["TimesCup"[v_]] := With[{term = PiTerm[v]},
	PiTerm[PiTerm[_, PiUnit, ___] :> PiTerm[{term, PiBottom}], PiFunction[PiUnit, PiTimes[PiInverse[term["Type"]], term["Type"]]], $PiCombinatorLabels["TimesCup"][term]]
]
PiCombinator["TimesCap"[v_]] := With[{term = PiTerm[v]},
	PiTerm[{PiTerm[{PiTerm[_, v, ___], PiBottom}, ___] ? PiTermQ :> PiTerm[PiUnit], _ :> $Failed}, PiFunction[PiTimes[PiInverse[v], v], PiUnit], $PiCombinatorLabels["TimesCap"][term]]
]

ResourceFunction["AddCodeCompletion"]["PiCombinator"][Replace[DownValues[PiCombinator][[All, 1, 1, 1]], h_String[_] :> h, 1]];


$PiCombinatorInverses = {
	"Identity" -> "Identity",
	"ZeroElimination" -> "ZeroIntroduction",
	"ZeroIntroduction" -> "ZeroElimination",
	"PlusSwap" -> "PlusSwap",
	"PlusLeftAssociation" -> "PlusRightAssociation",
	"PlusRightAssociation" -> "PlusLeftAssociation",
	"UnitElimination" -> "UnitIntroduction",
	"UnitIntroduction" -> "UnitElimination",
	"TimesSwap" -> "TimesSwap",
	"TimesLeftAssociation" -> "TimesRightAssociation",
	"TimesRightAssociation" -> "TimesLeftAssociation",
	"Distribution" -> "Factorization",
	"Factorization" -> "Distribution",
	"PlusCup" -> "PlusCap",
	"PlusCap" -> "PlusCup",
	"TimesCup"[v_] :> "TimesCap"[v],
	"TimesCap"[v_] :> "TimesCup"[v]
}

PiCombinatorInverse[PiTerm[_ , t_PiFunction, label_, ___] ? PiTermQ] :=
	Enclose @ PiTerm[PiCombinator[Replace[Confirm @ Lookup[Reverse /@ Normal[$PiCombinatorLabels], label], $PiCombinatorInverses]], Reverse[t]]


End[];

EndPackage[]; 