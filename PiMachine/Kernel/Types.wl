(* ::Package:: *)

BeginPackage["Wolfram`PiMachine`"];

ClearAll[
    PiZero, PiUnit, PiPlus, PiTimes, PiFunction, PiContinuation,
    PiMinus, PiInverse,
	PiForward, PiBackward,
	PiTypeQ
]

Begin["`Private`"];


PiPlus[x_] := x
PiPlus[] := PiZero

PiTimes[x_] := x
PiTimes[] := PiUnit

PiPlus[fs__PiFunction ? PiTypeQ] := PiFunction @@ PiPlus @@@ CanonicalizeTypes[Thread[UniquifyTypes /@ List @@@ {fs}]]
PiTimes[fs__PiFunction ? PiTypeQ] := PiFunction @@ PiTimes @@@ CanonicalizeTypes[Thread[UniquifyTypes /@ List @@@ {fs}]]
PiFunction /: RightComposition[fs__PiFunction ? PiTypeQ] := With[{types = UnifyFunctionTypes[List @@@ {fs}]},
	PiFunction[types[[1, 1]], types[[-1, 2]]] /; MatchQ[types, {{_, _} ..}] && AllTrue[Partition[Most @ Rest @ Catenate[types], 2], Apply[SameQ]]
]

PiTypeQ[HoldPattern[
	PiZero | PiUnit |
	PiPlus[ts : Repeated[_ ? PiTypeQ, {2, Infinity}]] |
	PiTimes[ts : Repeated[_ ? PiTypeQ, {2, Infinity}]] |
	Verbatim[Pattern][_Symbol, Verbatim[_]] |
	(PiFunction | PiContinuation)[ts : Repeated[_ ? PiTypeQ, {2}]] |

	PiMinus[_ ? PiTypeQ] |
	PiInverse[_ ? PiTypeQ] |

	PiForward[_ ? PiTypeQ] | PiBackward[_ ? PiTypeQ]
]] := True
PiTypeQ[___] := False


(* Formatting *)

PiZero /: MakeBoxes[PiZero, _] := InterpretationBox["\[DoubleStruckZero]", PiZero, Tooltip -> "\[DoubleStruckZero]: \[CapitalPi] type"]
PiUnit /: MakeBoxes[PiUnit, _] := InterpretationBox["\[DoubleStruckOne]", PiUnit, Tooltip -> "\[DoubleStruckOne]: \[CapitalPi] type"]

PiPlus /: MakeBoxes[PiPlus[xs__] ? PiTypeQ, form_] :=
	InterpretationBox[#, PiPlus[xs], Tooltip -> "\[CirclePlus]: \[CapitalPi] type"] & @ With[{type = Replace[CirclePlus[xs], CirclePlus[PiUnit, PiUnit] -> "\[DoubleStruckCapitalB]"]}, Parenthesize[type, form, Plus] /. "\[CirclePlus]" -> "+"]
PiTimes /: MakeBoxes[PiTimes[xs__] ? PiTypeQ, form_] :=
	InterpretationBox[#, PiTimes[xs], Tooltip -> "\[CircleTimes]: \[CapitalPi] type"] & @ (Parenthesize[CircleTimes[xs], form, Times] /. "\[CircleTimes]" -> "\[Times]")

PiFunction /: MakeBoxes[PiFunction[x_, y_] ? PiTypeQ, form_] :=
	InterpretationBox[#, PiFunction[x, y], Tooltip -> "\[TwoWayRule]: \[CapitalPi] type"] & @ RowBox[{ToBoxes[x, form], "\[TwoWayRule]", ToBoxes[y, form]}]
PiContinuation /: MakeBoxes[PiContinuation[x_, y_] ? PiTypeQ, form_] :=
	InterpretationBox[#, PiContinuation[x, y], Tooltip -> "CONT: \[CapitalPi] type"] & @ SubscriptBox["CONT", RowBox[{ToBoxes[x, form], "\[TwoWayRule]", ToBoxes[y, form]}]]

PiMinus /: MakeBoxes[PiMinus[x_] ? PiTypeQ, form_] :=
	InterpretationBox[#, PiMinus[x], Tooltip -> "-: \[CapitalPi] type"] & @ (RowBox[{"-", MakeBoxes[x, form]}])
PiInverse /: MakeBoxes[PiInverse[x_] ? PiTypeQ, form_] :=
	InterpretationBox[#, PiInverse[x], Tooltip -> "\!\(\*SuperscriptBox[\(\\\ \), \(-1\)]\): \[CapitalPi] type"] & @ (RowBox[{"\!\(\*SuperscriptBox[\(\\\ \), \(-1\)]\)", MakeBoxes[x, form]}])

PiForward /: MakeBoxes[PiForward[x_] ? PiTypeQ, form_] :=
	InterpretationBox[#, PiForward[x], Tooltip -> "\[RightArrow]: \[CapitalPi] type"] & @ SuperscriptBox[MakeBoxes[x, form], "\[RightArrow]"]

PiBackward /: MakeBoxes[PiBackward[x_] ? PiTypeQ, form_] :=
	InterpretationBox[#, PiBackward[x], Tooltip -> "\[LeftArrow]: \[CapitalPi] type"] & @ SuperscriptBox[MakeBoxes[x, form], "\[LeftArrow]"]


End[];

EndPackage[]; 