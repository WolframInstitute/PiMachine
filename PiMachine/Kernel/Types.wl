(* ::Package:: *)

BeginPackage["WolframInstitute`PiMachine`"];

ClearAll[
    PiZero, PiUnit, PiPlus, PiTimes, PiFunction, PiContinuation,
    PiMinus, PiInverse,
	PiForward, PiBackward, PiError,
	PiType, HoldPiTypeQ, PiTypeQ
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

HoldPiTypeQ = HoldFunction[PiTypeQ]

PiType = HoldPattern[
	PiZero | PiUnit |
	PiPlus[Repeated[_ ? HoldPiTypeQ, {2, Infinity}]] |
	PiTimes[Repeated[_ ? HoldPiTypeQ, {2, Infinity}]] |
	Verbatim[Pattern][_Symbol, Verbatim[_]] |
	(PiFunction | PiContinuation)[_ ? HoldPiTypeQ, _ ? HoldPiTypeQ] |

	PiMinus[_ ? HoldPiTypeQ] |
	PiInverse[_ ? HoldPiTermQ] |

	PiForward[_ ? HoldPiTypeQ] | PiBackward[_ ? HoldPiTypeQ] | PiError[_ ? HoldPiTypeQ]
]
PiTypeQ[type_] := MatchQ[Unevaluated[type], PiType]
PiTypeQ[___] := False


(* Formatting *)

PiZero /: MakeBoxes[PiZero, _] := InterpretationBox["\[DoubleStruckZero]", PiZero, Tooltip -> "\[DoubleStruckZero]: \[CapitalPi] type"]
PiUnit /: MakeBoxes[PiUnit, _] := InterpretationBox["\[DoubleStruckOne]", PiUnit, Tooltip -> "\[DoubleStruckOne]: \[CapitalPi] type"]

PiPlus /: MakeBoxes[PiPlus[xs__] ? HoldPiTypeQ, form_] :=
	InterpretationBox[#, PiPlus[xs], Tooltip -> "\[CirclePlus]: \[CapitalPi] type"] & @ With[{type = Replace[CirclePlus[xs], CirclePlus[PiUnit, PiUnit] -> "\[DoubleStruckCapitalB]"]}, Parenthesize[type, form, Plus] /. "\[CirclePlus]" -> "+"]
PiTimes /: MakeBoxes[PiTimes[xs__] ? HoldPiTypeQ, form_] :=
	InterpretationBox[#, PiTimes[xs], Tooltip -> "\[CircleTimes]: \[CapitalPi] type"] & @ (Parenthesize[CircleTimes[xs], form, Times] /. "\[CircleTimes]" -> "\[Times]")

PiFunction /: MakeBoxes[PiFunction[x_, y_] ? HoldPiTypeQ, form_] :=
	InterpretationBox[#, PiFunction[x, y], Tooltip -> "\[Rule]: \[CapitalPi] type"] & @ RowBox[{ToBoxes[x, form], "\[Rule]", ToBoxes[y, form]}]
PiContinuation /: MakeBoxes[PiContinuation[x_, y_] ? HoldPiTypeQ, form_] :=
	InterpretationBox[#, PiContinuation[x, y], Tooltip -> "CONT: \[CapitalPi] type"] & @ SubscriptBox["CONT", RowBox[{ToBoxes[x, form], "\[TwoWayRule]", ToBoxes[y, form]}]]

PiMinus /: MakeBoxes[PiMinus[x_] ? HoldPiTypeQ, form_] :=
	InterpretationBox[#, PiMinus[x], Tooltip -> "-: \[CapitalPi] type"] & @ (RowBox[{"-", MakeBoxes[x, form]}])
PiInverse /: MakeBoxes[PiInverse[x_] ? HoldPiTypeQ, form_] :=
	InterpretationBox[#, PiInverse[x], Tooltip -> "\!\(\*SuperscriptBox[\(\\\ \), \(-1\)]\): \[CapitalPi] type"] & @ (SuperscriptBox[MakeBoxes[x, form], -1])

PiForward /: MakeBoxes[PiForward[x_] ? HoldPiTypeQ, form_] :=
	InterpretationBox[#, PiForward[x], Tooltip -> "\[Rule]: \[CapitalPi] type"] & @ OverscriptBox[MakeBoxes[x, form], "\[Rule]"]

PiBackward /: MakeBoxes[PiBackward[x_] ? HoldPiTypeQ, form_] :=
	InterpretationBox[#, PiBackward[x], Tooltip -> "\[LeftArrow]: \[CapitalPi] type"] & @ OverscriptBox[MakeBoxes[x, form], "\[ShortLeftArrow]"]

PiError /: MakeBoxes[PiError[x_] ? HoldPiTypeQ, form_] :=
	InterpretationBox[#, PiError[x], Tooltip -> "error: \[CapitalPi] type"] & @ FrameBox[MakeBoxes[x, form], FrameStyle -> Red]


End[];

EndPackage[]; 