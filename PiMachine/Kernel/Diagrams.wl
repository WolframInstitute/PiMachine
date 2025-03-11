BeginPackage["WolframInstitute`PiMachine`", "ProcessTheory`Port`"];

ClearAll[
    PiMachinePort,
    PiMachineDiagram
]

Begin["`Private`"];

ClearAll[PiMachinePort, PiMachineDiagram]

PiMachinePort[type_ ? PiTypeQ] := Replace[type, {
	PiUnit :> Port["1"],
	PiZero :> Port["0"],
	HoldPattern[PiPlus[PiUnit, PiUnit]] :> Port["\[DoubleStruckCapitalB]"],
	HoldPattern[PiPlus[ts__]] :> PortSum @@ PiMachinePort /@ {ts},
	HoldPattern[PiTimes[ts__]] :> PortProduct @@ PiMachinePort /@ {ts},
	PiFunction[a_, b_] :> PortPower[PiMachinePort[a], PiMachinePort[b]],
	Verbatim[Pattern][a_, _] | a_ :> Port[a]
}]

PiMachineDiagram[pi_PiTerm ? PiTermQ, opts___] := Diagram[Replace[pi, {
	PiTerm[CircleDot[ts__], ___] :> ColumnDiagram[PiMachineDiagram /@ {ts}],
	PiTerm[CircleTimes[ts__], ___] :> DiagramProduct @@ PiMachineDiagram /@ {ts},
	PiTerm[CirclePlus[ts__], ___] :> DiagramSum @@ PiMachineDiagram /@ {ts},
	PiTerm[_, PiFunction[a_, b_], label_, ___] :> Diagram[label, PiMachinePort[a], PiMachinePort[b]]["Flatten"],
	PiTerm[_, PiFunction[a_, b_], ___] :> Diagram["f", PiMachinePort[a], PiMachinePort[b]]
}], opts]

End[]

EndPackage[]