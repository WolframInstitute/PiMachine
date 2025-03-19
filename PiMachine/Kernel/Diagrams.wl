Quiet @ Check[
    Get["ProcessTheoryLoader`"]
    ,
    PacletInstall["https://www.wolframcloud.com/obj/nikm/ProcessTheoryLoader.paclet", ForceVersionInstall -> True];
    Check[Get["ProcessTheoryLoader`"], Throw[$Failed]]
]

BeginPackage["WolframInstitute`PiMachine`", {"WolframInstitute`PiMachine`Programs`", "ProcessTheory`Diagram`"}];

ClearAll[
    PiMachinePort,
    PiMachineDiagram
]

Begin["`Private`"];

PiMachinePort[type_ ? PiTypeQ] := Replace[type, {
	PiUnit :> Port[1],
	PiZero :> Port["0"],
	HoldPattern[PiPlus[PiUnit, PiUnit]] :> Port["\[DoubleStruckCapitalB]"],
	HoldPattern[PiPlus[ts__]] :> PortSum @@ PiMachinePort /@ {ts},
	HoldPattern[PiTimes[ts__]] :> PortProduct @@ PiMachinePort /@ {ts},
    PiInverse[t_] :> PortDual[t],
    PiMinus[t_] :> PortMinus[PiMachinePort[t]],
	PiFunction[a_, b_] :> PortPower[PiMachinePort[a], PiMachinePort[b]],
	Verbatim[Pattern][a_, _] | a_ :> Port[a]
}]

PiMachineDiagram[pi_PiTerm ? PiTermQ, opts___] := Diagram[Replace[pi, {
	t_ /; MatchQ[t["Label"], id["Label"]] :> IdentityDiagram[{PiMachinePort[t["Type"][[1]]]}],
	t_ /; MatchQ[t["Label"], assoclt["Label"] | assocrt["Label"]] :> IdentityDiagram[PiMachinePort /@ List @@ Flatten[t["Type"][[1]], 1, PiTimes]],
	t_ /; MatchQ[t["Label"], swapt["Label"]] :> PermutationDiagram[List @@ PiMachinePort /@ t["Type"][[1]], Cycles[{{1, 2}}]],
	t_ /; MatchQ[t["Label"], uniti["Label"]] :> Diagram["", PiMachinePort @ t["Type"][[1]], List @@ PiMachinePort /@ t["Type"][[2]], "Shape" -> "Wires"[{{1, 3}}]],
	t_ /; MatchQ[t["Label"], unite["Label"]] :> Diagram["", List @@ PiMachinePort /@ t["Type"][[1]], PiMachinePort @ t["Type"][[2]], "Shape" -> "Wires"[{{2, 3}}]],
	PiTerm[CircleDot[ts__], ___] :> ColumnDiagram[PiMachineDiagram /@ {ts}],
	PiTerm[CircleTimes[ts__], ___] :> DiagramProduct @@ PiMachineDiagram /@ {ts},
	PiTerm[CirclePlus[ts__], ___] :> DiagramSum @@ PiMachineDiagram /@ {ts},
	PiTerm[_, PiFunction[a_, b_], label_, ___] :> Diagram[label, PiMachinePort[a], PiMachinePort[b]]["Flatten"],
	PiTerm[_, PiFunction[a_, b_], ___] :> Diagram["f", PiMachinePort[a], PiMachinePort[b]]
}], opts]

End[]

EndPackage[]