(* ::Package:: *)

BeginPackage["WolframInstitute`PiMachine`"];

(* ::Text:: *)
(*Declare your public symbols here:*)
ClearAll[
    PiTerm, HoldPiTermQ, PiTermQ
]


Get["WolframInstitute`PiMachine`Temp`"];
Get["WolframInstitute`PiMachine`Utilities`"];
Get["WolframInstitute`PiMachine`Types`"];
Get["WolframInstitute`PiMachine`Terms`"];
Get["WolframInstitute`PiMachine`Combinators`"];
Get["WolframInstitute`PiMachine`Interpreter`"];
Get["WolframInstitute`PiMachine`Programs`"];
Get["WolframInstitute`PiMachine`Diagrams`"];

EndPackage[];