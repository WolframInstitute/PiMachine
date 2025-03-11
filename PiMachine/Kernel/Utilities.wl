(* ::Package:: *)

BeginPackage["WolframInstitute`PiMachine`"];

ClearAll[
    Uniquify, UniquifyTypes, CanonicalizeTypes, UnifyFunctionTypes,
    makeReplaceRule, unify,
    TypeSubstitute,
    HoldFunction
]

Begin["`Private`"];


Uniquify[expr_, ref_ : None] := With[{types = DeleteDuplicates @ Cases[Replace[ref, None -> expr], Verbatim[Pattern][name_, _] :> Hold[name], All]},
	Thread[HoldPattern @@@ types -> Block[{$ModuleNumber = 1}, Function[Null, Unique[Unevaluated[#]], HoldFirst] @@@ types]]
]
UniquifyTypes[expr_, ref_ : None] := expr /. Uniquify[expr, ref]

CanonicalizeTypes[expr_] := With[{types = DeleteDuplicates @ Cases[expr, Verbatim[Pattern][name_, _] :> Hold[name], All]},
	expr /. MapThread[{old, new} |-> Function[Null, HoldPattern @@ old :> #, HoldFirst] @@ new, {types, ToExpression["\\[FormalCapital" <> ToUpperCase[#] <> "]", StandardForm, Hold] & /@ Take[Alphabet[], Length[types]]}]
]
UnifyFunctionTypes[fs : {{_, _} ..}, g : {_, _}] := Enclose @ With[{ug = UniquifyTypes[g, g[[1]]]},
	CanonicalizeTypes[Append[fs, ug] /. Confirm[MostGeneralUnifier @@ {fs[[-1, 2]], ug[[1]]}]]
]
UnifyFunctionTypes[{f : {_, _}, fs : {_, _} ..}] := Fold[UnifyFunctionTypes, {f}, {fs}]


SetAttributes[makeReplaceRule, HoldRest]
makeReplaceRule[lhs_, rhs_] := With[{newRHS = ReplaceAll[Hold[rhs], (Verbatim[#] -> First[#] & /@ DeleteDuplicates @ Cases[lhs, _Pattern, All, Heads -> True])]},
    ReleaseHold[RuleDelayed @@ {lhs, newRHS}]
]

Options[unify] := {Heads -> True};
unify[x_, y_, patt : Except[OptionsPattern[]] : _Pattern, opts : OptionsPattern[]] := Enclose[
    Module[{
        pos = Position[x, patt, Heads -> OptionValue[unify, {opts}, Heads]],
        patts
    },
        patts = DeleteDuplicates[Extract[x, pos]];

        ReleaseHold /@ Association @ DeleteCases[\[FormalX]_ -> Hold[\[FormalX]_]] @ MapThread[Rule, {patts, #}] & /@
            ConfirmBy[ReplaceList[y, With[{holdPatts = Hold /@ patts},
                makeReplaceRule[MapAt[Replace[s_Symbol :> Pattern @@ {s, Blank[]}], x, pos], holdPatts]]], Length[#] > 0 &]
    ],
    Failure["NonUnifiable", <|"MessageTemplate" -> "Can't unify `` with ``", "MessageParameters" -> {x, y}|>] &
]


TypeSubstitute[term_, rules_] := If[PiTermQ[term],
	PiTerm[TypeSubstitute[term["Term"], rules], term["Type"] /. rules, Sequence @@ term["Arguments"]],
	term /. t_PiTerm ? PiTermQ :> RuleCondition[TypeSubstitute[t, rules]]
]

HoldFunction[f_] := Function[Null, f @@ Unevaluated /@ Hold[##], HoldAllComplete]

End[];

EndPackage[]; 