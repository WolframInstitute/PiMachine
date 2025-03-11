BeginPackage["WolframInstitute`PiMachine`"];

ClearAll[
    MostGeneralUnifier
]

Begin["`Private`"];

patternsToSymbols[expr_] := 
 ReplaceAll[expr, Verbatim[Pattern][name_, _] :> name]

lexicographicPatternSort[l_List] := 
 Catenate@
  Values@Reverse@
    KeySort@GroupBy[SortBy[l, patternsToSymbols], 
      MatchQ[Hold[_Pattern]]]

disagreementSet // ClearAll

disagreementSet[term_ ...] := {}

disagreementSet[terms : Except[Pattern][___] ...] := 
 If[SameQ @@ Hold /@ Unevaluated@{terms}, {}, 
  Enclose@With[{rec = 
      Unevaluated[disagreementSet[##]] & @@ 
       ConfirmBy[Hold @@@ Unevaluated@{terms}, 
        Apply[Equal]@*Map[Length]]},
    
    lexicographicPatternSort[Union @@ ConfirmBy[Join[
        ReplacePart[
         Extract[Unevaluated@{terms}, {All, 0}, Hold], {1, 0} -> 
          disagreementSet],
        Thread[rec, Hold]
        ],
       NoneTrue[FailureQ]
       ]
     ]
    ]
  ]

disagreementSet[
  terms___] := {lexicographicPatternSort@
   Union[Hold /@ Unevaluated@{terms}]}

SetAttributes[disagreementSet, HoldAll]


unifier[terms___, substitution_Association] := 
 Module[{newTerms, ds, tuple, s, t, rule},
  newTerms = Hold[terms] /. substitution;
  ds = disagreementSet @@ newTerms;
  If[FailureQ[ds], 
   Return[With[{listTerms = List @@ HoldForm /@ newTerms}, 
     Failure["NonUnifiable", <|"MessageTemplate" -> "Can't unify ``", 
       "MessageParameters" -> {Row[{Row[Most@listTerms, ","], 
           Last@listTerms}, "and"]}, "Terms" -> listTerms|>]
     ]]];
  If[ds === {}, Return[substitution]];
  (*tuple=SelectFirst[ds,MatchQ[#[[2]],#[[1]]]&];*)
  (*If[MissingQ[tuple],Return[failure]];*)
  tuple = First[ds];
  {s, t} = Take[tuple, 2];
  If[! MatchQ[s, Hold[_Pattern]] || ! 
     FreeQ[t, HoldPattern[Evaluate[Verbatim @@ s]]], 
   Return[Failure[
     "NonUnifiable", <|"MessageTemplate" -> "Can't unify `` and ``", 
      "MessageParameters" -> HoldForm @@@ {s, t}, 
      "Terms" -> HoldForm @@@ {s, t}|>]]];
  rule = With[{rhs = Unevaluated @@ t}, First[s] :> rhs];
  With[{values = 
     Function[Null, Unevaluated@{##}, 
       HoldAll] @@ (Join @@ 
        ReplaceAll[<|rule|>] /@ Values[Hold /@ substitution])},
   unifier[terms, 
    Evaluate@<|AssociationThread[Keys[substitution] :> values], rule|>]]
  ]

SetAttributes[unifier, HoldAll]

MostGeneralUnifier[terms___] := unifier[terms, <||>]

SetAttributes[MostGeneralUnifier, HoldAll]


End[];

EndPackage[]; 