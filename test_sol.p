%--------------------------------------------------------------------------
% File     : lisa.maths.Tests.saturation : TPTP v8.0.0.
% Domain   : None
% Problem  : question0
% Version  : None
% English  :

% Refs     : https://github.com/epfl-lara/lisa
%          : lisa.utils.tptp.ProofParser
% Source   : [Lisa, lisa.maths.Tests.saturation]
% Names    : 

% Status   : Unknown
% Rating   : ?
% Syntax   : ?
% SPC      : FOF_UNK_RFO_SEQ

% Comments : This problem, was printed from a statement in a proof of a theorem by the Lisa theorem prover for submission to proof-producing ATPs.
%--------------------------------------------------------------------------
fof(aa1, axiom, (! [Xx]: ((Xx = sf(sf(sf(sf(sf(sf(sf(sf(Xx)))))))))))).
fof(a2, axiom, (! [Xx]: ((Xx = sf(sf(sf(sf(sf(Xx))))))))).
fof(c3, conjecture, (cemptySet = sf(cemptySet))).
% Assumptions after simplification:

tff(a2_, plain,
   ! [v0: $i] :  ! [v1: $i] : ( ~ (sf(v0) = v1) |  ~ $i(v0) |  ? [v2: $i] :  ?
    [v3: $i] :  ? [v4: $i] : (sf(v4) = v0 & sf(v3) = v4 & sf(v2) = v3 & sf(v1) =
      v2 & $i(v4) & $i(v3) & $i(v2)))
  inference(princessSimplification, [], [a2])
).

tff(aa1_, plain,
   ! [v0: $i] :  ! [v1: $i] : ( ~ (sf(v0) = v1) |  ~ $i(v0) |  ? [v2: $i] :  ?
    [v3: $i] :  ? [v4: $i] :  ? [v5: $i] :  ? [v6: $i] :  ? [v7: $i] : (sf(v7) =
      v0 & sf(v6) = v7 & sf(v5) = v6 & sf(v4) = v5 & sf(v3) = v4 & sf(v2) = v3 &
      sf(v1) = v2 & $i(v7) & $i(v6) & $i(v5) & $i(v4) & $i(v3) & $i(v2)))
  inference(princessSimplification, [], [aa1])
).

tff(c3_, plain,
  $i(cemptySet) &  ? [v0: $i] : ( ~ (v0 = cemptySet) & sf(cemptySet) = v0 &
    $i(v0))
  inference(princessSimplification, [], [c3])
).

tff(function-axioms, plain,
   ! [v0: $i] :  ! [v1: $i] :  ! [v2: $i] : (v1 = v0 |  ~ (sf(v2) = v1) |  ~
    (sf(v2) = v0)) &  ? [v0: $i] :  ? [v1: $i] : (sf(v0) = v1 & $i(v1))
  inference(functionAxioms, [], [])
).

% Those formulas are unsatisfiable:

% Begin of proof

tff(f1, plain, $i(cemptySet), inference(ALPHA, [], [fc3_])).
tff(f2, plain,  ? [v0: $i] : ( ~ (v0 = cemptySet) & sf(cemptySet) = v0 & $i(v0)), inference(ALPHA, [], [fc3_])).

tff(f3, plain,  ! [v0: $i] :  ! [v1: $i] :  ! [v2: $i] : (v1 = v0 |  ~ (sf(v2) = v1) |  ~ (sf(v2) = v0)), inference(ALPHA, [], [ffunction-axioms])).

tff(f4, plain,  ~ (all_8_0 = cemptySet) & sf(cemptySet) = all_8_0 & $i(all_8_0), inference(DELTA, [all_8_0],[f2])).

tff(f5, plain,  ~ (all_8_0 = cemptySet), inference(ALPHA, [], [f4])).
tff(f6, plain, sf(cemptySet) = all_8_0, inference(ALPHA, [], [f4])).

tff(f7, plain,  ? [v0: $i] :  ? [v1: $i] :  ? [v2: $i] :  ? [v3: $i] :  ? [v4: $i] :  ? [v5: $i] : (sf(v5) = cemptySet & sf(v4) = v5 & sf(v3) = v4 & sf(v2) = v3 & sf(v1) = v2 & sf(v0) = v1 & sf(all_8_0) = v0 & $i(v5) & $i(v4) & $i(v3) & $i(v2) & $i(v1) & $i(v0)), inference(GROUND_INST, [all_8_0, cemptySet],[faa1_, f1, f6])).

tff(f8, plain,  ? [v0: $i] :  ? [v1: $i] :  ? [v2: $i] : (sf(v2) = cemptySet & sf(v1) = v2 & sf(v0) = v1 & sf(all_8_0) = v0 & $i(v2) & $i(v1) & $i(v0)), inference(GROUND_INST, [all_8_0, cemptySet],[fa2_, f1, f6])).

tff(f9, plain, sf(all_15_0) = cemptySet & sf(all_15_1) = all_15_0 & sf(all_15_2) = all_15_1 & sf(all_8_0) = all_15_2 & $i(all_15_0) & $i(all_15_1) & $i(all_15_2), inference(DELTA, [all_15_0, all_15_1, all_15_2],[f8])).

tff(f10, plain, sf(all_8_0) = all_15_2, inference(ALPHA, [], [f9])).
tff(f11, plain, sf(all_15_2) = all_15_1, inference(ALPHA, [], [f9])).
tff(f12, plain, sf(all_15_1) = all_15_0, inference(ALPHA, [], [f9])).
tff(f13, plain, sf(all_15_0) = cemptySet, inference(ALPHA, [], [f9])).

tff(f14, plain, sf(all_17_0) = cemptySet & sf(all_17_1) = all_17_0 & sf(all_17_2) = all_17_1 & sf(all_17_3) = all_17_2 & sf(all_17_4) = all_17_3 & sf(all_17_5) = all_17_4 & sf(all_8_0) = all_17_5 & $i(all_17_0) & $i(all_17_1) & $i(all_17_2) & $i(all_17_3) & $i(all_17_4) & $i(all_17_5), inference(DELTA, [all_17_0, all_17_1, all_17_2, all_17_3, all_17_4, all_17_5],[f7])).

tff(f15, plain, sf(all_8_0) = all_17_5, inference(ALPHA, [], [f14])).
tff(f16, plain, sf(all_17_5) = all_17_4, inference(ALPHA, [], [f14])).
tff(f17, plain, sf(all_17_4) = all_17_3, inference(ALPHA, [], [f14])).
tff(f18, plain, sf(all_17_3) = all_17_2, inference(ALPHA, [], [f14])).
tff(f19, plain, sf(all_17_2) = all_17_1, inference(ALPHA, [], [f14])).
tff(f20, plain, sf(all_17_1) = all_17_0, inference(ALPHA, [], [f14])).
tff(f21, plain, sf(all_17_0) = cemptySet, inference(ALPHA, [], [f14])).

tff(f22, plain, all_17_5 = all_15_2, inference(GROUND_INST, [all_8_0, all_17_5, all_15_2],[f3, f10, f15])).

tff(f23, plain, sf(all_15_2) = all_17_4, inference(REDUCE, [], [f16, f22])).

tff(f24, plain, all_17_4 = all_15_1, inference(GROUND_INST, [all_15_2, all_17_4, all_15_1],[f3, f11, f23])).

tff(f25, plain, sf(all_15_1) = all_17_3, inference(REDUCE, [], [f17, f24])).

tff(f26, plain, all_17_3 = all_15_0, inference(GROUND_INST, [all_15_1, all_17_3, all_15_0],[f3, f12, f25])).

tff(f27, plain, sf(all_15_0) = all_17_2, inference(REDUCE, [], [f18, f26])).

tff(f28, plain, all_17_2 = cemptySet, inference(GROUND_INST, [all_15_0, all_17_2, cemptySet],[f3, f13, f27])).

tff(f29, plain, sf(cemptySet) = all_17_1, inference(REDUCE, [], [f19, f28])).

tff(f30, plain, all_17_1 = all_8_0, inference(GROUND_INST, [cemptySet, all_17_1, all_8_0],[f3, f29, f6])).

tff(f31, plain, sf(all_8_0) = all_17_0, inference(REDUCE, [], [f20, f30])).

tff(f32, plain, all_17_0 = all_15_2, inference(GROUND_INST, [all_8_0, all_17_0, all_15_2],[f3, f10, f31])).

tff(f33, plain, sf(all_15_2) = cemptySet, inference(REDUCE, [], [f21, f32])).

tff(f34, plain, all_15_1 = cemptySet, inference(GROUND_INST, [all_15_2, cemptySet, all_15_1],[f3, f11, f33])).

tff(f35, plain, sf(cemptySet) = all_15_0, inference(REDUCE, [], [f12, f34])).

tff(f36, plain, all_15_0 = all_8_0, inference(GROUND_INST, [cemptySet, all_15_0, all_8_0],[f3, f35, f6])).

tff(f37, plain, sf(all_8_0) = cemptySet, inference(REDUCE, [], [f13, f36])).

tff(f38, plain, all_15_2 = cemptySet, inference(GROUND_INST, [all_8_0, cemptySet, all_15_2],[f3, f10, f37])).

tff(f39, plain, sf(cemptySet) = cemptySet, inference(REDUCE, [], [f33, f38])).

tff(f40, plain, all_8_0 = cemptySet, inference(GROUND_INST, [cemptySet, cemptySet, all_8_0],[f3, f39, f6])).

tff(f41, plain, $false, inference(REDUCE, [], [f40, f5])).
remaining cert

End of proof
