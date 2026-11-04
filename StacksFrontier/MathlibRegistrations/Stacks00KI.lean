module
public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksCore.Tactic.StacksAttribute

/-! Mathlib already states Stacks tag 00KI via `isArtinianRing_iff_krullDimLE_zero` and
    `isArtinianRing_iff_isFiniteLength`. -/

@[expose] public section

add_to_stacks 00KI "dimension zero implies d=0" isArtinianRing_iff_krullDimLE_zero
add_to_ega "0 16.1.1" "partial" isArtinianRing_iff_krullDimLE_zero
add_to_ega "0 16.2.5" "special case" isArtinianRing_iff_krullDimLE_zero
add_to_stacks 00KI "d=0 characterization" isArtinianRing_iff_isFiniteLength
add_to_sga "3 VIIB 0.1" "partial" isArtinianRing_iff_isFiniteLength
add_to_sga "3 VIIB 0.4.2" "more general" isArtinianRing_iff_isFiniteLength
