module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import StacksCore.Tactic.StacksAttribute

/-! # Transcendence basis -/

@[expose] public section

add_to_stacks 030E "4, correctness" isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic
add_to_stacks 030F "first part" exists_isTranscendenceBasis
