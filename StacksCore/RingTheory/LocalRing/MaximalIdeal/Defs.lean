module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import StacksCore.Tactic.StacksAttribute

/-! # The maximal ideal of a local ring

Stacks tag 07BI, second sentence: the maximal ideal of a local ring `R`, written `𝔪_R` in the
Stacks project. Mathlib spells it `IsLocalRing.maximalIdeal R`, defined as the ideal of
nonunits; that it is the unique maximal ideal is `IsLocalRing.maximalIdeal.isMaximal` together
with `IsLocalRing.maximal_ideal_unique`.
-/

@[expose] public section

add_to_stacks 07BI "The maximal ideal `𝔪_R` of a local ring `R`, realised as the ideal of
  nonunits." IsLocalRing.maximalIdeal
