module

public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CompleteIntersection.Smooth
public import StacksFrontier.RingTheory.Syntomic.Defs

/-!
# Smooth ring maps are locally standard smooth and syntomic

Let `R → S` be a smooth ring map. Then `Spec(S)` is covered by standard opens `D(g)` with each
`S_g` standard smooth over `R`, and `R → S` is syntomic. The cover is
`Algebra.Smooth.exists_span_eq_top_isStandardSmooth`. For syntomicity: `R → S` is flat and of
finite presentation, and each fibre `κ(p) ⊗_R S` is smooth over the field `κ(p)`, hence a local
complete intersection over `κ(p)` by Lemma 00T5.

## References

* [Stacks Project, Tag 00TA](https://stacks.math.columbia.edu/tag/00TA)
-/

@[expose] public section

namespace Algebra.Smooth

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- A smooth algebra is syntomic. -/
theorem syntomic [Smooth R S] : Syntomic R S where
  isLocalCompleteIntersection_fiber p _ := isLocalCompleteIntersection_of_smooth _ _

/-- **Stacks 00TA.** Let `R → S` be a smooth ring map. There are `g ∈ S` whose standard opens
`D(g)` cover `Spec(S)` and such that each `S_g` is standard smooth over `R`. In particular
`R → S` is syntomic. -/
@[stacks 00TA "The cover by standard opens `D(g)`, `g ∈ s`, is `Ideal.span s = ⊤`. Syntomic is
`Algebra.Syntomic` (Definition 00SL); it is derived here directly from Lemma 00T5 on the fibres
rather than through Lemmas 00T7, 00SW and 00SO."]
theorem exists_span_eq_top_isStandardSmooth_and_syntomic [Smooth R S] :
    (∃ s : Set S, Ideal.span s = ⊤ ∧ ∀ g ∈ s, IsStandardSmooth R (Localization.Away g)) ∧
      Syntomic R S :=
  ⟨exists_span_eq_top_isStandardSmooth R S, syntomic R S⟩

end Algebra.Smooth
