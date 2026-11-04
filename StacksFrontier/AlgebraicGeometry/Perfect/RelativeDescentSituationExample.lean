module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentHomDescentIso
public import StacksFrontier.AlgebraicGeometry.SmallnessNecessary.Basic

/-!
# A relative descent situation that assumes nothing, and a term of its Hom-descent predicate

The situation of Stacks 0DI6 — `AlgebraicGeometry.RelativeDescentSituation` — and the conclusion
of Stacks 0DI7 — `AlgebraicGeometry.RelativeDescentSituation.HomDescent` — are both carried
around the development as hypotheses. Nothing in the tree exhibited a term of either, so no
statement about them could be told apart from a vacuous one. This file supplies both, from
declarations with no hypotheses.

The inverse system is the one of
`StacksFrontier/AlgebraicGeometry/SmallnessNecessary/Basic.lean`: a system of spectra of fields
indexed by the ordinals, with affine transition morphisms, whose limit is the empty scheme. Over
its fixed stage `S₀` take `X₀ = S₀` with the identity morphism, which is flat and of finite
presentation because it is an open immersion, quasi-compact and quasi-separated.

## Main definitions

* `AlgebraicGeometry.RelativeDescentSituation.example_ordinalSpectra`: **a relative descent
  situation constructed from no hypotheses.**

## Main results

* `AlgebraicGeometry.RelativeDescentSituation.exists_homDescent_example`: **the conclusion of
  Stacks 0DI7 has a term over that situation**, so the hypothesis `HomDescent K₀ L₀` of
  `AlgebraicGeometry.RelativeDescentSituation.homDescent_of_iso` and of
  `homDescent_shiftZero` is instantiable and not merely satisfiable in principle. The witness is
  a zero object, through `homDescent_of_isZero`, read back through `homDescent_shiftZero` so that
  both of those declarations are instantiated at once.

## References

* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RelativeDescentSituation

/-- A relative descent situation built from no hypotheses: the ordinal-indexed system of spectra
of fields of `StacksFrontier/AlgebraicGeometry/SmallnessNecessary/Basic.lean`, with `X₀ = S₀` and
the identity morphism over the fixed stage. -/
def example_ordinalSpectra : RelativeDescentSituation.{u + 1, u} Ordinal.{u} where
  descent := Stacks.AlgebraicGeometry.SmallnessNecessary.situation
  X₀ := Over.mk (𝟙 _)
  flat := inferInstanceAs (Flat (𝟙 _))
  finitePresentation := (⟨inferInstance, inferInstance, inferInstance⟩ : FinitePresentation (𝟙 _))

/-- **The conclusion of Stacks 0DI7 is instantiable.** Over the situation
`example_ordinalSpectra`, which assumes nothing, a zero first argument gives a term of
`HomDescent`, and reading it back through `homDescent_shiftZero` instantiates every binder of
that declaration and of `homDescent_of_iso` at once. -/
theorem exists_homDescent_example :
    ∃ K₀ L₀ : DerivedCategory
      (SheafOfModules.{u} (structureSheafRing example_ordinalSpectra.X₀.left.toRingedSpace)),
      example_ordinalSpectra.HomDescent K₀ L₀ := by
  obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := DerivedCategory
    (SheafOfModules.{u} (structureSheafRing (example_ordinalSpectra.{u}).X₀.left.toRingedSpace)))
  exact ⟨Z, Z, example_ordinalSpectra.homDescent_shiftZero Z Z
    (example_ordinalSpectra.homDescent_of_isZero Z _ hZ)⟩

end AlgebraicGeometry.RelativeDescentSituation

end
