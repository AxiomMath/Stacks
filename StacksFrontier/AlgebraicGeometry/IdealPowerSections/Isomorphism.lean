/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.IdealPowerSectionsSurjective.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.IdealPowerQuotientIso

/-!
# Sections over the complement of `V(I)` in an affine scheme

Let `A` be a commutative ring, `I ⊆ A` a finitely generated ideal and `M` an `A`-module, and
write `Mₙ = {x ∈ M | Iⁿ x = 0}`. This file collects the three assertions about the canonical maps
`colim_n Hom_A(I ^ n, M) → Γ(Spec(A) \ V(I), M̃)` and
`colim_n Hom_A(I ^ n, M / Mₙ) → Γ(Spec(A) \ V(I), M̃)` into one statement.

## Main results

* `canonicalMapToSections_injective_and_isIso`: the first canonical map is injective, it is an
  isomorphism if no nonzero element of `M` is annihilated by `I`, and the second canonical map is
  an isomorphism.

## References

* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.AlgebraicGeometry.IdealPowerSections

variable (A : Type u) [CommRing A] (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]

/-- Let `I` be a finitely generated ideal of `A` and `M` an `A`-module. The canonical map
`colim_n Hom_A(I ^ n, M) → Γ(Spec(A) \ V(I), M̃)` is injective; it is an isomorphism if
`I x = 0` implies `x = 0` for every `x ∈ M`; and with `Mₙ = {x ∈ M | Iⁿ x = 0}` the canonical
map `colim_n Hom_A(I ^ n, M / Mₙ) → Γ(Spec(A) \ V(I), M̃)` is an isomorphism. -/
@[stacks 01PM "complete statement"]
public theorem canonicalMapToSections_injective_and_isIso (hI : I.FG) :
    Function.Injective (canonicalMapToSections A I M) ∧
      ((∀ x : M, (∀ a ∈ I, a • x = 0) → x = 0) → IsIso (canonicalMapToSections A I M)) ∧
      IsIso (canonicalMapModuloAnnihilator A I M) :=
  ⟨canonicalMapToSections_injective A I M hI,
    fun htors => (ConcreteCategory.isIso_iff_bijective _).mpr
      (canonicalMapToSections_bijective A I M hI htors),
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (canonicalMapModuloAnnihilator_bijective A M I hI)⟩

end Stacks.AlgebraicGeometry.IdealPowerSections

end
