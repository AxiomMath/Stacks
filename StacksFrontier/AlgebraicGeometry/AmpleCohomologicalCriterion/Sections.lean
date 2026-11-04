module

public import StacksFrontier.Homology.DerivedIndexing.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Vanishing `H¹` makes global sections surjective

[Stacks, Tag 0B5P] uses its cohomological hypothesis exactly once, and in one shape: from a short
exact sequence `0 → A → B → C → 0` of `𝒪_X`-modules with `H¹(X, A) = 0`, the map on global
sections `Γ(X, B) → Γ(X, C)` is surjective, so that a prescribed section of `C` can be lifted to
`B`. That implication was not available.

What was available is its two halves, separately. `CategoryTheory.DeltaFunctor` — the long exact
cohomology sequence, [Stacks, Tag 010Q] — carries `exact_δ₁`, the exactness of
`Fⁿ(X₂) → Fⁿ(X₃) → Fⁿ⁺¹(X₁)`, but only its two *dual* consequences are drawn there
(`epi_δ_of_map_f_eq_zero`, `mono_δ_of_map_g_eq_zero`); and
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives` builds a δ-functor out of any
additive functor from a category with enough injectives, but had never been instantiated at
`SheafOfModules.evaluation`.

This file draws the consequence and performs the instantiation, at the sections functor
`SheafOfModules.evaluation X.ringCatSheaf (op U)` of an open of a scheme — the functor whose
right derived functors the statement of Tag 0B5P is written with.

## Main results

* `Stacks.AmpleCohomologicalCriterion.epi_map_g_of_isZero`: for any cohomological δ-functor,
  `Fⁿ⁺¹(X₁) = 0` implies that `Fⁿ(X₂) → Fⁿ(X₃)` is an epimorphism. The general statement, from
  `exact_δ₁`.
* `Stacks.AmpleCohomologicalCriterion.sectionsDeltaFunctor`: the long exact cohomology sequence of
  an open `U` of a scheme, in the `ModuleCat Γ(X, U)`-valued spelling, with degree-`n` part
  `(SheafOfModules.evaluation X.ringCatSheaf (op U)).rightDerived n`.
* `Stacks.AmpleCohomologicalCriterion.epi_rightDerived_zero_map_g` and
  `Stacks.AmpleCohomologicalCriterion.epi_evaluation_map_g`: if `H¹(U, A) = 0` for a short exact
  sequence `0 → A → B → C → 0` of `𝒪_X`-modules, then `Γ(U, B) → Γ(U, C)` is an epimorphism —
  stated both for `rightDerived 0` and, after `Functor.rightDerivedZeroIsoSelf`, for the sections
  functor itself.
* `Stacks.AmpleCohomologicalCriterion.surjective_evaluation_map_g`: the same on elements.

## Implementation notes

**Why the statements are at the `SheafOfModules.{u} X.ringCatSheaf` spelling and not at
`X.Modules`.** `AlgebraicGeometry.Scheme.Modules` is a semireducible `def` for
`SheafOfModules.{u} X.ringCatSheaf`, so the two carry category instances that are equal but not
syntactically identical, and an `Additive` instance supplied for one is not found for the other.
Writing `DeltaFunctor X.Modules _` as the type of `sectionsDeltaFunctor` makes the elaborator ask
for `(SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive` at the `X.Modules` instance and
fail, with the local instance in scope. The unfolded spelling is used throughout; consumers
working with `X.Modules` reach these statements by definitional unfolding, which `exact` performs
and instance search does not.

**The two typeclass gaps, and how they are closed.** `EnoughInjectives` and
`HasInjectiveResolutions` for a scheme's sheaves of modules need no local instance at this pin:
Mathlib has `IsGrothendieckAbelian X.Modules` and
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives`, and instance search traverses the chain
at both spellings. The two that are *not* instances are
`(SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive`, supplied below by unfolding
`SheafOfModules.evaluation` into a composite of additive functors, and
`HasDerivedCategory`, supplied by `HasDerivedCategory.standard` as a local instance — the
δ-functor is built through the bounded-below derived category, which is the price recorded in
`StacksFrontier/AlgebraicGeometry/SectionsExact/Discharge.lean`.

**Degree zero.** `Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor`
holds by `rfl`, so the δ-functor's degree-`n` part *is* `rightDerived n` and no transport is
needed in any degree; the only transport in the file is
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`, which identifies degree zero with the sections
functor itself and whose one side condition — left exactness of sections — is already an instance
for `SheafOfModules.evaluation`.

## References

* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AmpleCohomologicalCriterion

/-- **If `Fⁿ⁺¹(X₁)` vanishes then `Fⁿ(X₂) → Fⁿ(X₃)` is an epimorphism.** The connecting
morphism `δ : Fⁿ(X₃) ⟶ Fⁿ⁺¹(X₁)` is zero because its target is, and
`CategoryTheory.DeltaFunctor.exact_δ₁` says `Fⁿ(X₂) → Fⁿ(X₃) → Fⁿ⁺¹(X₁)` is exact. -/
theorem epi_map_g_of_isZero {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : DeltaFunctor A B) {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)
    (h : IsZero ((F.functor (n + 1)).obj S.X₁)) : Epi ((F.functor n).map S.g) :=
  (ShortComplex.exact_iff_epi _ (h.eq_of_tgt _ 0)).1 (F.exact_δ₁ hS n)

section Scheme

attribute [local instance] HasDerivedCategory.standard

/-- Module-valued sections over an open of a scheme are an additive functor. The instance is not
found without unfolding `SheafOfModules.evaluation` into the composite of the forgetful functor
to presheaves of modules with evaluation of presheaves. -/
instance evaluation_additive (X : Scheme.{u}) (U : Opens X.carrier) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

/-- **The long exact cohomology sequence over an open of a scheme**, with values in
`ModuleCat Γ(X, U)`: the right derived δ-functor of the sections functor
`SheafOfModules.evaluation X.ringCatSheaf (op U)`. -/
noncomputable def sectionsDeltaFunctor (X : Scheme.{u}) (U : Opens X.carrier) :
    DeltaFunctor (SheafOfModules.{u} X.ringCatSheaf)
      (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U))) :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (SheafOfModules.evaluation X.ringCatSheaf (op U))

/-- The degree-`n` part of `Stacks.AmpleCohomologicalCriterion.sectionsDeltaFunctor` is the `n`-th
right derived functor of sections. -/
theorem sectionsDeltaFunctor_functor (X : Scheme.{u}) (U : Opens X.carrier) (n : ℕ) :
    (sectionsDeltaFunctor X U).functor n =
      (SheafOfModules.evaluation X.ringCatSheaf (op U)).rightDerived n :=
  rfl

/-- **Vanishing `H¹` of the subobject makes degree-zero cohomology surjective.** -/
theorem epi_rightDerived_zero_map_g (X : Scheme.{u}) (U : Opens X.carrier)
    {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact)
    (h : IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op U)).rightDerived 1).obj S.X₁)) :
    Epi (((SheafOfModules.evaluation X.ringCatSheaf (op U)).rightDerived 0).map S.g) :=
  epi_map_g_of_isZero (sectionsDeltaFunctor X U) hS 0 h

/-- **Vanishing `H¹` makes global sections surjective**, in the shape [Stacks, Tag 0B5P]
consumes: for a short exact sequence `0 → A → B → C → 0` of `𝒪_X`-modules with `H¹(U, A) = 0`,
the map `Γ(U, B) ⟶ Γ(U, C)` is an epimorphism. Degree zero is identified with the sections
functor by `CategoryTheory.Functor.rightDerivedZeroIsoSelf`, whose naturality square transports
the epimorphism. -/
theorem epi_evaluation_map_g (X : Scheme.{u}) (U : Opens X.carrier)
    {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact)
    (h : IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op U)).rightDerived 1).obj S.X₁)) :
    Epi ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map S.g) := by
  have := epi_rightDerived_zero_map_g X U hS h
  let φ := (Functor.rightDerivedZeroIsoSelf (SheafOfModules.evaluation X.ringCatSheaf (op U))).hom
  have : Epi (φ.app S.X₂ ≫ (SheafOfModules.evaluation X.ringCatSheaf (op U)).map S.g) := by
    rw [← φ.naturality S.g]
    exact epi_comp _ _
  exact epi_of_epi (φ.app S.X₂) _

/-- `Stacks.AmpleCohomologicalCriterion.epi_evaluation_map_g` on elements: every section of `C`
over `U` is the image of a section of `B` over `U`. -/
theorem surjective_evaluation_map_g (X : Scheme.{u}) (U : Opens X.carrier)
    {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact)
    (h : IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op U)).rightDerived 1).obj S.X₁)) :
    Function.Surjective
      ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map S.g).hom := by
  have := epi_evaluation_map_g X U hS h
  rwa [← ModuleCat.epi_iff_surjective]

end Scheme

end Stacks.AmpleCohomologicalCriterion

end
