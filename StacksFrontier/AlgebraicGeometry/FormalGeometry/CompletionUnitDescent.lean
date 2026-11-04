module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology

/-!
# Descending a map along the derived completion unit

Derived `I`-adic completion is a reflection of `D(A)` onto its derived `I`-complete objects
(`Stacks.Algebraization.adicCompletionFunctor`, with unit
`Stacks.Algebraization.adicCompletionUnit`). So a map `c : X ⟶ R` whose target is derived
`I`-complete factors through the unit at `X`, and does so in exactly one way.

This file defines that factorization, the canonical comparison `X^∧ ⟶ R`, and records its two
characterizing clauses.

## Main results

* `Stacks.Algebraization.completionUnitCompEquiv` — precomposition with the completion unit,
  as a bijection onto the maps out of `X`.
* `Stacks.Algebraization.completionDescent` — the map `X^∧ ⟶ R` induced by `c : X ⟶ R` for a
  derived `I`-complete target `R`.
* `Stacks.Algebraization.completionDescent_unit` — its defining clause: composing it with the
  completion unit at `X` returns `c`.
* `Stacks.Algebraization.completionDescent_unique` — that clause determines it.
* `Stacks.Algebraization.eq_completionDescent` — the same, read as a rewriting rule.
* `Stacks.Algebraization.isIso_completionDescent_iff` — it is invertible exactly when the
  completion of `c` is.

## References

* [Stacks Project, Tag 0922](https://stacks.math.columbia.edu/tag/0922)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A]

/-- **Precomposition with the completion unit, as a bijection** from the maps `X^∧ ⟶ R` onto the
maps `X ⟶ R`, for a derived `I`-complete target `R`. -/
public def completionUnitCompEquiv (I : Ideal A) (hI : I.FG)
    (X : DerivedCategory (ModuleCat.{u} A)) {R : DerivedCategory (ModuleCat.{u} A)}
    (hR : IsDerivedComplete I R) :
    ((adicCompletionFunctor A I hI).obj X ⟶ R) ≃ (X ⟶ R) :=
  Equiv.ofBijective _ (completionUnit_comp_bijective I hI X R hR)

/-- `Stacks.Algebraization.completionUnitCompEquiv` sends `g` to its precomposition with the
completion unit at `X`. -/
@[simp] public theorem completionUnitCompEquiv_apply (I : Ideal A) (hI : I.FG)
    (X : DerivedCategory (ModuleCat.{u} A)) {R : DerivedCategory (ModuleCat.{u} A)}
    (hR : IsDerivedComplete I R) (g : (adicCompletionFunctor A I hI).obj X ⟶ R) :
    completionUnitCompEquiv I hI X hR g = (adicCompletionUnit A I hI).app X ≫ g := rfl

/-- **The map induced by `c : X ⟶ R` on the derived `I`-adic completion of `X`**, for a derived
`I`-complete target `R`.

Derived completion is a reflection onto the derived `I`-complete objects, so precomposition with
the completion unit at `X` is a bijection from `X^∧ ⟶ R` onto `X ⟶ R`
(`Stacks.Algebraization.completionUnit_comp_bijective`); this is the inverse image of `c` under
that bijection, so no choice is involved.

It is characterized by `Stacks.Algebraization.completionDescent_unit` together with
`Stacks.Algebraization.completionDescent_unique`: it is the unique map `X^∧ ⟶ R` whose composite
with the completion unit at `X` is `c`. -/
public def completionDescent (I : Ideal A) (hI : I.FG)
    {X R : DerivedCategory (ModuleCat.{u} A)} (hR : IsDerivedComplete I R) (c : X ⟶ R) :
    (adicCompletionFunctor A I hI).obj X ⟶ R :=
  (completionUnitCompEquiv I hI X hR).symm c

/-- **The defining clause of `Stacks.Algebraization.completionDescent`**: it is a factorization of
`c` through the completion unit at `X`. -/
public theorem completionDescent_unit (I : Ideal A) (hI : I.FG)
    {X R : DerivedCategory (ModuleCat.{u} A)} (hR : IsDerivedComplete I R) (c : X ⟶ R) :
    (adicCompletionUnit A I hI).app X ≫ completionDescent I hI hR c = c :=
  (completionUnitCompEquiv I hI X hR).apply_symm_apply c

/-- **`Stacks.Algebraization.completionDescent` is the only factorization of `c` through the
completion unit**, because precomposition with the unit is injective on maps into a derived
complete object. -/
public theorem completionDescent_unique (I : Ideal A) (hI : I.FG)
    {X R : DerivedCategory (ModuleCat.{u} A)} (hR : IsDerivedComplete I R) (c : X ⟶ R)
    (u : (adicCompletionFunctor A I hI).obj X ⟶ R)
    (hu : (adicCompletionUnit A I hI).app X ≫ u = c) :
    u = completionDescent I hI hR c :=
  (completionUnitCompEquiv I hI X hR).injective
    (by rw [completionUnitCompEquiv_apply, hu, completionUnitCompEquiv_apply,
      completionDescent_unit])

/-- **`Stacks.Algebraization.completionDescent` agrees with the explicit formula**: the completion
of `c`, followed by the inverse of the completion unit at the complete object `R`. -/
public theorem completionDescent_eq (I : Ideal A) (hI : I.FG)
    {X R : DerivedCategory (ModuleCat.{u} A)} (hR : IsDerivedComplete I R) (c : X ⟶ R) :
    letI : IsIso ((adicCompletionUnit A I hI).app R) :=
      isIso_completionUnit_of_derivedComplete I hI R hR
    completionDescent I hI hR c =
      (adicCompletionFunctor A I hI).map c ≫ inv ((adicCompletionUnit A I hI).app R) := by
  let : IsIso ((adicCompletionUnit A I hI).app R) :=
    isIso_completionUnit_of_derivedComplete I hI R hR
  refine ((completionDescent_unique I hI hR c _ ?_)).symm
  have hnat : (adicCompletionUnit A I hI).app X ≫ (adicCompletionFunctor A I hI).map c =
      c ≫ (adicCompletionUnit A I hI).app R := by
    simpa using ((adicCompletionUnit A I hI).naturality c).symm
  rw [← Category.assoc, hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- `Stacks.Algebraization.completionDescent_unique` as a rewriting rule. -/
public theorem eq_completionDescent (I : Ideal A) (hI : I.FG)
    {X R : DerivedCategory (ModuleCat.{u} A)} (hR : IsDerivedComplete I R)
    {u : (adicCompletionFunctor A I hI).obj X ⟶ R} :
    (adicCompletionUnit A I hI).app X ≫ u =
      (adicCompletionUnit A I hI).app X ≫ completionDescent I hI hR
        ((adicCompletionUnit A I hI).app X ≫ u) := by
  rw [completionDescent_unit]

/-- **The unit-induced comparison is invertible exactly when the completion of `c` is.** -/
public theorem isIso_completionDescent_iff (I : Ideal A) (hI : I.FG)
    {X R : DerivedCategory (ModuleCat.{u} A)} (hR : IsDerivedComplete I R) (c : X ⟶ R) :
    IsIso (completionDescent I hI hR c) ↔ IsIso ((adicCompletionFunctor A I hI).map c) := by
  let : IsIso ((adicCompletionUnit A I hI).app R) :=
    isIso_completionUnit_of_derivedComplete I hI R hR
  rw [completionDescent_eq I hI hR c]
  exact ⟨fun _ ↦ IsIso.of_isIso_comp_right _ (inv ((adicCompletionUnit A I hI).app R)),
    fun _ ↦ inferInstance⟩

/-- The unit-induced comparison is invertible as soon as the completion of `c` is. -/
public theorem isIso_completionDescent (I : Ideal A) (hI : I.FG)
    {X R : DerivedCategory (ModuleCat.{u} A)} (hR : IsDerivedComplete I R) (c : X ⟶ R)
    [IsIso ((adicCompletionFunctor A I hI).map c)] :
    IsIso (completionDescent I hI hR c) :=
  (isIso_completionDescent_iff I hI hR c).2 inferInstance

end Stacks.Algebraization

end
