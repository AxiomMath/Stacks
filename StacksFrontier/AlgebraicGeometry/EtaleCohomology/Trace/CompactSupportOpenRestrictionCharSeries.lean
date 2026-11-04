module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportOpenRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactCharSeries

/-!
# `det(1 - π^* T | RΓ_c)` of an open subscheme

Let `j : X ⟶ X̄` be a compactification of `X` over a finite field `k` and `j_U : U ⟶ X` an open
immersion. The identification `RΓ_c(U_k̄, K) ≅ RΓ_c(X_k̄, j_{U!} K)` of
`Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyRestrictOpenIso`, for the induced
compactification `j ∘ j_U` of `U`, commutes with the canonical Frobenius actions. Hence perfectness
of the two sides is equivalent, and their characteristic series
`det(1 - π^* T | -)` agree. This is the open half of the dévissage of [Stacks, Tag 03UZ] along the
excision sequence `0 → j_{U!} j_U⁻¹ F → F → i_* i⁻¹ F → 0`.

## Main results

* `Stacks.EtaleCohomology.isPerfect_compactSupportFrobeniusCohomology_restrictOpen_iff`.
* `Stacks.EtaleCohomology.perfectDerivedCharSeries_canonicalCompactSupportFrobenius_restrictOpen`.

## Implementation notes

The identification and the canonical Frobenius action are defined for the model
`HasDerivedCategory.standard` of the derived category, so the statements here are too.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) {U : Scheme.{u}} (jU : U ⟶ X)
  [IsOpenImmersion jU] (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [Fintype k] in
/-- `RΓ_c(U_k̄, K)` is perfect if and only if `RΓ_c(X_k̄, j_{U!} K)` is. -/
theorem isPerfect_compactSupportFrobeniusCohomology_restrictOpen_iff
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ (jU ≫ f) (j.restrictOpen jU) kbar K)) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
          ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj K))) :=
  have e := DerivedCategory.Plus.ι.mapIso
    (compactSupportFrobeniusCohomologyRestrictOpenIso Λ f j jU kbar K)
  ⟨StacksDraft.Perfect.isPerfect_of_iso e.symm, StacksDraft.Perfect.isPerfect_of_iso e⟩

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **`det(1 - π_U^* T | RΓ_c(U_k̄, K)) = det(1 - π_X^* T | RΓ_c(X_k̄, j_{U!} K))`**, for the
compactification of `U` induced by one of `X`. -/
theorem perfectDerivedCharSeries_canonicalCompactSupportFrobenius_restrictOpen
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U))
    (hp : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ (jU ≫ f) (j.restrictOpen jU) kbar K)))
    (hp' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj K)))) :
    CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp (DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, 0} Λ (jU ≫ f) (j.restrictOpen jU) kbar p q hcard K)) =
      CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp' (DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard
          ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj K))) :=
  CategoryTheory.FilteredDerived.perfectDerivedCharSeries_congr Λ hp hp'
    (DerivedCategory.Plus.ι.mapIso (compactSupportFrobeniusCohomologyRestrictOpenIso Λ f j jU
      kbar K)) _ _ (by
        rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp,
          compactSupportFrobeniusCohomologyRestrictOpenIso_hom_frobenius])

end Stacks.EtaleCohomology
