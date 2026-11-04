module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportClosedRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactCharSeries

/-!
# `det(1 - π^* T | RΓ_c)` of a closed subscheme

Let `j : X ⟶ X̄` be a compactification of `X` over a finite field `k` and `i : Z ⟶ X` a closed
immersion. The identification `RΓ_c(Z_k̄, L) ≅ RΓ_c(X_k̄, i_* L)` of
`Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyClosedImmersionIso`, for the induced
compactification of `Z`, commutes with the canonical Frobenius actions. Hence perfectness of the
two sides is equivalent, and their characteristic series `det(1 - π^* T | -)` agree.

## Main results

* `isPerfect_compactSupportFrobeniusCohomology_restrictClosed_iff`: `RΓ_c(Z_k̄, L)` is perfect
  if and only if `RΓ_c(X_k̄, i_* L)` is.
* `perfectDerivedCharSeries_canonicalCompactSupportFrobenius_restrictClosed`:
  `det(1 - π_Z^* T | RΓ_c(Z_k̄, L)) = det(1 - π_X^* T | RΓ_c(X_k̄, i_* L))`.

## Implementation notes

The identification and the canonical Frobenius action are defined for the model
`HasDerivedCategory.standard` of the derived category, so the statements here are too.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [QuasiCompact f] (j : CompactificationOf (Over.mk f)) {Z : Scheme.{u}}
  (i : Z ⟶ X) [IsClosedImmersion i] (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- `RΓ_c(Z_k̄, L)` is perfect if and only if `RΓ_c(X_k̄, i_* L)` is. -/
theorem isPerfect_compactSupportFrobeniusCohomology_restrictClosed_iff
    (L : CochainComplex.Plus (EtaleModules.{u, r} Λ Z)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, r} Λ (i ≫ f) (j.restrictClosed i) kbar L)) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar
          ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj L))) :=
  have e := DerivedCategory.Plus.ι.mapIso
    (compactSupportFrobeniusCohomologyClosedImmersionIso Λ f j i kbar L)
  ⟨StacksDraft.Perfect.isPerfect_of_iso e.symm, StacksDraft.Perfect.isPerfect_of_iso e⟩

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **`det(1 - π_Z^* T | RΓ_c(Z_k̄, L)) = det(1 - π_X^* T | RΓ_c(X_k̄, i_* L))`**, for the
compactification of `Z` induced by one of `X`. -/
theorem perfectDerivedCharSeries_canonicalCompactSupportFrobenius_restrictClosed
    (L : CochainComplex.Plus (EtaleModules.{u, r} Λ Z))
    (hp : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ (i ≫ f) (j.restrictClosed i) kbar L)))
    (hp' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar
        ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj L)))) :
    CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp (DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, r} Λ (i ≫ f) (j.restrictClosed i) kbar p q hcard L)) =
      CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp' (DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard
          ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj L))) :=
  CategoryTheory.FilteredDerived.perfectDerivedCharSeries_congr Λ hp hp'
    (DerivedCategory.Plus.ι.mapIso (compactSupportFrobeniusCohomologyClosedImmersionIso Λ f j i
      kbar L)) _ _ (by
        rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp,
          compactSupportFrobeniusCohomologyClosedImmersionIso_hom_frobenius])

end Stacks.EtaleCohomology
