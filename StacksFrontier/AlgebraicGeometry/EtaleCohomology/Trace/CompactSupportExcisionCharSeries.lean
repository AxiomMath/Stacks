module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusCharSeries
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportClosedRestrictionCharSeries
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportOpenRestrictionCharSeries

/-!
# Excision for `det(1 - π^* T | RΓ_c)`

Let `X` be a scheme over a finite field `k` with a compactification `j : X ⟶ X̄`, `i : Z ⟶ X` a
closed immersion with open complement `j_U : U ⟶ X`, and `F` a sheaf of `Λ`-modules on `X_étale`.
If `RΓ_c(U_k̄, F|_U)` and `RΓ_c(Z_k̄, F|_Z)` are perfect, for the compactifications of `U` and `Z`
induced by `j`, then `RΓ_c(X_k̄, F)` is perfect and

```
det(1 - π_X^* T | RΓ_c(X_k̄, F))
  = det(1 - π_U^* T | RΓ_c(U_k̄, F|_U)) · det(1 - π_Z^* T | RΓ_c(Z_k̄, F|_Z)).
```

This is the dévissage step of [Stacks, Tag 03UZ]: the excision sequence
`0 → j_{U!} j_U⁻¹ F → F → i_* i⁻¹ F → 0` (Tag 095L), the multiplicativity of the characteristic
series along it, and the identifications `RΓ_c(X_k̄, j_{U!} -) ≅ RΓ_c(U_k̄, -)` and
`RΓ_c(X_k̄, i_* -) ≅ RΓ_c(Z_k̄, -)` compatible with Frobenius.

## Main results

* `Stacks.EtaleCohomology.singlePlusObjMapIso`: placing in degree `0` commutes with an additive
  functor.
* `Stacks.EtaleCohomology.perfectDerivedCharSeries_canonicalCompactSupportFrobenius_excision`:
  excision for the characteristic series of the Frobenius on compactly supported cohomology.

## Implementation notes

The canonical Frobenius action is defined for the model `HasDerivedCategory.standard` of the
derived category, so the statements here are too.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- Placing an object in degree `0` commutes with an additive functor, in bounded below
complexes. -/
def singlePlusObjMapIso {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] (Φ : C ⥤ D)
    [Φ.Additive] (G : C) :
    (Stacks.DerivedIndexing.singlePlusFunctor D 0).obj (Φ.obj G) ≅
      Φ.mapCochainComplexPlus.obj ((Stacks.DerivedIndexing.singlePlusFunctor C 0).obj G) :=
  ObjectProperty.isoMk _
    ((HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).app G).symm

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [QuasiCompact f] (j : CompactificationOf (Over.mk f))
  {Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (jU : U ⟶ X) [IsOpenImmersion jU]
  (hij : Set.range jU.base = (Set.range i.base)ᶜ)
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

include hij in
/-- **Excision for `det(1 - π^* T | RΓ_c)`.** If the compactly supported cohomologies of the
restrictions of `F` to the open `U` and the closed complement `Z` are perfect, so is that of `F`,
and its characteristic series is the product of theirs. -/
theorem perfectDerivedCharSeries_canonicalCompactSupportFrobenius_excision
    (F : EtaleModules.{u, 0} Λ X)
    (hU : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ (jU ≫ f) (j.restrictOpen jU) kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ U) 0).obj
          ((etaleModuleRestriction.{u, 0} Λ jU).obj F)))))
    (hZ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ (i ≫ f) (j.restrictClosed i) kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ Z) 0).obj
          ((etaleModuleInverseImage.{u, 0} Λ i).obj F))))) :
    ∃ hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ X) 0).obj F))),
      CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hX (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard
            ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ X) 0).obj F))) =
        CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hU (DerivedCategory.Plus.ι.map
            (canonicalCompactSupportFrobenius.{u, 0} Λ (jU ≫ f) (j.restrictOpen jU) kbar p q hcard
              ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ U) 0).obj
                ((etaleModuleRestriction.{u, 0} Λ jU).obj F)))) *
          CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hZ
            (DerivedCategory.Plus.ι.map
              (canonicalCompactSupportFrobenius.{u, 0} Λ (i ≫ f) (j.restrictClosed i) kbar p q
                hcard ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ Z) 0).obj
                  ((etaleModuleInverseImage.{u, 0} Λ i).obj F)))) := by
  obtain ⟨h, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage Λ i jU hij F
  set GU := (etaleModuleRestriction.{u, 0} Λ jU).obj F
  set GZ := (etaleModuleInverseImage.{u, 0} Λ i).obj F
  -- the open end
  have hU' := (isPerfect_compactSupportFrobeniusCohomology_restrictOpen_iff Λ f j jU kbar
    ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ U) 0).obj GU)).1 hU
  have hp₁ := isPerfect_compactSupportFrobeniusCohomology_of_iso Λ f j kbar
    (singlePlusObjMapIso (etaleModuleExtensionByZero.{u, 0} Λ jU) GU).symm hU'
  -- the closed end
  have hZ' := (isPerfect_compactSupportFrobeniusCohomology_restrictClosed_iff Λ f j i kbar
    ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ Z) 0).obj GZ)).1 hZ
  have hp₃ := isPerfect_compactSupportFrobeniusCohomology_of_iso Λ f j kbar
    (singlePlusObjMapIso (etaleModuleDirectImage.{u, 0} Λ i) GZ).symm hZ'
  -- the middle
  have hp₂ := isPerfect_compactSupportFrobeniusCohomology_single_X₂ Λ f j kbar hS hp₁ hp₃
  refine ⟨hp₂, ?_⟩
  refine (perfectDerivedCharSeries_canonicalCompactSupportFrobenius_single_X₂_eq_mul Λ f j kbar p q
    hcard hS hp₁ hp₂ hp₃).trans ?_
  congr 1
  · rw [perfectDerivedCharSeries_canonicalCompactSupportFrobenius_restrictOpen Λ f j jU kbar p q
      hcard _ hU hU']
    exact perfectDerivedCharSeries_canonicalCompactSupportFrobenius_congr Λ f j kbar p q hcard
      (singlePlusObjMapIso (etaleModuleExtensionByZero.{u, 0} Λ jU) GU) hp₁ hU'
  · rw [perfectDerivedCharSeries_canonicalCompactSupportFrobenius_restrictClosed Λ f j i kbar p q
      hcard _ hZ hZ']
    exact perfectDerivedCharSeries_canonicalCompactSupportFrobenius_congr Λ f j kbar p q hcard
      (singlePlusObjMapIso (etaleModuleDirectImage.{u, 0} Λ i) GZ) hp₃ hZ'

end Stacks.EtaleCohomology
