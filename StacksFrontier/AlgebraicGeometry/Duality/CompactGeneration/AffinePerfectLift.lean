module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.PerfectIsCompactCover
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.Homology.DerivedCategory.ModelComparison

/-!
# Lifting a perfect complex from a quasi-compact open of an affine scheme

Let `j : X ⟶ Spec A` be an open immersion with `X` quasi-compact and `N` a perfect complex of
`𝒪_X`-modules. There is a perfect complex `Q` of `𝒪_{Spec A}`-modules with `j^*Q ≅ N ⊕ N[1]` in
`D(𝒪_X)`. This is [Stacks, Tag 08EK] read through [Stacks, Tag 09M1]: in `D_QCoh` of the open
`D(f₁) ∪ … ∪ D(f_r) = j(X)` the perfect object `N` is compact, its lift
`Stacks.Duality.QcqsGeneration.exists_isCompactObject_restrict_iso_biprod_shift` is compact,
hence perfect.

The statements are at the level of complexes, so that they hold at every model of the derived
category; the compactness argument runs at the locally small model.

## Main results

* `Stacks.Duality.QcqsGeneration.exists_isPerfectComplex_restrict_iso_biprod_shift`: the lift
  along `D(f₁) ∪ … ∪ D(f_r) ⊆ Spec A`.
* `Stacks.Duality.QcqsGeneration.exists_isPerfectComplex_pullback_iso_biprod_shift`: the lift
  along any quasi-compact open immersion into `Spec A`, at any model.

## References

* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w z u

namespace StacksDraft.DerivedModel

variable {C : Type*} [Category C] [Abelian C]

/-- **An isomorphism of localized complexes at one model gives one at any other model.** -/
theorem nonempty_Q_iso_of_nonempty_Q_iso (h₁ : HasDerivedCategory.{w} C)
    (h₂ : HasDerivedCategory.{z} C) {K L : CochainComplex C ℤ}
    (e : Nonempty ((@DerivedCategory.Q C _ _ h₁).obj K ≅ (@DerivedCategory.Q C _ _ h₁).obj L)) :
    Nonempty ((@DerivedCategory.Q C _ _ h₂).obj K ≅ (@DerivedCategory.Q C _ _ h₂).obj L) :=
  e.map fun e => ((modelCompQIso h₁ h₂).app K).symm ≪≫ (modelEquiv h₁ h₂).functor.mapIso e ≪≫
    (modelCompQIso h₁ h₂).app L

end StacksDraft.DerivedModel

namespace Stacks.Duality.QcqsGeneration

open Stacks.Duality.OpenImmersion Stacks.Koszul.Truncation

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- The cohomology sheaves of a perfect complex on a scheme are quasi-coherent, at the standard
model: `AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_of_isPerfect`. -/
theorem isQuasicoherent_homology_Q_of_isPerfectComplex_standard {X : Scheme.{u}}
    (E : CochainComplex X.Modules ℤ)
    (hE : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) E) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj (DerivedCategory.Q.obj E)).IsQuasicoherent :=
  AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_of_isPerfect X
    (DerivedCategory.Q.obj E) (RingedSpace.IsPerfectComplex.isPerfect.{u, u + 1} hE) i

end Standard

/-- **The cohomology sheaves of a perfect complex on a scheme are quasi-coherent**, at every
model of the derived category: the standard-model statement, moved along the identification of
both cohomology functors with the cohomology of the complex. -/
theorem isQuasicoherent_homology_Q_of_isPerfectComplex {X : Scheme.{u}}
    [HasDerivedCategory.{w} X.Modules] (E : CochainComplex X.Modules ℤ)
    (hE : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) E) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj (DerivedCategory.Q.obj E)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((@DerivedCategory.homologyFunctorFactors _ _ _ (HasDerivedCategory.standard X.Modules) i).app
      E ≪≫ ((DerivedCategory.homologyFunctorFactors X.Modules i).app E).symm)
    (isQuasicoherent_homology_Q_of_isPerfectComplex_standard E hE i)

variable {A : Type u} [CommRing A]

/-- **[Stacks, Tag 08EK] for perfect complexes on `D(f₁) ∪ … ∪ D(f_r)`.** Let
`W = D(f₁) ∪ … ∪ D(f_r) ⊆ Spec A` and `N` a perfect complex of `𝒪_W`-modules. There is a perfect
complex `Q` of `𝒪_{Spec A}`-modules with `Q|_W ≅ N ⊕ N[1]` in `D(𝒪_W)` (locally small model).

`N` has quasi-coherent cohomology and is compact in `D_QCoh(𝒪_W)` ([Stacks, Tag 09M1]); its lift
`exists_isCompactObject_restrict_iso_biprod_shift` is compact in `D_QCoh(𝒪_{Spec A})`, hence
perfect ([Stacks, Tag 09M1]), so represented by a perfect complex. -/
theorem exists_isPerfectComplex_restrict_iso_biprod_shift {r : ℕ} (f : Fin r → A)
    (N : CochainComplex (openComplement f).toScheme.Modules ℤ)
    (hN : RingedSpace.IsPerfectComplex (X := (openComplement f).toScheme.toRingedSpace) N) :
    ∃ Q₀ : CochainComplex (Spec (CommRingCat.of A)).Modules ℤ,
      RingedSpace.IsPerfectComplex (X := (Spec (CommRingCat.of A)).toRingedSpace) Q₀ ∧
        Nonempty (DerivedCategory.Q.obj
            (((Scheme.Modules.restrictFunctor (openComplement f).ι).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj Q₀) ≅
          DerivedCategory.Q.obj (N ⊞ N⟦(1 : ℤ)⟧)) := by
  have : QuasiSeparatedSpace (openComplement f).toScheme :=
    quasiSeparatedSpace_of_quasiSeparated (openComplement f).ι
  let P : Stacks.Duality.quasiCoherentDerivedCategory (openComplement f).toScheme :=
    ⟨DerivedCategory.Q.obj N, fun i => isQuasicoherent_homology_Q_of_isPerfectComplex N hN i⟩
  have hPc : IsCompactObject.{u} P :=
    Stacks.Duality.PerfectCompact.isCompactObject_of_isPerfect _ P hN.isPerfect
  obtain ⟨Q, hQc, ⟨e⟩⟩ := exists_isCompactObject_restrict_iso_biprod_shift f P hPc
  obtain ⟨Q₀, hQ₀, ⟨eQ⟩⟩ :=
    Stacks.Duality.SupportedGeneration.isPerfect_of_isCompactObject _ Q hQc
  let ι := (DerivedCategoryB.derivedCategoryB (A := (openComplement f).toScheme.Modules)
    (SheafOfModules.isQuasicoherent (openComplement f).toScheme.ringCatSheaf)).ι
  refine ⟨Q₀, hQ₀, ⟨?_⟩⟩
  exact ((Scheme.Modules.restrictFunctor (openComplement f).ι).mapDerivedCategoryFactors.app
      Q₀).symm ≪≫ (derivedRestrict (openComplement f).ι).mapIso eQ ≪≫
    ((restrictedDerivedRestrictCompιIso (openComplement f).ι).app Q).symm ≪≫ ι.mapIso e ≪≫
    ι.mapBiprod _ _ ≪≫ biprod.mapIso (Iso.refl _) ((ι.commShiftIso (1 : ℤ)).app P) ≪≫
    biprod.mapIso (Iso.refl _) ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app N).symm ≪≫
    (DerivedCategory.Q.mapBiprod N (N⟦(1 : ℤ)⟧)).symm

/-- **[Stacks, Tag 08EK] for perfect complexes on a quasi-compact open of `Spec A`.** Let
`j : X ⟶ Spec A` be an open immersion with `X` quasi-compact and `N` a perfect complex of
`𝒪_X`-modules. There is a perfect complex `Q` of `𝒪_{Spec A}`-modules with `j^*Q ≅ N ⊕ N[1]` in
`D(𝒪_X)`, at any model of the derived category.

The image of `j` is an open `D(f₁) ∪ … ∪ D(f_r)`, isomorphic to `X` over `Spec A`; the lift is
`exists_isPerfectComplex_restrict_iso_biprod_shift` there, moved to `X` along the isomorphism. -/
theorem exists_isPerfectComplex_pullback_iso_biprod_shift {X : Scheme.{u}}
    (j : X ⟶ Spec (CommRingCat.of A)) [IsOpenImmersion j] [CompactSpace X]
    [HasDerivedCategory.{w} X.Modules] (N : CochainComplex X.Modules ℤ)
    (hN : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) N) :
    ∃ Q₀ : CochainComplex (Spec (CommRingCat.of A)).Modules ℤ,
      RingedSpace.IsPerfectComplex (X := (Spec (CommRingCat.of A)).toRingedSpace) Q₀ ∧
        Nonempty (DerivedCategory.Q.obj
            (((Scheme.Modules.pullback j).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q₀) ≅
          DerivedCategory.Q.obj (N ⊞ N⟦(1 : ℤ)⟧)) := by
  have hcpt : IsCompact (Set.range j.base)ᶜᶜ := by
    rw [compl_compl]
    exact isCompact_range j.continuous
  obtain ⟨r, f, hf⟩ := Stacks.Duality.Supported.exists_coe_openComplement_eq_compl
    (A := A) (Set.range j.base)ᶜ j.isOpenEmbedding.isOpen_range.isClosed_compl hcpt
  have hrange : Set.range j.base = Set.range (openComplement f).ι.base := by
    rw [Scheme.Opens.range_ι, hf, compl_compl]
  let e : X ≅ (openComplement f).toScheme := IsOpenImmersion.isoOfRangeEq j _ hrange
  have he : e.hom ≫ (openComplement f).ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let N₁ := ((Scheme.Modules.restrictFunctor e.inv).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj N
  have hN₁ : RingedSpace.IsPerfectComplex (X := (openComplement f).toScheme.toRingedSpace) N₁ :=
    Stacks.Duality.SupportedGeneration.isPerfectComplex_restrictFunctor_of_isIso e.inv N hN
  obtain ⟨Q₀, hQ₀, ⟨eQ⟩⟩ := exists_isPerfectComplex_restrict_iso_biprod_shift f N₁ hN₁
  refine ⟨Q₀, hQ₀, ⟨?_⟩⟩
  let F := Scheme.Modules.restrictFunctor e.hom
  let Φ₁ : Scheme.Modules.restrictFunctor (openComplement f).ι ⋙ F ≅ Scheme.Modules.pullback j :=
    (Scheme.Modules.restrictFunctorComp e.hom (openComplement f).ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr he ≪≫ Scheme.Modules.restrictFunctorIsoPullback j
  let Φ₂ : Scheme.Modules.restrictFunctor e.inv ⋙ F ≅ 𝟭 _ :=
    (Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫ Scheme.Modules.restrictFunctorId
  let e₂ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N₁ ≅ N :=
    (Functor.mapHomologicalComplexCompIso Φ₂ (ComplexShape.up ℤ)).app N ≪≫
      (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app N
  let e₃ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (N₁ ⊞ N₁⟦(1 : ℤ)⟧) ≅ N ⊞ N⟦(1 : ℤ)⟧ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).mapBiprod _ _ ≪≫
      biprod.mapIso e₂
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).app N₁ ≪≫
          (shiftFunctor _ (1 : ℤ)).mapIso e₂)
  exact DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso Φ₁ (ComplexShape.up ℤ)).app Q₀).symm ≪≫
    (F.mapDerivedCategoryFactors.app _).symm ≪≫ F.mapDerivedCategory.mapIso eQ ≪≫
    F.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso e₃

end Stacks.Duality.QcqsGeneration

end
