module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.AffineLift

/-!
# Extending `F ⊕ F[1]` from a quasi-compact open of an affine scheme with support

Let `X` be an affine scheme, let `T ⊆ X` be closed with `X ∖ T` quasi-compact and let `U ⊆ X` be
a quasi-compact open. For every perfect object `F` of `D(𝒪_U)` supported on `T ∩ U`, the object
`F ⊕ F[1]` is the restriction of a perfect object of `D(𝒪_X)` supported on `T`.

## Main results

* `exists_isPerfectComplex_supported_restrict_iso_biprod_shift_of_isAffine`: for `X` affine,
  `F ⊕ F[1]` extends from `U` to a perfect complex on `X` with cohomology supported on `T`.

## References

* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace

universe u

namespace Stacks.DerivedQCoh.OpenLift

open Stacks.Cohomology.SiteModules Stacks.ExtensionByZero Stacks.Cohomology.PerfectComplexes
open _root_.Stacks.StrictlyPerfect Stacks.DerivedQCoh
open Stacks.Duality.OpenImmersion (derivedRestrict)

attribute [local instance 10000] HasDerivedCategory.standard

/-- Let `X` be an affine scheme, `T ⊆ X` a closed subset with
`X ∖ T` quasi-compact and `U ⊆ X` a quasi-compact open. For every perfect object `F` of
`D(𝒪_U)` whose cohomology is supported on `T ∩ U`, the object `F ⊕ F[1]` is the restriction of a
perfect object of `D(𝒪_X)` with cohomology supported on `T`: there is a perfect complex `P` of
`𝒪_X`-modules, with cohomology supported on `T`, whose degreewise restriction to `U` represents
`F ⊕ F[1]`. -/
@[stacks 08EK]
theorem exists_isPerfectComplex_supported_restrict_iso_biprod_shift_of_isAffine
    (X : Scheme.{u}) [IsAffine X]
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (F : DerivedCategory U.toScheme.Modules)
    (hF : IsPerfect (X := U.toScheme.toRingedSpace) F)
    (hFT : CohomologySupportedOn U.toScheme.ringCatSheaf (Subtype.val ⁻¹' T) F) :
    ∃ P : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) ℤ,
      IsPerfectComplex P ∧
      CohomologySupportedOn X.ringCatSheaf T (DerivedCategory.Q.obj P) ∧
      Nonempty ((F ⊞ F⟦(1 : ℤ)⟧) ≅ DerivedCategory.Q.obj
        (((AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace
          U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  classical
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
  obtain ⟨S, hS, hSeq⟩ := (isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen
    (X := X) (U := Tᶜ)).mp ⟨hTc, hT.isOpen_compl⟩
  let : Fintype S := hS.fintype
  let r := Fintype.card S
  let eS : Fin r ≃ S := (Fintype.equivFin S).symm
  let φ : Fin r → Γ(X, ⊤) := fun i => (eS i).val
  have hcov : ∀ x : X, x ∉ T → ∃ i, x ∈ X.basicOpen (φ i) := fun x hx => by
    obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.mp (hSeq.subset hx)
    exact ⟨eS.symm ⟨g, hg⟩, by simpa [φ] using hxg⟩
  have hdisj : ∀ i (x : X), x ∈ X.basicOpen (φ i) → x ∉ T := fun i x hx =>
    hSeq.symm.subset (Set.mem_iUnion₂.mpr ⟨(eS i).val, (eS i).property, hx⟩)
  have h08EJ : ∀ i, ∃ n : ℕ,
      globalScalar U.toScheme.ringCatSheaf (U.ι.appTop (φ i)) ^ n • 𝟙 F = 0 := fun i =>
    exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn (X := U.toScheme)
      (U.ι.appTop (φ i)) F F
      (PerfectApproximation.isQuasicoherent_homology_of_isPerfect U.toScheme F hF) hF
      (cohomologySupportedOn_mono_standard (fun y hy => by
        rw [Scheme.zeroLocus_singleton, ← Scheme.preimage_basicOpen_top]
        exact fun hy' => hdisj i y.1 hy' hy) hFT) (𝟙 F)
  choose n hn using h08EJ
  obtain ⟨P₀, hP₀, ⟨e₀⟩⟩ :=
    exists_isPerfectComplex_restrict_iso_biprod_shift_of_isAffine X U hU F hF
  let R := derivedRestrict U.ι
  let E₀ : DerivedCategory X.Modules := DerivedCategory.Q.obj P₀
  let e₁ : F ⊞ F⟦(1 : ℤ)⟧ ≅ R.obj E₀ := e₀ ≪≫
    (AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso _ U P₀).symm ≪≫
    (AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor X U).app
      (DerivedCategory.Q.obj P₀)
  let s : Fin r → GlobalSectionRing X.ringCatSheaf :=
    fun i => globalScalar X.ringCatSheaf (φ i ^ (n i + 1))
  let s' : Fin r → GlobalSectionRing U.toScheme.ringCatSheaf :=
    fun i => globalScalar U.toScheme.ringCatSheaf (U.ι.appTop (φ i ^ (n i + 1)))
  have hs'F : ∀ i, s' i • 𝟙 F = 0 := by
    intro i
    have e : s' i = globalScalar U.toScheme.ringCatSheaf (U.ι.appTop (φ i)) *
        globalScalar U.toScheme.ringCatSheaf (U.ι.appTop (φ i)) ^ n i :=
      (congrArg (globalScalar U.toScheme.ringCatSheaf)
        (map_pow (ConcreteCategory.hom U.ι.appTop) (φ i) (n i + 1))).trans
        ((globalScalar_pow _ _ _).trans (pow_succ' _ _))
    rw [e, mul_smul, hn i, smul_zero]
  have hs : ∀ i, s' i • 𝟙 (R.obj E₀) = 0 := fun i =>
    CategoryTheory.Pretriangulated.smul_id_eq_zero_of_iso (s' i) e₁
      (CategoryTheory.Pretriangulated.smul_id_biprod_eq_zero (s' i) (hs'F i) (by
        rw [← (shiftFunctor (DerivedCategory U.toScheme.Modules) (1 : ℤ)).map_id,
          ← Functor.map_smul, hs'F i, Functor.map_zero]))
  have hE₀ : IsPerfect (X := X.toRingedSpace)
      (DerivedCategory.Q.obj P₀ : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u}
        X.toRingedSpace)) := ⟨P₀, hP₀, ⟨Iso.refl _⟩⟩
  obtain ⟨E, G, b, hE, hEk⟩ := CategoryTheory.Pretriangulated.exists_coneTower_restrict_iso_biprod
    R s s' (fun i _ _ g => derivedRestrict_map_globalScalar_smul U.ι _ g)
    (fun K => IsPerfect (X := X.toRingedSpace) K)
    (fun T' hT' h₁ h₂ => isPerfect_obj₃_of_distinguished_modules (X) T' hT' h₁ h₂)
    E₀ hE₀ F (F⟦(1 : ℤ)⟧) (biprod.braiding _ _ ≪≫ e₁) hs
  have hET : CohomologySupportedOn X.ringCatSheaf T E := by
    intro j x hx
    obtain ⟨i, hi⟩ := hcov x hx
    obtain ⟨k, hk⟩ := hEk i
    have hk' : globalScalar X.ringCatSheaf (φ i ^ (n i + 1)) ^ k • 𝟙 E = 0 := hk
    refine cohomologySupportedOn_compl_basicOpen_of_pow_smul_id _ E k hk' j x ?_
    rw [Scheme.basicOpen_pow (X := X) (f := φ i) (Nat.succ_pos (n i))]
    exact fun h => h hi
  let b' : G ⊞ F ≅ (AlgebraicGeometry.RingedSpace.derivedRestrictModules
      X.toRingedSpace U).obj E :=
    b ≪≫ ((AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor (X)
      U).app E).symm
  obtain ⟨E₁, γ, a, hE₁, ⟨I, ⟨eI⟩⟩, hα⟩ :=
    exists_isPerfect_derivedTensor_restrict_eq_biprod_map_id_zero_of_isAffine X U hU E hE G F b'
  have hE₁T : CohomologySupportedOn X.ringCatSheaf T E₁ :=
    (Stacks.SheafOfModules.cohomologySupportedOn_derivedTensor_left X.sheaf T E I
      hET).of_iso eI.symm
  let γ' : (E₁ : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)) ⟶
      (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)) := γ
  obtain ⟨Z, g, h, hTr⟩ := distinguished_cocone_triangle γ'
  obtain ⟨P, hP, ⟨iP⟩⟩ :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished _ hTr hE₁ hE
  have hZT : CohomologySupportedOn X.ringCatSheaf T Z :=
    cohomologySupportedOn_obj₃_of_distinguished _ T _ hTr hE₁T hET
  obtain ⟨eZ⟩ : Nonempty ((F ⊞ F⟦(1 : ℤ)⟧) ≅
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).obj Z) :=
    nonempty_iso_biprod_shift_of_map_eq_biprod_map_id_zero
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U) γ' g h hTr a b' hα
  have hPT : CohomologySupportedOn X.ringCatSheaf T (DerivedCategory.Q.obj P) :=
    fun i x hx => by
      rw [← SheafOfModules.isZero_stalkFunctor_obj_iff]
      exact ((SheafOfModules.isZero_stalkFunctor_obj_iff _ x _).2 (hZT i x hx)).of_iso
        ((SheafOfModules.stalkFunctor _ x).mapIso
          ((DerivedCategory.homologyFunctor _ i).mapIso iP))
  exact ⟨P, hP, hPT, ⟨eZ ≪≫
    ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).mapIso
      iP).symm ≪≫
    AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso X.toRingedSpace U P⟩⟩

end Stacks.DerivedQCoh.OpenLift

end
