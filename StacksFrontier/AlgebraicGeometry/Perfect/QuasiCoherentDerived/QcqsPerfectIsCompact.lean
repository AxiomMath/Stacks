module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.PerfectComplexCharts
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.CompactAndPerfectLocallySmall
public import StacksFrontier.Homology.Perfect.ModelIndependence

/-!
# A perfect object of `D_QCoh(𝒪_X)` is compact, for `X` quasi-compact and quasi-separated

Let `X` be a quasi-compact quasi-separated scheme and let `K` be an object of `D_QCoh(𝒪_X)` which
is perfect as an object of `D(𝒪_X)`. Then `K` is a compact object of `D_QCoh(𝒪_X)`, with the
direct sums tested over index types in the universe of `X`. The derived categories are the locally
small `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.

## Main results

* `Stacks.DerivedQCoh.isPerfect_derivedRestrict_of_isOpenImmersion_of_model`: restriction along an
  arbitrary open immersion preserves perfectness, at an arbitrary chosen derived category.
* `Stacks.Duality.QcqsPerfect.isCompactObject_of_step`: on a quasi-compact quasi-separated scheme
  covered by a quasi-compact open and an affine open, an object of `D_QCoh` whose two restrictions
  are compact is compact.
* `Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect`: on a quasi-compact quasi-separated
  scheme, a perfect object of `D_QCoh(𝒪_X)` is compact.

## References

* [The Stacks Project, Proposition 36.17.1 (09M1)](https://stacks.math.columbia.edu/tag/09M1)
* [The Stacks Project, Theorem 36.15.3 (09IS)](https://stacks.math.columbia.edu/tag/09IS)
* [The Stacks Project, Lemma 20.46.14 (09UA)](https://stacks.math.columbia.edu/tag/09UA)
* [The Stacks Project, Lemma 36.4.5 (08DZ)](https://stacks.math.columbia.edu/tag/08DZ)
* [The Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Stacks.Duality.OpenImmersion (derivedRestrict)

universe u

/-! ### Perfectness of a restriction along an open immersion, at any chosen model -/

namespace Stacks.DerivedQCoh

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- At the standard model, if a cochain complex `E` represents a perfect object then the
restriction of `E` along an open immersion represents a perfect object. -/
@[sga "6 I 4.18" "special case"]
private theorem isPerfect_q_restrictComplex_of_isOpenImmersion {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (E : CochainComplex X.Modules ℤ)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace)
      (DerivedCategory.Q.obj E)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := U.toRingedSpace)
      (DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors.app E)
    (AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_restrictFunctor_mapDerivedCategory
      j hE)

end Standard

section AnyModel

universe w

/-- Restriction along an arbitrary open immersion preserves perfectness, at an arbitrary chosen
derived category. -/
@[sga "6 I 4.18" "special case"]
public theorem isPerfect_derivedRestrict_of_isOpenImmersion_of_model {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [hX : HasDerivedCategory.{w} X.Modules]
    [hU : HasDerivedCategory.{w} U.Modules] (K : DerivedCategory X.Modules)
    (hK : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace hX K) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect U.toRingedSpace hU
      ((derivedRestrict j).obj K) := by
  obtain ⟨E, ⟨eE⟩⟩ : ∃ E : CochainComplex X.Modules ℤ,
      Nonempty ((@DerivedCategory.Q X.Modules _ _ hX).obj E ≅ K) :=
    ⟨DerivedCategory.Q.objPreimage K, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  have eR : (@DerivedCategory.Q U.Modules _ _ hU).obj
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) ≅
      (derivedRestrict j).obj K :=
    ((Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors.app E).symm ≪≫
      (derivedRestrict j).mapIso eE
  exact (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model _ hU (Iso.refl _) eR).1
    (isPerfect_q_restrictComplex_of_isOpenImmersion j E
      ((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model hX _ eE (Iso.refl _)).1 hK))

end AnyModel

end Stacks.DerivedQCoh

/-! ### The dévissage -/

namespace Stacks.Duality.QcqsPerfect

open Stacks.Duality.OpenImmersion Stacks.Duality.QcqsGeneration

/-- The restriction `Stacks.Duality.OpenImmersion.restrictedDerivedRestrict` of a perfect object of
`D_QCoh(𝒪_X)` along an open immersion is perfect. -/
theorem isPerfect_obj_restrictedDerivedRestrict {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (K : Stacks.Duality.quasiCoherentDerivedCategory X)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K.obj) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := U.toRingedSpace)
      ((restrictedDerivedRestrict j).obj K).obj :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    ((restrictedDerivedRestrictCompιIso j).app K).symm
    (Stacks.DerivedQCoh.isPerfect_derivedRestrict_of_isOpenImmersion_of_model j K.obj hK)

section Step

open Stacks.Koszul.Truncation

variable {Y : Scheme.{u}} [QuasiSeparatedSpace Y] [CompactSpace Y]
  {U : Scheme.{u}} [CompactSpace U] (jU : U ⟶ Y) [IsOpenImmersion jU]
  {A : Type u} [CommRing A] (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
  {r : ℕ} (f : Fin r → A) (iU : (openComplement f).toScheme ⟶ U) [IsOpenImmersion iU]
  (hsq : IsPullback iU (openComplement f).ι jU jV)
  (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y))

include hsq hcov in
/-- Let `Y` be a quasi-compact quasi-separated scheme covered by a quasi-compact open
`j_U : U ⟶ Y` and an affine open `j_V : Spec A ⟶ Y` whose overlap is
`D(f₁) ∪ … ∪ D(f_r) ⊆ Spec A`. An object of `D_QCoh(𝒪_Y)` whose restrictions to `U` and to
`Spec A` are compact is compact. -/
theorem isCompactObject_of_step (K : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (hKU : IsCompactObject.{u} ((restrictedDerivedRestrict jU).obj K))
    (hKV : IsCompactObject.{u} ((restrictedDerivedRestrict jV).obj K)) :
    IsCompactObject.{u} K := by
  let adjU := restrictedDerivedRestrictAdjunction jU
  let adjV := restrictedDerivedRestrictAdjunction jV
  let : (Stacks.Duality.quasiCoherentDerivedPushforward jU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).CommShift ℤ :=
    adjU.rightAdjointCommShift ℤ
  let : adjU.CommShift ℤ := adjU.commShift_of_leftAdjoint ℤ
  let : (Stacks.Duality.quasiCoherentDerivedPushforward jV
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)).CommShift ℤ :=
    adjV.rightAdjointCommShift ℤ
  have : (Stacks.Duality.quasiCoherentDerivedPushforward jU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).Additive :=
    adjU.right_adjoint_additive
  have : (Stacks.Duality.quasiCoherentDerivedPushforward jV
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)).Additive :=
    adjV.right_adjoint_additive
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward jU
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward jU
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward jV
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward jV
  exact isCompactObject_of_isCompactObject_restrict adjU adjV
    (isIso_unit_of_isZero_restrict jU jV f iU hsq hcov) K hKU hKV

end Step

section Induction

open Stacks.Koszul.Truncation

/-- `Stacks.Duality.QcqsPerfect.isCompactObject_of_step` with the overlap given as an open of
`Spec A` equal to `D(f₁) ∪ … ∪ D(f_r)`. -/
theorem isCompactObject_of_step' {Y : Scheme.{u}} [QuasiSeparatedSpace Y] [CompactSpace Y]
    {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U] (jU : U ⟶ Y) [IsOpenImmersion jU]
    {A : Type u} [CommRing A] (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
    {r : ℕ} (f : Fin r → A) {W : (Spec (CommRingCat.of A)).Opens} (hW : W = openComplement f)
    (iU : W.toScheme ⟶ U) [IsOpenImmersion iU] (hsq : IsPullback iU W.ι jU jV)
    (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y))
    (K : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (hKU : IsCompactObject.{u} ((restrictedDerivedRestrict jU).obj K))
    (hKV : IsCompactObject.{u} ((restrictedDerivedRestrict jV).obj K)) :
    IsCompactObject.{u} K := by
  subst hW
  exact isCompactObject_of_step jU jV f iU hsq hcov K hKU hKV

/-- Let `Y` be a quasi-compact quasi-separated scheme covered by a quasi-compact open `U` and the
image of an open immersion `Spec A ⟶ Y`, and suppose every perfect object of `D_QCoh(𝒪_U)` is
compact. Then every perfect object of `D_QCoh(𝒪_Y)` is compact. -/
theorem isCompactObject_of_cover {Y : Scheme.{u}} [QuasiSeparatedSpace Y] [CompactSpace Y]
    (U : Y.Opens) (hUc : IsCompact (U : Set Y)) {A : Type u} [CommRing A]
    (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
    (hcov : ∀ y : Y, y ∈ U ∨ (∃ x, jV x = y))
    (hU : ∀ L : Stacks.Duality.quasiCoherentDerivedCategory U.toScheme,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := U.toScheme.toRingedSpace) L.obj →
        IsCompactObject.{u} L)
    (K : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) K.obj) :
    IsCompactObject.{u} K := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUc
  have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
  obtain ⟨s, hs⟩ := Stacks.AlgebraicGeometry.InductionPrinciple.exists_finset_basicOpen_of_isCompact
    (isAffineOpen_top (Spec (CommRingCat.of A))) (jV.isCompact_preimage hUc) le_top
  let e := s.equivFin
  let f : Fin s.card → A := fun i ↦ (Scheme.ΓSpecIso (CommRingCat.of A)).hom (e.symm i)
  have hW : jV ⁻¹ᵁ U = openComplement f := by
    rw [hs]
    refine le_antisymm (iSup₂_le fun g hg ↦ ?_) (iSup_le fun i ↦ ?_)
    · refine le_trans (le_of_eq ?_) (le_iSup _ (e ⟨g, hg⟩))
      congr 1
      simp [f]
    · refine le_trans (le_of_eq ?_)
        (le_iSup₂ (f := fun g _ ↦ (Spec (CommRingCat.of A)).basicOpen g) (e.symm i).1 (e.symm i).2)
      congr 1
      simp [f]
  exact isCompactObject_of_step' U.ι jV f hW (jV ∣_ U) (isPullback_morphismRestrict jV U)
    (fun y ↦ (hcov y).imp (fun hy ↦ ⟨⟨y, hy⟩, rfl⟩) id) K
    (hU _ (isPerfect_obj_restrictedDerivedRestrict U.ι K hK))
    ((AlgebraicGeometry.isCompactObject_iff_isPerfect_spec_of_model (CommRingCat.of A) _).2
      (isPerfect_obj_restrictedDerivedRestrict jV K hK))

/-- On a quasi-separated scheme covered by `n` affine opens, every perfect object of
`D_QCoh(𝒪_Y)` is compact. -/
theorem isCompactObject_of_affineCover : ∀ (n : ℕ) (Y : Scheme.{u})
    [QuasiSeparatedSpace Y] (V : Fin n → Y.Opens), (∀ i, IsAffineOpen (V i)) →
    (⨆ i, V i) = ⊤ → ∀ K : Stacks.Duality.quasiCoherentDerivedCategory Y,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) K.obj →
        IsCompactObject.{u} K
  | 0, Y, _, V, _, hcov, K, _ => by
      have : IsEmpty Y := ⟨fun y ↦ by
        have hy : y ∈ (⊤ : Y.Opens) := trivial
        rw [← hcov] at hy
        simp at hy⟩
      have h0 : IsZero K.obj :=
        @Stacks.Duality.QcqsGeneration.isZero_of_isZero_derivedRestrict Y K.obj Empty
          (fun i ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim)
          (fun y ↦ (IsEmpty.false y).elim) (fun i ↦ i.elim)
      exact isCompactObject_of_iso
        (CategoryTheory.ObjectProperty.isZero_fullSubcategory_of_isZero_obj h0).isoZero
        isCompactObject_zero'
  | n + 1, Y, _, V, hV, hcov, K, hK => by
      have hcomp : ∀ (m : ℕ) (W : Fin m → Y.Opens), (∀ i, IsAffineOpen (W i)) →
          IsCompact (((⨆ i, W i : Y.Opens)) : Set Y) := fun m W hW ↦ by
        rw [TopologicalSpace.Opens.coe_iSup]
        exact isCompact_iUnion fun i ↦ (hW i).isCompact
      have : CompactSpace Y := ⟨by
        simpa only [hcov, TopologicalSpace.Opens.coe_top] using hcomp _ V hV⟩
      let U : Y.Opens := ⨆ i : Fin n, V i.castSucc
      have hUc : IsCompact (U : Set Y) := hcomp _ _ fun i ↦ hV _
      have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
      have hIH : ∀ L : Stacks.Duality.quasiCoherentDerivedCategory U.toScheme,
          Stacks.Cohomology.PerfectComplexes.IsPerfect (X := U.toScheme.toRingedSpace) L.obj →
            IsCompactObject.{u} L :=
        isCompactObject_of_affineCover n U.toScheme (fun i ↦ U.ι ⁻¹ᵁ V i.castSucc)
          (fun i ↦ (hV i.castSucc).preimage_of_isOpenImmersion U.ι (by
            rw [Scheme.Opens.opensRange_ι]
            exact le_iSup (fun i : Fin n => V i.castSucc) i))
          (by
            rw [← Scheme.Hom.preimage_iSup]
            exact Scheme.Opens.ι_preimage_self U)
      refine isCompactObject_of_cover U hUc (A := Γ(Y, V (Fin.last n)))
        (hV (Fin.last n)).fromSpec (fun y ↦ ?_) hIH K hK
      have hy : y ∈ (⊤ : Y.Opens) := trivial
      rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hy
      obtain ⟨i, hi⟩ := hy
      refine Fin.lastCases
        (motive := fun i ↦ y ∈ V i → y ∈ U ∨ ∃ x, (hV (Fin.last n)).fromSpec x = y)
        (fun h ↦ Or.inr ?_) (fun j h ↦ Or.inl ?_) i hi
      · rw [← Set.mem_range, (hV (Fin.last n)).range_fromSpec]
        exact h
      · exact (TopologicalSpace.Opens.mem_iSup.mpr ⟨j, h⟩ : y ∈ U)

end Induction

/-! ### Perfect objects are compact -/

/-- Let `X` be a quasi-compact quasi-separated scheme and let `K` be an object of `D_QCoh(𝒪_X)`
which is perfect as an object of `D(𝒪_X)`. Then `K` is a compact object of `D_QCoh(𝒪_X)`, with
the direct sums tested over index types in the universe of `X`, at the locally small derived
category `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. -/
@[stacks 09M1 "perfect implies compact, on a quasi-compact quasi-separated scheme, at the locally \
small AlgebraicGeometry.Scheme.Modules.hasDerivedCategory. The opposite implication is not covered \
here; for it on a general scheme see AlgebraicGeometry.isPerfect_of_isCompactObject, and for both \
on an affine scheme see AlgebraicGeometry.isCompactObject_iff_isPerfect_spec_of_model"]
theorem isCompactObject_of_isPerfect (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (K : Stacks.Duality.quasiCoherentDerivedCategory X)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K.obj) :
    IsCompactObject.{u} K := by
  obtain ⟨s, hs, hX⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : X.Opens))).mp (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
  let t := hs.toFinset
  let e := t.equivFin
  refine isCompactObject_of_affineCover t.card X (fun i ↦ ((e.symm i).1 : X.Opens))
    (fun i ↦ (e.symm i).1.2) ?_ K hK
  rw [hX]
  refine le_antisymm (iSup_le fun i ↦ ?_) (iSup₂_le fun W hW ↦ ?_)
  · exact le_iSup₂ (f := fun (W : X.affineOpens) (_ : W ∈ s) ↦ (W : X.Opens)) (e.symm i).1
      (hs.mem_toFinset.mp (e.symm i).2)
  · exact (le_iSup (fun i ↦ ((e.symm i).1 : X.Opens)) (e ⟨W, hs.mem_toFinset.mpr hW⟩)).trans'
      (by simp)

end Stacks.Duality.QcqsPerfect

end
