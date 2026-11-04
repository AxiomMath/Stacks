module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.PerfectComplexCharts
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsPerfectGenerator
public import StacksFrontier.Homology.Perfect.CompactObjectAnyModel
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RepresentativeIndependence
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction

/-!
# Perfect objects of `D_QCoh(𝒪_X)` are compact

Let `X` be a quasi-compact and quasi-separated scheme. An object of `D_QCoh(𝒪_X)` is compact if and
only if it is perfect ([Stacks, Tag 09M1]). This file proves the implication from perfectness to
compactness at the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` of
the derived category, where compactness is tested against direct sums indexed by the morphism
universe; the converse is `Stacks.Duality.SupportedGeneration.isPerfect_of_isCompactObject`.

## Main results

* `Stacks.Duality.PerfectCompact.isPerfect_derivedRestrict` — restriction along an open immersion
  preserves perfectness, at the locally small model.
* `Stacks.Duality.PerfectCompact.isCompactObject_of_isPerfect_spec` — the affine case.
* `Stacks.Duality.PerfectCompact.isCompactObject_of_step` — compactness is local for a cover by a
  quasi-compact open and an affine open.
* `Stacks.Duality.PerfectCompact.isCompactObject_of_isPerfect` — a perfect object of
  `D_QCoh(𝒪_X)` is compact, for `X` quasi-compact and quasi-separated.
* `Stacks.Duality.PerfectCompact.isCompactObject_iff_isPerfect` — an object of `D_QCoh(𝒪_X)` is
  compact if and only if it is perfect.

## References

* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
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
open CategoryTheory.Pretriangulated ZeroObject

universe u

namespace Stacks.Duality.PerfectCompact

open Stacks.Duality.OpenImmersion Stacks.Duality.QcqsGeneration

/-! ### Perfect complexes, at the standard model -/

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Restriction along an open immersion preserves perfect complexes.** -/
theorem isPerfectComplex_restrictFunctor {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (E : CochainComplex X.Modules ℤ)
    (hE : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) E) :
    RingedSpace.IsPerfectComplex (X := Y.toRingedSpace)
      (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) := by
  have h₂ := ComplexAndDivisorSituation.isPerfect_restrictFunctor_mapDerivedCategory j
    (RingedSpace.IsPerfectComplex.isPerfect.{u, u + 1} hE)
  exact RingedSpace.isPerfectComplex_of_isPerfect_representation
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := Y.toRingedSpace)
      (((Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors).app E) h₂) ⟨Iso.refl _⟩

/-- **A complex of modules whose associated complex of sheaves is perfect is a perfect object of
`D(R)`**, at the standard model ([Stacks, Tag 08EB]). -/
theorem isPerfect_Q_of_isPerfectComplex_tilde {R : CommRingCat.{u}}
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : RingedSpace.IsPerfectComplex (X := (Spec R).toRingedSpace)
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P) :=
  (isPerfect_tilde_iff (DerivedCategory.Q.obj P)).1
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := (Spec R).toRingedSpace)
      (((tilde.functor R).mapDerivedCategoryFactors).app P).symm
      (RingedSpace.IsPerfectComplex.isPerfect.{u, u + 1} hP))

end Standard

/-! ### Perfect objects, at the locally small model -/

/-- **Restriction along an open immersion preserves perfect objects**, at the locally small model
of the derived category. -/
theorem isPerfect_derivedRestrict {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory X.Modules) (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K) :
    RingedSpace.IsPerfect (X := Y.toRingedSpace) ((derivedRestrict j).obj K) := by
  let E := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj E ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hE : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) E :=
    RingedSpace.isPerfectComplex_of_isPerfect_representation hK ⟨e⟩
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := Y.toRingedSpace)
    ((((Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors).app E).symm ≪≫
      (derivedRestrict j).mapIso e)
    (RingedSpace.IsPerfectComplex.isPerfect (isPerfectComplex_restrictFunctor j E hE))

/-- Perfectness of `Q(P)` for a complex `P` of modules passes from the standard model of `D(R)` to
the locally small one. -/
theorem isPerfect_Q_of_isPerfect_Q_standard {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : @StacksDraft.Perfect.IsPerfect R _ (HasDerivedCategory.standard _)
      ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj P)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P) := by
  exact StacksDraft.Perfect.isPerfect_of_iso
    ((StacksDraft.DerivedModel.modelCompQIso (HasDerivedCategory.standard _)
      ModuleCat.hasDerivedCategory).app P).symm
    ((StacksDraft.Perfect.AnyModel.isPerfect_iff_isPerfect_modelEquiv
      (HasDerivedCategory.standard _) ModuleCat.hasDerivedCategory _).1 hP)

/-! ### The affine case -/

/-- **A perfect object of `D_QCoh(𝒪_{Spec R})` is compact**, at the locally small model. -/
theorem isCompactObject_of_isPerfect_spec (R : CommRingCat.{u})
    (L : Stacks.Duality.quasiCoherentDerivedCategory (Spec R))
    (hL : RingedSpace.IsPerfect (X := (Spec R).toRingedSpace) L.obj) :
    IsCompactObject.{u} L := by
  let M := (derivedTilde R).objPreimage L
  let eM : (derivedTilde R).obj M ≅ L := (derivedTilde R).objObjPreimageIso L
  let P := DerivedCategory.Q.objPreimage M
  let eP : DerivedCategory.Q.obj P ≅ M := DerivedCategory.Q.objObjPreimageIso M
  let ι := (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι
  have e : DerivedCategory.Q.obj (((tilde.functor R).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P) ≅ L.obj :=
    (((tilde.functor R).mapDerivedCategoryFactors).app P).symm ≪≫
      (tilde.functor R).mapDerivedCategory.mapIso eP ≪≫ ((derivedTildeCompι R).app M).symm ≪≫
      ι.mapIso eM
  have hP := RingedSpace.isPerfectComplex_of_isPerfect_representation hL ⟨e⟩
  have hM : StacksDraft.Perfect.IsPerfect M := StacksDraft.Perfect.isPerfect_of_iso eP.symm
    (isPerfect_Q_of_isPerfect_Q_standard P (isPerfect_Q_of_isPerfectComplex_tilde P hP))
  exact isCompactObject_of_iso eM.symm (isCompactObject_derivedTilde_obj R M
    ((StacksDraft.Perfect.AnyModel.isPerfect_iff_isCompactObject_max.{u, u} M).1 hM))

/-! ### Compactness is local, for a cover by a quasi-compact open and an affine open -/

section Step

open Stacks.Koszul.Truncation

variable {Y : Scheme.{u}} [QuasiSeparatedSpace Y] [CompactSpace Y]
  {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U] (jU : U ⟶ Y) [IsOpenImmersion jU]
  {A : Type u} [CommRing A] (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
  {r : ℕ} (f : Fin r → A) (iU : (openComplement f).toScheme ⟶ U) [IsOpenImmersion iU]
  (hsq : IsPullback iU (openComplement f).ι jU jV)
  (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y))

omit [QuasiSeparatedSpace U] in
include hsq hcov in
/-- **Compactness is local on `Y = U ∪ Spec A`.** An object of `D_QCoh(𝒪_Y)` whose restrictions
to `U` and to `Spec A` are compact is compact. -/
theorem isCompactObject_of_step (K : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (hU : IsCompactObject.{u} ((restrictedDerivedRestrict jU).obj K))
    (hV : IsCompactObject.{u} ((restrictedDerivedRestrict jV).obj K)) :
    IsCompactObject.{u} K := by
  let adjU := restrictedDerivedRestrictAdjunction jU
  let adjV := restrictedDerivedRestrictAdjunction jV
  let : (Stacks.Duality.quasiCoherentDerivedPushforward jU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).CommShift ℤ :=
    adjU.rightAdjointCommShift ℤ
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
    (fun N hN => isIso_unit_of_isZero_restrict jU jV f iU hsq hcov N hN) K hU hV

end Step

/-- `Stacks.Duality.PerfectCompact.isCompactObject_of_step` with the overlap given as an open of
`Spec A` equal to `D(f₁) ∪ … ∪ D(f_r)`. -/
theorem isCompactObject_of_step' {Y : Scheme.{u}} [QuasiSeparatedSpace Y] [CompactSpace Y]
    {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U] (jU : U ⟶ Y) [IsOpenImmersion jU]
    {A : Type u} [CommRing A] (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
    {r : ℕ} (f : Fin r → A) {W : (Spec (CommRingCat.of A)).Opens}
    (hW : W = Stacks.Koszul.Truncation.openComplement f)
    (iU : W.toScheme ⟶ U) [IsOpenImmersion iU] (hsq : IsPullback iU W.ι jU jV)
    (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y))
    (K : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (hU : IsCompactObject.{u} ((restrictedDerivedRestrict jU).obj K))
    (hV : IsCompactObject.{u} ((restrictedDerivedRestrict jV).obj K)) :
    IsCompactObject.{u} K := by
  subst hW
  exact isCompactObject_of_step jU jV f iU hsq hcov K hU hV

/-- **Compactness is local, for a cover by a quasi-compact open and an affine open.** Let `Y` be a
quasi-compact quasi-separated scheme covered by a quasi-compact open `U` and the image of an open
immersion `Spec A ⟶ Y`. An object of `D_QCoh(𝒪_Y)` whose restrictions to `U` and to `Spec A` are
compact is compact. -/
theorem isCompactObject_of_cover {Y : Scheme.{u}} [QuasiSeparatedSpace Y] [CompactSpace Y]
    (U : Y.Opens) (hUc : IsCompact (U : Set Y)) {A : Type u} [CommRing A]
    (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
    (hcov : ∀ y : Y, y ∈ U ∨ (∃ x, jV x = y))
    (K : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (hU : IsCompactObject.{u} ((restrictedDerivedRestrict U.ι).obj K))
    (hV : IsCompactObject.{u} ((restrictedDerivedRestrict jV).obj K)) :
    IsCompactObject.{u} K := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUc
  have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
  have hc := jV.isCompact_preimage hUc
  obtain ⟨s, hs⟩ := Stacks.AlgebraicGeometry.InductionPrinciple.exists_finset_basicOpen_of_isCompact
    (isAffineOpen_top (Spec (CommRingCat.of A))) hc le_top
  let e := s.equivFin
  let f : Fin s.card → A := fun i => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (e.symm i)
  have hW : jV ⁻¹ᵁ U = Stacks.Koszul.Truncation.openComplement f := by
    rw [hs]
    refine le_antisymm (iSup₂_le fun g hg => ?_) (iSup_le fun i => ?_)
    · refine le_trans (le_of_eq ?_) (le_iSup _ (e ⟨g, hg⟩))
      congr 1
      simp [f]
    · refine le_trans (le_of_eq ?_)
        (le_iSup₂ (f := fun g _ => (Spec (CommRingCat.of A)).basicOpen g) (e.symm i).1 (e.symm i).2)
      congr 1
      simp [f]
  exact isCompactObject_of_step' U.ι jV f hW (jV ∣_ U) (isPullback_morphismRestrict jV U)
    (fun y => (hcov y).imp (fun hy => ⟨⟨y, hy⟩, rfl⟩) id) K hU hV

/-! ### The induction -/

/-- An object of `D_QCoh(𝒪_Y)` over the empty scheme is zero. -/
theorem isZero_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y]
    (K : Stacks.Duality.quasiCoherentDerivedCategory Y) : IsZero K :=
  isZero_fullSubcategory_of_isZero_obj ((DerivedCategory.isZero_iff_forall_isZero_homology _).2
    fun _ => Stacks.Cohomology.PushforwardRestriction.isZero_sheafOfModules_of_stalk_isZero
      Y.ringCatSheaf _ fun y => isEmptyElim y)

/-- **Perfect objects are compact on a scheme covered by `n` affine opens.** -/
theorem isCompactObject_of_isPerfect_of_affineCover : ∀ (n : ℕ) (Y : Scheme.{u})
    [QuasiSeparatedSpace Y] (V : Fin n → Y.Opens), (∀ i, IsAffineOpen (V i)) →
    (⨆ i, V i) = ⊤ → ∀ K : Stacks.Duality.quasiCoherentDerivedCategory Y,
      RingedSpace.IsPerfect (X := Y.toRingedSpace) K.obj → IsCompactObject.{u} K
  | 0, Y, _, V, _, hcov => fun K _ => by
      have : IsEmpty Y := ⟨fun y => by
        have hy : y ∈ (⊤ : Y.Opens) := trivial
        rw [← hcov] at hy
        simp at hy⟩
      exact isCompactObject_of_iso (isZero_of_isEmpty K).isoZero isCompactObject_zero'
  | n + 1, Y, _, V, hV, hcov => fun K hK => by
      have hcomp : ∀ (m : ℕ) (W : Fin m → Y.Opens), (∀ i, IsAffineOpen (W i)) →
          IsCompact (((⨆ i, W i : Y.Opens)) : Set Y) := fun m W hW => by
        rw [TopologicalSpace.Opens.coe_iSup]
        exact isCompact_iUnion fun i => (hW i).isCompact
      have : CompactSpace Y := ⟨by
        have := hcomp _ V hV
        rwa [hcov, TopologicalSpace.Opens.coe_top] at this⟩
      let U : Y.Opens := ⨆ i : Fin n, V i.castSucc
      have hUc : IsCompact (U : Set Y) := hcomp _ _ fun i => hV _
      have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
      have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUc
      have hIH := isCompactObject_of_isPerfect_of_affineCover n U.toScheme
        (fun i => U.ι ⁻¹ᵁ V i.castSucc)
        (fun i => (hV i.castSucc).preimage_of_isOpenImmersion U.ι (by
          rw [Scheme.Opens.opensRange_ι]
          exact le_iSup (fun i : Fin n => V i.castSucc) i))
        (by
          rw [← Scheme.Hom.preimage_iSup]
          exact Scheme.Opens.ι_preimage_self U)
      let jV := (hV (Fin.last n)).fromSpec
      refine isCompactObject_of_cover U hUc (A := Γ(Y, V (Fin.last n))) jV (fun y => ?_) K
        (hIH _ (isPerfect_derivedRestrict U.ι K.obj hK))
        (isCompactObject_of_isPerfect_spec _ _ (isPerfect_derivedRestrict jV K.obj hK))
      have hy : y ∈ (⊤ : Y.Opens) := trivial
      rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hy
      obtain ⟨i, hi⟩ := hy
      refine Fin.lastCases
        (motive := fun i => y ∈ V i → y ∈ U ∨ ∃ x, (hV (Fin.last n)).fromSpec x = y)
        (fun h => Or.inr ?_) (fun j h => Or.inl ?_) i hi
      · change y ∈ Set.range (hV (Fin.last n)).fromSpec
        rwa [(hV (Fin.last n)).range_fromSpec]
      · exact (TopologicalSpace.Opens.mem_iSup.mpr ⟨j, h⟩ : y ∈ U)

/-- **Perfect objects of `D_QCoh(𝒪_X)` are compact**, for `X` quasi-compact and quasi-separated,
at the locally small model: the implication "perfect ⇒ compact" of [Stacks, Tag 09M1]. -/
theorem isCompactObject_of_isPerfect (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (K : Stacks.Duality.quasiCoherentDerivedCategory X)
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K.obj) : IsCompactObject.{u} K := by
  obtain ⟨s, hs, hX⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : X.Opens))).mp (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
  let t := hs.toFinset
  let e := t.equivFin
  refine isCompactObject_of_isPerfect_of_affineCover t.card X (fun i => ((e.symm i).1 : X.Opens))
    (fun i => (e.symm i).1.2) ?_ K hK
  rw [hX]
  refine le_antisymm (iSup_le fun i => ?_) (iSup₂_le fun W hW => ?_)
  · exact le_iSup₂ (f := fun (W : X.affineOpens) (_ : W ∈ s) => (W : X.Opens)) (e.symm i).1
      (hs.mem_toFinset.mp (e.symm i).2)
  · exact le_iSup (fun i => ((e.symm i).1 : X.Opens)) (e ⟨W, hs.mem_toFinset.mpr hW⟩) |>.trans'
      (by simp)

/-- Let `X` be a quasi-compact and quasi-separated scheme. An object of `D_QCoh(𝒪_X)` is compact
if and only if it is perfect. -/
@[stacks 09M1]
theorem isCompactObject_iff_isPerfect (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (K : Stacks.Duality.quasiCoherentDerivedCategory X) :
    IsCompactObject.{u} K ↔ RingedSpace.IsPerfect (X := X.toRingedSpace) K.obj :=
  ⟨Stacks.Duality.SupportedGeneration.isPerfect_of_isCompactObject X K,
    isCompactObject_of_isPerfect X K⟩

end Stacks.Duality.PerfectCompact

end
