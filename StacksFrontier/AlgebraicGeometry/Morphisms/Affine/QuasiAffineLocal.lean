module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine

/-!
# Quasi-affine morphisms are Zariski local on the base

A morphism of schemes is quasi-affine when the inverse image of every affine open subscheme of
the target is a quasi-affine scheme. This file shows that the condition only has to be tested on
one affine open covering of the target.

## Main results

* `AlgebraicGeometry.Scheme.IsQuasiAffine.of_isOpenCover_basicOpen`: a scheme covered by finitely
  many quasi-affine standard opens of its global sections is quasi-affine.
* `AlgebraicGeometry.Scheme.IsQuasiAffine.basicOpen`: a standard open of a quasi-affine scheme
  is quasi-affine.
* `AlgebraicGeometry.hasAffinePropertyIsQuasiAffineHom`: being quasi-affine is determined by the
  inverse images of the members of an affine open covering of the target.
* `AlgebraicGeometry.isQuasiAffineHom_isZariskiLocalAtTarget`: being quasi-affine is Zariski
  local on the target.
* `AlgebraicGeometry.isQuasiAffineHom_iff_isQuasiAffine`: a morphism to an affine scheme is
  quasi-affine if and only if its source is quasi-affine.
* `AlgebraicGeometry.isQuasiAffineHom_iff_of_isOpenCover`: a morphism is quasi-affine if and only
  if the inverse images of the members of a given affine open covering of the target are
  quasi-affine.
* `AlgebraicGeometry.isQuasiAffineHom_iff_exists_isOpenCover`: a morphism is quasi-affine if and
  only if some affine open covering of the target has quasi-affine inverse images.

## References

* [Stacks Project, Tag 01SM](https://stacks.math.columbia.edu/tag/01SM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A scheme which is covered by finitely many quasi-affine standard opens of global sections is
quasi-affine. -/
theorem Scheme.IsQuasiAffine.of_isOpenCover_basicOpen (X : Scheme.{u}) {ι : Type*} [Finite ι]
    (a : ι → Γ(X, ⊤)) (ha : IsOpenCover fun i ↦ X.basicOpen (a i))
    (h : ∀ i, Scheme.IsQuasiAffine (X.basicOpen (a i)).toScheme) : X.IsQuasiAffine := by
  have hqs (i : ι) : IsQuasiSeparated (α := X) ↑(X.basicOpen (a i)) := by
    have := h i
    rw [isQuasiSeparated_iff_quasiSeparatedSpace]
    exacts [inferInstanceAs (QuasiSeparatedSpace (X.basicOpen (a i)).toScheme),
      (X.basicOpen (a i)).isOpen]
  have hcpt (i : ι) : IsCompact (X := X) ↑(X.basicOpen (a i)) :=
    isCompact_iff_compactSpace.mpr (h i).toCompactSpace
  have _ : CompactSpace X := ⟨by
    rw [← Opens.coe_top, ← ha, Opens.coe_iSup]
    exact isCompact_iUnion hcpt⟩
  have _ : QuasiSeparatedSpace X :=
    QuasiSeparatedSpace.of_isOpenCover ha (fun i ↦ isRetrocompact_basicOpen _) hqs
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X fun x ↦ ?_
  obtain ⟨i, hi⟩ : ∃ i, x ∈ X.basicOpen (a i) := by simpa using congr(x ∈ $ha)
  have hqa := h i
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ :=
    (Scheme.IsQuasiAffine.isBasis_basicOpen (X.basicOpen (a i)).toScheme).exists_subset_of_mem_open
      (Set.mem_univ (⟨x, hi⟩ : X.basicOpen (a i))) isOpen_univ
  have _ := isLocalization_basicOpen_of_qcqs (X := X) (U := ⊤) isCompact_univ
    isQuasiSeparated_univ (a i)
  obtain ⟨⟨b, ⟨_, m, rfl⟩⟩, hb⟩ :=
    IsLocalization.surj (M := Submonoid.powers (a i))
      (S := Γ(X, X.basicOpen (a i))) ((X.basicOpen (a i)).topIso.hom r)
  have hb' : (X.basicOpen (a i)).topIso.hom r *
      algebraMap Γ(X, ⊤) Γ(X, X.basicOpen (a i)) (a i ^ (m + 1)) =
      algebraMap Γ(X, ⊤) Γ(X, X.basicOpen (a i)) (b * a i) := by
    rw [pow_succ, map_mul, map_mul, ← mul_assoc]
    exact congrArg (· * _) hb
  have hres (c : Γ(X, ⊤)) :
      X.basicOpen (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen (a i)) c) =
        X.basicOpen (a i) ⊓ X.basicOpen c := by
    simp only [RingHom.algebraMap_toAlgebra]
    exact X.basicOpen_res c _
  have h1 : X.basicOpen ((X.basicOpen (a i)).topIso.hom r *
      algebraMap Γ(X, ⊤) Γ(X, X.basicOpen (a i)) (a i ^ (m + 1))) =
      X.basicOpen ((X.basicOpen (a i)).topIso.hom r) := by
    rw [X.basicOpen_mul, hres, X.basicOpen_pow _ m.succ_pos, inf_idem,
      inf_eq_left.mpr (X.basicOpen_le _)]
  have h2 : X.basicOpen (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen (a i)) (b * a i)) =
      X.basicOpen (a i * b) := by
    rw [hres, X.basicOpen_mul, X.basicOpen_mul, inf_comm (X.basicOpen b), ← inf_assoc, inf_idem]
  have key : X.basicOpen ((X.basicOpen (a i)).topIso.hom r) = X.basicOpen (a i * b) :=
    h1.symm.trans ((congrArg X.basicOpen hb').trans h2)
  have hrX := Scheme.Opens.ι_image_basicOpen_topIso_inv (X.basicOpen (a i))
    ((X.basicOpen (a i)).topIso.hom r)
  simp only [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at hrX
  refine ⟨a i * b, ?_, ?_⟩ <;> rw [← key, ← hrX]
  exacts [hr.image_of_isOpenImmersion _, ⟨⟨x, hi⟩, hxr, rfl⟩]

/-- A quasi-affine scheme stays quasi-affine on the standard open defined by a global section. -/
theorem Scheme.IsQuasiAffine.basicOpen (X : Scheme.{u}) [X.IsQuasiAffine] (r : Γ(X, ⊤)) :
    Scheme.IsQuasiAffine (X.basicOpen r).toScheme :=
  have : CompactSpace (X.basicOpen r).toScheme :=
    isCompact_iff_compactSpace.mp (isRetrocompact_basicOpen r).isCompact
  Scheme.IsQuasiAffine.of_isImmersion (X.basicOpen r).ι

/-- Being quasi-affine is determined by the inverse images of the members of an affine open
covering of the target. -/
instance hasAffinePropertyIsQuasiAffineHom :
    HasAffineProperty (@IsQuasiAffineHom : MorphismProperty Scheme.{u})
      fun X _ _ _ ↦ Scheme.IsQuasiAffine X where
  isLocal_affineProperty := by
    constructor
    · refine AffineTargetMorphismProperty.respectsIso_mk (fun e f _ hf ↦ ?_) (fun _ _ _ hf ↦ hf)
      have := hf
      have := QuasiCompact.compactSpace_of_compactSpace e.hom
      exact Scheme.IsQuasiAffine.of_isImmersion e.hom
    · intro X Y _ f r hf
      have := hf
      have he : f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.appTop r) := f.preimage_basicOpen_top r
      exact he ▸ Scheme.IsQuasiAffine.basicOpen X (f.appTop r)
    · intro X Y _ f s hs hf
      have hcov : IsOpenCover fun r : s ↦ X.basicOpen (f.appTop (r : Γ(Y, ⊤))) := by
        have h := f.iSup_preimage_eq_top ((isAffineOpen_top Y).iSup_basicOpen_eq_self_iff.mpr hs)
        simp only [f.preimage_basicOpen_top] at h
        exact h
      exact Scheme.IsQuasiAffine.of_isOpenCover_basicOpen X _ hcov fun r ↦
        (f.preimage_basicOpen_top (r : Γ(Y, ⊤))) ▸ hf r
  eq_targetAffineLocally' := by
    ext X Y f
    rw [isQuasiAffineHom_iff]
    exact ⟨fun h U ↦ h U.1 U.2, fun h U hU ↦ h ⟨U, hU⟩⟩

/-- Quasi-affineness of a morphism of schemes is Zariski local on the target. -/
theorem isQuasiAffineHom_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@IsQuasiAffineHom : MorphismProperty Scheme.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hasAffinePropertyIsQuasiAffineHom

/-- A morphism to an affine scheme is quasi-affine exactly when its source is a quasi-affine
scheme. -/
theorem isQuasiAffineHom_iff_isQuasiAffine {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) :
    IsQuasiAffineHom f ↔ Scheme.IsQuasiAffine X :=
  @HasAffineProperty.iff_of_isAffine _ _ hasAffinePropertyIsQuasiAffineHom _ _ f _

/-- A morphism is quasi-affine if and only if the inverse images of the members of any one affine
open covering of the target are quasi-affine. -/
theorem isQuasiAffineHom_iff_of_isOpenCover {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type*}
    (U : ι → S.affineOpens) (hU : IsOpenCover fun i ↦ (U i : S.Opens)) :
    IsQuasiAffineHom f ↔ ∀ i, Scheme.IsQuasiAffine (f ⁻¹ᵁ (U i : S.Opens)).toScheme :=
  @HasAffineProperty.iff_of_iSup_eq_top _ _ hasAffinePropertyIsQuasiAffineHom _ _ _ _ U hU

/-- A morphism of schemes is quasi-affine if and only if there exists an affine open covering of
the target all of whose members have quasi-affine inverse image. -/
@[stacks 01SM "(1) ↔ (2)", ega "II 5.1.1"]
theorem isQuasiAffineHom_iff_exists_isOpenCover {X S : Scheme.{u}} (f : X ⟶ S) :
    IsQuasiAffineHom f ↔ ∃ (ι : Type u) (U : ι → S.affineOpens),
      IsOpenCover (fun i ↦ (U i : S.Opens)) ∧
        ∀ i, Scheme.IsQuasiAffine (f ⁻¹ᵁ (U i : S.Opens)).toScheme :=
  ⟨fun hf ↦ ⟨S.affineOpens, id, iSup_affineOpens_eq_top S, fun i ↦
      hf.isQuasiAffine_preimage (i : S.Opens) i.2⟩,
    fun ⟨_, U, hU, h⟩ ↦ (isQuasiAffineHom_iff_of_isOpenCover f U hU).mpr h⟩

end AlgebraicGeometry

end
