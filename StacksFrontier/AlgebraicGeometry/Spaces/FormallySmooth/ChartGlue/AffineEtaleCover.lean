module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# A finite affine étale refinement over a quasi-compact base

Let `W ⟶ T` be an étale surjection of objects of the big fppf site over `S` with `T`
quasi-compact, and let `W ⟶ Z` be any morphism. Then there is an affine object `E`, a finite
disjoint union of affine opens of `Z`, with an étale morphism `E ⟶ Z` such that every point of
`T` is the image of a point of `W` whose image in `Z` comes from `E`.

## Main definitions

* `AlgebraicGeometry.Space.ChartGlue.sigmaDescOver`: the morphism out of a coproduct of objects
  of the site.

## Main results

* `AlgebraicGeometry.Space.ChartGlue.exists_affine_etale_refinement`: a finite affine étale
  refinement of `Z` through which every point of `T` is reached from `W`.
* `AlgebraicGeometry.Space.ChartGlue.exists_affine_etale_cover_through`: an affine étale
  surjection onto `T` factoring through `W` and through an affine object étale over `Z`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.ChartGlue

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism of schemes out of the coproduct induced by a family `r i : V i ⟶ Z`, composed
with the structure morphism of `Z`, is the structure morphism of the coproduct object. -/
lemma sigmaDesc_comp_hom {I : Type u} (V : I → BigFppfOver B S hS)
    (hsum : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (V i)))
    {Z : BigFppfOver B S hS} (r : ∀ i, V i ⟶ Z) :
    (Sigma.desc fun i => (BigFppfOver.toScheme B S hS).map (r i)) ≫ B.inclusion.map Z.hom =
      B.inclusion.map (BigFppfOver.sigmaOver B S hS V hsum).hom := by
  show _ = B.inclusion.map (B.inclusion.preimage (X := B.obj hsum) (Y := B.obj hS)
    (Sigma.desc fun i => B.inclusion.map (V i).hom))
  rw [B.inclusion.map_preimage]
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [Sigma.ι_desc_assoc, Sigma.ι_desc]
  show B.inclusion.map (r i).left ≫ B.inclusion.map Z.hom = _
  rw [← Functor.map_comp, Over.w]

/-- The morphism out of a coproduct of objects of the site given by a family of morphisms. -/
def sigmaDescOver {I : Type u} (V : I → BigFppfOver B S hS)
    (hsum : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (V i)))
    {Z : BigFppfOver B S hS} (r : ∀ i, V i ⟶ Z) : BigFppfOver.sigmaOver B S hS V hsum ⟶ Z :=
  (BigFppfOver.exists_hom_of_comp_eq B S hS _ (sigmaDesc_comp_hom B S hS V hsum r)).choose

/-- The underlying morphism of schemes of `sigmaDescOver` is `Sigma.desc` of the underlying
morphisms of schemes. -/
lemma toScheme_map_sigmaDescOver {I : Type u} (V : I → BigFppfOver B S hS)
    (hsum : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (V i)))
    {Z : BigFppfOver B S hS} (r : ∀ i, V i ⟶ Z) :
    (BigFppfOver.toScheme B S hS).map (sigmaDescOver B S hS V hsum r) =
      Sigma.desc fun i => (BigFppfOver.toScheme B S hS).map (r i) :=
  (BigFppfOver.exists_hom_of_comp_eq B S hS _ (sigmaDesc_comp_hom B S hS V hsum r)).choose_spec

/-- The `i`-th coprojection followed by `sigmaDescOver` is `r i`. -/
lemma sigmaOverInj_sigmaDescOver {I : Type u} (V : I → BigFppfOver B S hS)
    (hsum : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (V i)))
    {Z : BigFppfOver B S hS} (r : ∀ i, V i ⟶ Z) (i : I) :
    BigFppfOver.sigmaOverInj B S hS V hsum i ≫ sigmaDescOver B S hS V hsum r = r i := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, toScheme_map_sigmaDescOver, BigFppfOver.toScheme_map_sigmaOverInj]
  exact Sigma.ι_desc _ _

/-- **A finite affine étale refinement over a quasi-compact base.** -/
theorem exists_affine_etale_refinement {Z W T : BigFppfOver B S hS} (wZ : W ⟶ Z) (wT : W ⟶ T)
    (hwT : Etale ((BigFppfOver.toScheme B S hS).map wT))
    (hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map wT))
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj T)] :
    ∃ (E : BigFppfOver B S hS) (eZ : E ⟶ Z), IsAffine ((BigFppfOver.toScheme B S hS).obj E) ∧
      Etale ((BigFppfOver.toScheme B S hS).map eZ) ∧
      ∀ t : (BigFppfOver.toScheme B S hS).obj T, ∃ (w : (BigFppfOver.toScheme B S hS).obj W)
        (e : (BigFppfOver.toScheme B S hS).obj E),
        (BigFppfOver.toScheme B S hS).map wT w = t ∧
          (BigFppfOver.toScheme B S hS).map wZ w = (BigFppfOver.toScheme B S hS).map eZ e := by
  classical
  set Zs := (BigFppfOver.toScheme B S hS).obj Z
  set φ := (BigFppfOver.toScheme B S hS).map wZ
  set ψ := (BigFppfOver.toScheme B S hS).map wT
  have hopen := isOpenMap_of_etale ψ hwT
  -- the open sets of `T` swept out by the affine opens of `Z`
  let Uo : Zs.affineOpens → Set ((BigFppfOver.toScheme B S hS).obj T) :=
    fun O ↦ ψ '' (φ ⁻¹' (O.1 : Set Zs))
  have hUo : ∀ O, IsOpen (Uo O) := fun O ↦ hopen _ (O.1.2.preimage φ.continuous)
  have hcov : Set.univ ⊆ ⋃ O, Uo O := by
    intro t _
    obtain ⟨w, rfl⟩ := hsurj t
    have hx : φ w ∈ (⊤ : Zs.Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hx
    obtain ⟨O, hO⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact Set.mem_iUnion.2 ⟨O, w, hO, rfl⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover Uo hUo hcov
  choose V r hoi hrange haff using fun O : s ↦ BigFppfOver.exists_affineOpen_restrict B S hS Z O.1
  have hsum : B.Contains (∐ fun O : s => (BigFppfOver.toScheme B S hS).obj (V O)) :=
    BigFppfSite.contains_sigma_of_lt_cof B (Cardinal.mk_lt_aleph0.trans B.aleph0_lt_cutoff_cof) _
      fun O ↦ (V O).left.property
  have : ∀ O, IsAffine ((BigFppfOver.toScheme B S hS).obj (V O)) := haff
  refine ⟨BigFppfOver.sigmaOver B S hS V hsum, sigmaDescOver B S hS V hsum r, ?_, ?_, ?_⟩
  · show IsAffine (∐ fun O : s => (BigFppfOver.toScheme B S hS).obj (V O))
    infer_instance
  · rw [toScheme_map_sigmaDescOver]
    exact IsZariskiLocalAtSource.sigmaDesc fun O ↦ by
      have := hoi O
      infer_instance
  · intro t
    obtain ⟨O, hO, ht⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ t))
    obtain ⟨w, hw, rfl⟩ := ht
    obtain ⟨v, hv⟩ : φ w ∈ Set.range ((BigFppfOver.toScheme B S hS).map (r ⟨O, hO⟩)) := by
      rwa [hrange]
    refine ⟨w, Sigma.ι (fun O : s => (BigFppfOver.toScheme B S hS).obj (V O)) ⟨O, hO⟩ v, rfl, ?_⟩
    rw [toScheme_map_sigmaDescOver, ← hv]
    have h := Sigma.ι_desc (fun O : s ↦ (BigFppfOver.toScheme B S hS).map (r O)) ⟨O, hO⟩
    exact (congrArg (fun g ↦ g v) h).symm

/-- The image in schemes of a composite of morphisms with étale images is étale. -/
private theorem etale_map_comp {X Y Z : BigFppfOver B S hS} {f : X ⟶ Y} {g : Y ⟶ Z}
    [Etale ((BigFppfOver.toScheme B S hS).map f)]
    [Etale ((BigFppfOver.toScheme B S hS).map g)] :
    Etale ((BigFppfOver.toScheme B S hS).map (f ≫ g)) := by
  rw [Functor.map_comp]
  infer_instance

/-- **An affine étale surjection over `T` factoring through `W` and through an affine object étale
over `Z`.** -/
theorem exists_affine_etale_cover_through {Z W T : BigFppfOver B S hS} (wZ : W ⟶ Z)
    (wT : W ⟶ T) (hwT : Etale ((BigFppfOver.toScheme B S hS).map wT))
    (hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map wT))
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj T)] :
    ∃ (E : BigFppfOver B S hS) (eZ : E ⟶ Z) (Wa : BigFppfOver B S hS) (wa : Wa ⟶ T)
      (m : Wa ⟶ E) (w' : Wa ⟶ W), IsAffine ((BigFppfOver.toScheme B S hS).obj E) ∧
      Etale ((BigFppfOver.toScheme B S hS).map eZ) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Wa) ∧
      Etale ((BigFppfOver.toScheme B S hS).map wa) ∧
      Function.Surjective ((BigFppfOver.toScheme B S hS).map wa) ∧
      w' ≫ wT = wa ∧ w' ≫ wZ = m ≫ eZ := by
  obtain ⟨E, eZ, hEaff, hEet, hEcov⟩ := exists_affine_etale_refinement B S hS wZ wT hwT hsurj
  have hpres := Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  let P := pullback wZ eZ
  have hsq : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst wZ eZ))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd wZ eZ))
      ((BigFppfOver.toScheme B S hS).map wZ) ((BigFppfOver.toScheme B S hS).map eZ) :=
    (IsPullback.of_hasPullback wZ eZ).map (BigFppfOver.toScheme B S hS)
  have hfstEt : Etale ((BigFppfOver.toScheme B S hS).map (pullback.fst wZ eZ)) :=
    MorphismProperty.of_isPullback (P := @Etale) hsq.flip hEet
  let pT : P ⟶ T := pullback.fst wZ eZ ≫ wT
  have hpTet : Etale ((BigFppfOver.toScheme B S hS).map pT) := etale_map_comp B S hS
  have hpTsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map pT) := by
    intro t
    obtain ⟨w, e, hw, he⟩ := hEcov t
    obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback w e he
    refine ⟨hsq.isoPullback.inv z, ?_⟩
    show (BigFppfOver.toScheme B S hS).map wT
      ((BigFppfOver.toScheme B S hS).map (pullback.fst wZ eZ) (hsq.isoPullback.inv z)) = t
    have h1 := congrArg (fun g ↦ g z) hsq.isoPullback_inv_fst
    simp only [Scheme.Hom.comp_apply] at h1
    rw [h1, hz₁, hw]
  obtain ⟨Wa, wa₀, hWaff, hwa₀et, hWacov⟩ :=
    exists_affine_etale_refinement B S hS (𝟙 P) pT hpTet hpTsurj
  refine ⟨E, eZ, Wa, wa₀ ≫ pT, wa₀ ≫ pullback.snd wZ eZ, wa₀ ≫ pullback.fst wZ eZ, hEaff, hEet,
    hWaff, ?_, ?_, by simp [pT], by simp [pullback.condition]⟩
  · exact etale_map_comp B S hS
  · intro t
    obtain ⟨w, e, hw, he⟩ := hWacov t
    refine ⟨e, ?_⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply, ← he]
    simpa using hw

end AlgebraicGeometry.Space.ChartGlue

end
