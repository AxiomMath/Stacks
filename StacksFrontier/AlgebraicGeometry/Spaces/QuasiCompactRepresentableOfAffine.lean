/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperRepresentableOfAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Representability by quasi-compact schemes is detected over affine schemes

Let `a : F ⟶ G` be a morphism of fppf sheaves on the big fppf site of `S`, with `G` an algebraic
space. Suppose that for every object `W` of the site with affine underlying scheme and every
morphism `h_W ⟶ G`, the base change `F ×_G h_W` is represented by an object `Z` of the site whose
morphism `Z ⟶ W` is quasi-compact and locally of finite type. Then the same holds over every
object of the site, so `a` is representable, `F` is an algebraic space (Stacks 02WY) and `a` is
quasi-compact (Stacks 03KG).

## Main results

* `AlgebraicGeometry.Space.exists_isPullback_quasiCompact_of_isAffine`: the representing data
  over an arbitrary object of the site, from the data over affine objects.
* `AlgebraicGeometry.Space.isAlgebraicSpace_isQuasiCompact_of_isAffine`: `F` is an algebraic
  space and `a` is quasi-compact.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-- The property of the representing morphisms: quasi-compact and locally of finite type. -/
abbrev QuasiCompactFiniteType : MorphismProperty Scheme.{u} :=
  @QuasiCompact.{u} ⊓ @LocallyOfFiniteType.{u}

/-- Being quasi-compact and locally of finite type is Zariski local on the target. -/
instance : IsZariskiLocalAtTarget QuasiCompactFiniteType.{u} :=
  have : IsZariskiLocalAtTarget (@QuasiCompact.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  have : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FiniteType)
  MorphismProperty.IsLocalAtTarget.inf _ _

/-- **Representing a base change by a quasi-compact scheme of finite type, over every object of
the site, from the affine objects.** -/
theorem exists_isPullback_quasiCompact_of_isAffine
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) (a : F ⟶ G)
    (h : ∀ (W : BigFppfOver B S hS) (ξ : yoneda.obj W ⟶ G),
      IsAffine ((𝒯).obj W) →
        ∃ (Z : BigFppfOver B S hS) (s : yoneda.obj Z ⟶ F) (q : Z ⟶ W),
          IsPullback s (yoneda.map q) a ξ ∧ QuasiCompactFiniteType ((𝒯).map q))
    (V : BigFppfOver B S hS) (ξ : yoneda.obj V ⟶ G) :
    ∃ (Y : BigFppfOver B S hS) (s : yoneda.obj Y ⟶ F) (P : Y ⟶ V),
      IsPullback s (yoneda.map P) a ξ ∧ QuasiCompactFiniteType ((𝒯).map P) := by
  classical
  let Vi : ((𝒯).obj V).affineOpens → BigFppfOver B S hS :=
    fun W => BigFppfOver.opensRestrictObj B S hS V W.1
  let ui : ∀ W : ((𝒯).obj V).affineOpens, Vi W ⟶ V :=
    fun W => BigFppfOver.opensRestrictHom B S hS V W.1
  have hVi : ∀ W : ((𝒯).obj V).affineOpens, IsAffine ((𝒯).obj (Vi W)) := fun W => W.2
  choose Z s q hpb hprop using
    fun W : ((𝒯).obj V).affineOpens => h (Vi W) (yoneda.map (ui W) ≫ ξ) (hVi W)
  have hsq : IsPullback (pullback.fst ξ a) (pullback.snd ξ a) ξ a :=
    IsPullback.of_hasPullback ξ a
  let t : ∀ W : ((𝒯).obj V).affineOpens, yoneda.obj (Z W) ⟶ pullback ξ a := fun W =>
    pullback.lift (yoneda.map (q W) ≫ yoneda.map (ui W)) (s W) (by
      rw [Category.assoc]
      exact ((hpb W).w).symm)
  have ht₂ : ∀ W : ((𝒯).obj V).affineOpens, t W ≫ pullback.snd ξ a = s W :=
    fun W => pullback.lift_snd _ _ _
  have hpbW : ∀ W : ((𝒯).obj V).affineOpens,
      IsPullback (t W) (yoneda.map (q W)) (pullback.fst ξ a) (yoneda.map (ui W)) :=
    fun W => IsPullback.of_right (by rw [ht₂]; exact hpb W) (pullback.lift_fst _ _ _) hsq.flip
  have hFV : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback ξ a) :=
    Presheaf.isSheaf_pullback _ ξ a (BigFppfOver.isSheaf_yoneda_obj B S hS V) hF hG
  obtain ⟨Y, e, P, he, hP⟩ := exists_representing_over_of_openCover_of_size_le B S hS
    (inferInstance : IsZariskiLocalAtTarget QuasiCompactFiniteType.{u}) hFV
    (pullback.fst ξ a) (V := Vi) (W := Z) (u := ui) (p := q) (q := t)
    (fun W => inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion W.1.ι))
    (fun y => by
      obtain ⟨W, hW, hyW, -⟩ :=
        exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by trivial)
      exact ⟨⟨W, hW⟩, ⟨y, hyW⟩, rfl⟩)
    hpbW hprop (μ := ((𝒯).obj V).size) V.left.property
    (fun (W : ((𝒯).obj V).affineOpens) => by
      have : QuasiCompact ((𝒯).map (q W)) := (hprop W).1
      have : LocallyOfFiniteType ((𝒯).map (q W)) := (hprop W).2
      have hW : _root_.AlgebraicGeometry.IsOpenImmersion (W.1 : ((𝒯).obj V).Opens).ι :=
        inferInstance
      exact (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact ((𝒯).map (q W))).trans
        (@Scheme.size_le_of_isOpenImmersion _ _ (W.1 : ((𝒯).obj V).Opens).ι hW))
  refine ⟨Y, e.inv ≫ pullback.snd ξ a, P, ?_, hP⟩
  have hc : CommSq (yoneda.map P) (e.inv ≫ pullback.snd ξ a) ξ a :=
    ⟨by rw [← he, Category.assoc, Category.assoc, pullback.condition]⟩
  exact (IsPullback.of_iso_pullback hc e.symm he rfl).flip

/-- **A morphism of sheaves whose affine base changes are represented by quasi-compact schemes of
finite type is representable.** -/
theorem relativelyRepresentable_of_isAffine_quasiCompact
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) (a : F ⟶ G)
    (h : ∀ (W : BigFppfOver B S hS) (ξ : yoneda.obj W ⟶ G),
      IsAffine ((𝒯).obj W) →
        ∃ (Z : BigFppfOver B S hS) (s : yoneda.obj Z ⟶ F) (q : Z ⟶ W),
          IsPullback s (yoneda.map q) a ξ ∧ QuasiCompactFiniteType ((𝒯).map q)) :
    yoneda.relativelyRepresentable a := by
  intro V ξ
  obtain ⟨Y, s, P, hpb, -⟩ := exists_isPullback_quasiCompact_of_isAffine B S hS hF hG a h V ξ
  exact ⟨Y, P, s, hpb⟩

/-- **Algebraicity and quasi-compactness from the affine base changes.**  A morphism `a : F ⟶ G`
from an fppf sheaf to an algebraic space, whose base changes along morphisms from affine schemes
are represented by schemes quasi-compact and locally of finite type over them, is representable,
so `F` is an algebraic space (Stacks 02WY), and `a` is quasi-compact (Stacks 03KG). -/
theorem isAlgebraicSpace_isQuasiCompact_of_isAffine
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : IsAlgebraicSpace B S hS G) (a : F ⟶ G)
    (h : ∀ (W : BigFppfOver B S hS) (ξ : yoneda.obj W ⟶ G),
      IsAffine ((𝒯).obj W) →
        ∃ (Z : BigFppfOver B S hS) (s : yoneda.obj Z ⟶ F) (q : Z ⟶ W),
          IsPullback s (yoneda.map q) a ξ ∧ QuasiCompactFiniteType ((𝒯).map q)) :
    IsAlgebraicSpace B S hS F ∧ IsQuasiCompact B S hS a := by
  have hFa : IsAlgebraicSpace B S hS F :=
    isAlgebraicSpace_of_relativelyRepresentable B S hS a
      (relativelyRepresentable_of_isAffine_quasiCompact B S hS hF hG.isSheaf a h) hG
  refine ⟨hFa, isQuasiCompact_of_isQuasiCompactSpace_pullback_affine B S hS hFa hG a
    fun W hW ξ => ?_⟩
  obtain ⟨Z, s, q, hpb, hq⟩ := h W ξ hW
  have : QuasiCompact ((𝒯).map q) := hq.1
  have : CompactSpace ((𝒯).obj Z) := QuasiCompact.compactSpace_of_compactSpace ((𝒯).map q)
  exact IsQuasiCompactSpace.of_iso B S hS (isQuasiCompact_yoneda_of_compact B S hS Z this)
    hpb.flip.isoPullback

end AlgebraicGeometry.Space

end
