/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperRepresentableOfAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.GroupSpaceTranslation

/-!
# Separated finitely presented representability is detected over affine schemes

Let `a : F ⟶ G` be a morphism from an fppf sheaf to an algebraic space on the big fppf site of
`S`. Suppose that for every object `W` of the site with affine underlying scheme and every
morphism `h_W ⟶ G`, the base change `F ×_G h_W` is represented by an object `Z` of the site whose
morphism `Z ⟶ W` is separated and of finite presentation. Then `F` is an algebraic space and `a`
is separated and of finite presentation.

The representability is the gluing argument of
`AlgebraicGeometry.Space.exists_isPullback_isProper_of_isAffine`, run for an arbitrary property
of morphisms of schemes which is Zariski local on the target and implies local finite type and
quasi-compactness (the two hypotheses bounding the size of the glued scheme). The three
properties of `a` are then read on affine base changes: separatedness by Stacks 03KM, local finite
presentation by Stacks 0410 and quasi-compactness by Stacks 03KG; quasi-separatedness follows
from separatedness (Stacks 03KK).

This is the reduction, in the proof of Stacks 0DPD, of the claim that `Quot^P_{F/X/B}` is
separated and of finite presentation over an algebraic space `B` to the case of affine `B`.

## Main results

* `AlgebraicGeometry.Space.exists_isPullback_of_isAffine`: the representing data over an arbitrary
  object of the site, from the data over affine objects.
* `AlgebraicGeometry.Space.isAlgebraicSpace_isSeparated_isFinitePresentation_of_isAffine`: `F` is
  an algebraic space and `a` is separated and of finite presentation.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
* [Stacks Project, Tag 0410](https://stacks.math.columbia.edu/tag/0410)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local notation "𝒯" => BigFppfOver.toScheme B S hS

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site is deep
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_SeparatedFinitePresentationOfAffine :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Shortcut for pullbacks of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_SeparatedFinitePresentationOfAffine
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Representing a base change over every object of the site, from the affine objects**, for a
property `Q` of morphisms of schemes which is Zariski local on the target and implies local
finite type and quasi-compactness. If every base change of `a : F ⟶ G` along a morphism
`h_W ⟶ G` from an object `W` with affine underlying scheme is represented by an object `Z` with
`Q (Z ⟶ W)`, then so is every base change along a morphism `h_V ⟶ G` from an arbitrary object
`V` of the site. -/
theorem exists_isPullback_of_isAffine {Q : MorphismProperty Scheme.{u}}
    (hQ : IsZariskiLocalAtTarget Q)
    (hQft : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Q f → LocallyOfFiniteType f ∧ QuasiCompact f)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) (a : F ⟶ G)
    (h : ∀ (W : BigFppfOver B S hS) (ξ : yoneda.obj W ⟶ G),
      IsAffine ((𝒯).obj W) →
        ∃ (Z : BigFppfOver B S hS) (s : yoneda.obj Z ⟶ F) (q : Z ⟶ W),
          IsPullback s (yoneda.map q) a ξ ∧ Q ((𝒯).map q))
    (V : BigFppfOver B S hS) (ξ : yoneda.obj V ⟶ G) :
    ∃ (Y : BigFppfOver B S hS) (s : yoneda.obj Y ⟶ F) (P : Y ⟶ V),
      IsPullback s (yoneda.map P) a ξ ∧ Q ((𝒯).map P) := by
  classical
  let Vi : ((𝒯).obj V).affineOpens → BigFppfOver B S hS :=
    fun W => BigFppfOver.opensRestrictObj B S hS V W.1
  let ui : ∀ W : ((𝒯).obj V).affineOpens, Vi W ⟶ V :=
    fun W => BigFppfOver.opensRestrictHom B S hS V W.1
  choose Z s q hpb hprop using
    fun W : ((𝒯).obj V).affineOpens => h (Vi W) (yoneda.map (ui W) ≫ ξ) W.2
  let t : ∀ W : ((𝒯).obj V).affineOpens, yoneda.obj (Z W) ⟶ pullback ξ a := fun W =>
    pullback.lift (yoneda.map (q W) ≫ yoneda.map (ui W)) (s W) (by
      rw [Category.assoc]
      exact ((hpb W).w).symm)
  have ht₁ : ∀ W : ((𝒯).obj V).affineOpens,
      t W ≫ pullback.fst ξ a = yoneda.map (q W) ≫ yoneda.map (ui W) :=
    fun W => pullback.lift_fst _ _ _
  have ht₂ : ∀ W : ((𝒯).obj V).affineOpens, t W ≫ pullback.snd ξ a = s W :=
    fun W => pullback.lift_snd _ _ _
  have hpbW : ∀ W : ((𝒯).obj V).affineOpens,
      IsPullback (t W) (yoneda.map (q W)) (pullback.fst ξ a) (yoneda.map (ui W)) :=
    fun W => IsPullback.of_right (by rw [ht₂]; exact hpb W) (ht₁ W)
      (IsPullback.of_hasPullback ξ a).flip
  have hFV : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback ξ a) :=
    Presheaf.isSheaf_pullback _ ξ a (BigFppfOver.isSheaf_yoneda_obj B S hS V) hF hG
  obtain ⟨Y, e, P, he, hP⟩ := exists_representing_over_of_openCover_of_size_le B S hS hQ hFV
    (pullback.fst ξ a) (V := Vi) (W := Z) (u := ui) (p := q) (q := t)
    (fun W => inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion W.1.ι))
    (fun y => by
      obtain ⟨W, hW, hyW, -⟩ :=
        exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by trivial)
      exact ⟨⟨W, hW⟩, ⟨y, hyW⟩, rfl⟩)
    hpbW hprop (μ := ((𝒯).obj V).size) V.left.property
    (fun (W : ((𝒯).obj V).affineOpens) => by
      obtain ⟨h₁, h₂⟩ := hQft _ (hprop W)
      have hW : _root_.AlgebraicGeometry.IsOpenImmersion (W.1 : ((𝒯).obj V).Opens).ι :=
        inferInstance
      exact (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact ((𝒯).map (q W))).trans
        (@Scheme.size_le_of_isOpenImmersion _ _ (W.1 : ((𝒯).obj V).Opens).ι hW))
  refine ⟨Y, e.inv ≫ pullback.snd ξ a, P, ?_, hP⟩
  have hc : CommSq (yoneda.map P) (e.inv ≫ pullback.snd ξ a) ξ a :=
    ⟨by rw [← he, Category.assoc, Category.assoc, pullback.condition]⟩
  exact (IsPullback.of_iso_pullback hc e.symm he rfl).flip

/-- **A morphism from an fppf sheaf to an algebraic space whose affine base changes are
represented by separated morphisms of finite presentation is representable, and its source is an
algebraic space which is separated and of finite presentation over the target.**

Let `a : F ⟶ G` be a morphism from an fppf sheaf to an algebraic space such that every base change
of `a` along a morphism `h_W ⟶ G` from an object `W` with affine underlying scheme is represented
by an object `Z` whose morphism `Z ⟶ W` is separated, locally of finite presentation and
quasi-compact. Then `F` is an algebraic space and `a` is separated and of finite presentation. -/
theorem isAlgebraicSpace_isSeparated_isFinitePresentation_of_isAffine
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : IsAlgebraicSpace B S hS G) (a : F ⟶ G)
    (h : ∀ (W : BigFppfOver B S hS) (ξ : yoneda.obj W ⟶ G),
      IsAffine ((𝒯).obj W) →
        ∃ (Z : BigFppfOver B S hS) (s : yoneda.obj Z ⟶ F) (q : Z ⟶ W),
          IsPullback s (yoneda.map q) a ξ ∧
            (_root_.AlgebraicGeometry.IsSeparated ((𝒯).map q) ∧
              LocallyOfFinitePresentation ((𝒯).map q) ∧ QuasiCompact ((𝒯).map q))) :
    IsAlgebraicSpace B S hS F ∧ IsSeparated B S hS a ∧ IsFinitePresentation B S hS a := by
  let Q : MorphismProperty Scheme.{u} :=
    @_root_.AlgebraicGeometry.IsSeparated ⊓ (@LocallyOfFinitePresentation ⊓ @QuasiCompact)
  have hQ₀ : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FinitePresentation)
  have hQ₂ : IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  have hQ₁ : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation ⊓ @QuasiCompact) :=
    MorphismProperty.IsLocalAtTarget.inf _ _
  have hQ : IsZariskiLocalAtTarget Q := MorphismProperty.IsLocalAtTarget.inf _ _
  have hQft : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Q f → LocallyOfFiniteType f ∧ QuasiCompact f :=
    fun f hf => haveI : LocallyOfFinitePresentation f := hf.2.1; ⟨inferInstance, hf.2.2⟩
  have hrep : yoneda.relativelyRepresentable a := by
    intro V ξ
    obtain ⟨Y, s, P, hpb, -⟩ :=
      exists_isPullback_of_isAffine B S hS hQ hQft hF hG.isSheaf a h V ξ
    exact ⟨Y, P, s, hpb⟩
  have hFa : IsAlgebraicSpace B S hS F :=
    isAlgebraicSpace_of_relativelyRepresentable B S hS a hrep hG
  -- the base change along an affine `h_W ⟶ G`, and its comparison with the representing object
  have key : ∀ (W : BigFppfOver B S hS) (ξ : yoneda.obj W ⟶ G),
      IsAffine ((𝒯).obj W) →
        ∃ (Z : BigFppfOver B S hS) (e : yoneda.obj Z ≅ pullback ξ a) (q : Z ⟶ W),
          pullback.fst ξ a = e.inv ≫ yoneda.map q ∧ Q ((𝒯).map q) := by
    intro W ξ hW
    obtain ⟨Z, s, q, hpb, hq⟩ := h W ξ hW
    exact ⟨Z, hpb.flip.isoPullback, q, (Iso.eq_inv_comp _).2 hpb.flip.isoPullback_hom_fst, hq⟩
  have hsep : IsSeparated B S hS a := by
    refine (isSeparated_iff_affine B S hS hFa a).2 fun W hW ξ => ?_
    refine isSeparated_pullback_snd_of_fst B S hS a ξ ?_
    obtain ⟨Z, e, q, he, hq⟩ := key W ξ hW
    rw [he]
    exact isSeparated_comp B S hS _ _ (isSeparated_of_isIso B S hS e.inv)
      ((isSeparated_yoneda_map_iff B S hS q).2 hq.1)
  refine ⟨hFa, hsep, ?_⟩
  refine ⟨((isLocallyOfFinitePresentation_tfae B S hS hFa hG a).out 1 4).2 fun W ξ hW => ?_,
    isQuasiCompact_of_isQuasiCompactSpace_pullback_affine B S hS hFa hG a fun W hW ξ => ?_,
    isQuasiSeparated_of_isSeparated B S hS hsep⟩
  · obtain ⟨Z, e, q, he, hq⟩ := key W ξ hW
    rw [he]
    exact (holdsOnEveryEtaleChart_precomp_iso B S hS _ e.symm (yoneda.map q)).1
      ((holdsOnEveryEtaleChart_yoneda_map_iff B S hS
        LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget q).2 hq.2.1)
  · obtain ⟨Z, e, q, he, hq⟩ := key W ξ hW
    have : IsAffine ((𝒯).obj W) := hW
    have : QuasiCompact ((𝒯).map q) := hq.2.2
    exact isQuasiCompactSpace_of_iso B S hS e
      (isQuasiCompactSpace_yoneda_obj B S hS
        (QuasiCompact.compactSpace_of_compactSpace ((𝒯).map q)))

end AlgebraicGeometry.Space

end
