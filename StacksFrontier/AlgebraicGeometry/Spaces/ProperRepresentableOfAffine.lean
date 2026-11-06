/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelativeSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOpenRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# Proper representability is detected over affine schemes

Let `a : F ⟶ G` be a morphism of fppf sheaves on the big fppf site of `S`. Suppose that for every
object `W` of the site with affine underlying scheme and every morphism `h_W ⟶ G`, the base
change `F ×_G h_W` is represented by an object `Z` of the site whose morphism `Z ⟶ W` is a
proper morphism of schemes. Then the same holds over every object `V` of the site: cover `V` by
its affine opens `W`; the base change of `F ×_G h_V ⟶ h_V` along `h_W ⟶ h_V` is `F ×_G h_W`, and
the representing schemes glue (Stacks 01JJ, in the relative form of
`AlgebraicGeometry.Space.exists_representing_over_of_openCover_of_size_le`). Properness is local
on the target, so the glued morphism is proper. No size hypothesis is needed: a scheme proper over
an affine open `W` of `V` has size at most that of `W`, which is at most that of `V`.

Consequently `a` is representable, so `F` is an algebraic space as soon as `G` is (Stacks 02WY),
and `a` is proper by the affine clause of Stacks 083R. This is the reduction, in the proofs of
Stacks 0DPB and 0DPC, of properness of `Quot^P_{F/X/B} ⟶ B` over an algebraic space `B` to the
case of an affine scheme `B`.

## Main results

* `AlgebraicGeometry.Space.exists_isPullback_isProper_of_isAffine`: the representing data over
  an arbitrary object of the site, from the data over affine objects.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_isAffine`: `a` is representable.
* `AlgebraicGeometry.Space.isAlgebraicSpace_isProper_of_isAffine`: `F` is an algebraic space and
  `a` is proper.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
* [Stacks Project, Tag 083R](https://stacks.math.columbia.edu/tag/083R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local notation "𝒯" => BigFppfOver.toScheme B S hS

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_ProperRepresentableOfAffine :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ProperRepresentableOfAffine
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Properly representing a base change over every object of the site, from the affine
objects.** If every base change of `a : F ⟶ G` along a morphism `h_W ⟶ G` from an object `W`
with affine underlying scheme is represented by an object `Z` proper over `W`, then so is every
base change along a morphism `h_V ⟶ G` from an arbitrary object `V` of the site. -/
theorem exists_isPullback_isProper_of_isAffine
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) (a : F ⟶ G)
    (h : ∀ (W : BigFppfOver B S hS) (ξ : yoneda.obj W ⟶ G),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
        ∃ (Z : BigFppfOver B S hS) (s : yoneda.obj Z ⟶ F) (q : Z ⟶ W),
          IsPullback s (yoneda.map q) a ξ ∧
            _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map q))
    (V : BigFppfOver B S hS) (ξ : yoneda.obj V ⟶ G) :
    ∃ (Y : BigFppfOver B S hS) (s : yoneda.obj Y ⟶ F) (P : Y ⟶ V),
      IsPullback s (yoneda.map P) a ξ ∧
        _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map P) := by
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
  have ht₂ : ∀ W, t W ≫ pullback.snd ξ a = s W := fun W => pullback.lift_snd _ _ _
  have hpbW : ∀ W : ((𝒯).obj V).affineOpens, IsPullback (t W) (yoneda.map (q W))
      (pullback.fst ξ a) (yoneda.map (ui W)) := fun W =>
    IsPullback.of_right (by
      rw [ht₂]
      exact hpb W) (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback ξ a).flip
  have hFV : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback ξ a) :=
    Presheaf.isSheaf_pullback _ ξ a (BigFppfOver.isSheaf_yoneda_obj B S hS V) hF hG
  have hQ : IsZariskiLocalAtTarget (@_root_.AlgebraicGeometry.IsProper.{u}) := inferInstance
  obtain ⟨Y, e, P, he, hP⟩ := exists_representing_over_of_openCover_of_size_le B S hS hQ hFV
    (pullback.fst ξ a) (V := Vi) (W := Z) (u := ui) (p := q) (q := t)
    (fun W => inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion W.1.ι))
    (fun y => by
      obtain ⟨W, hW, hyW, -⟩ :=
        exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by trivial)
      exact ⟨⟨W, hW⟩, ⟨y, hyW⟩, rfl⟩)
    hpbW hprop (μ := ((𝒯).obj V).size) V.left.property
    (fun (W : ((𝒯).obj V).affineOpens) => by
      have : _root_.AlgebraicGeometry.IsProper ((𝒯).map (q W)) := hprop W
      have hW : _root_.AlgebraicGeometry.IsOpenImmersion (W.1 : ((𝒯).obj V).Opens).ι :=
        inferInstance
      exact (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact ((𝒯).map (q W))).trans
        (@Scheme.size_le_of_isOpenImmersion _ _ (W.1 : ((𝒯).obj V).Opens).ι hW))
  refine ⟨Y, e.inv ≫ pullback.snd ξ a, P, ?_, hP⟩
  have hc : CommSq (yoneda.map P) (e.inv ≫ pullback.snd ξ a) ξ a :=
    ⟨by rw [← he, Category.assoc, Category.assoc, pullback.condition]⟩
  exact (IsPullback.of_iso_pullback hc e.symm he rfl).flip

/-- **A morphism of sheaves whose affine base changes are representable is representable.** -/
theorem relativelyRepresentable_of_isAffine
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) (a : F ⟶ G)
    (h : ∀ (W : BigFppfOver B S hS) (ξ : yoneda.obj W ⟶ G),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
        ∃ (Z : BigFppfOver B S hS) (s : yoneda.obj Z ⟶ F) (q : Z ⟶ W),
          IsPullback s (yoneda.map q) a ξ ∧
            _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map q)) :
    yoneda.relativelyRepresentable a := by
  intro V ξ
  obtain ⟨Y, s, P, hpb, -⟩ := exists_isPullback_isProper_of_isAffine B S hS hF hG a h V ξ
  exact ⟨Y, P, s, hpb⟩

/-- **Stacks 083R, affine clause, for a morphism of sheaves represented over affines.** Let
`a : F ⟶ G` be a morphism from an fppf sheaf to an algebraic space over `S` such that every base
change of `a` along a morphism `h_W ⟶ G` from an object `W` with affine underlying scheme is
represented by an object proper over `W`. Then `F` is an algebraic space and `a` is proper. -/
theorem isAlgebraicSpace_isProper_of_isAffine
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : IsAlgebraicSpace B S hS G) (a : F ⟶ G)
    (h : ∀ (W : BigFppfOver B S hS) (ξ : yoneda.obj W ⟶ G),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
        ∃ (Z : BigFppfOver B S hS) (s : yoneda.obj Z ⟶ F) (q : Z ⟶ W),
          IsPullback s (yoneda.map q) a ξ ∧
            _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map q)) :
    IsAlgebraicSpace B S hS F ∧ IsProper B S hS a := by
  have hFa : IsAlgebraicSpace B S hS F :=
    isAlgebraicSpace_of_relativelyRepresentable B S hS a
      (relativelyRepresentable_of_isAffine B S hS hF hG.isSheaf a h) hG
  refine ⟨hFa, ((isProper_tfae B S hS hFa hG a).out 3 1).mp fun W ξ hW => ?_⟩
  obtain ⟨Z, s, q, hpb, hq⟩ := h W ξ hW
  rw [(Iso.eq_inv_comp _).2 hpb.flip.isoPullback_hom_fst]
  exact isProper_comp' B S hS _ (yoneda.map q) (isAlgebraicSpace_yoneda B S hS Z)
    (isAlgebraicSpace_yoneda B S hS W) (isProper_of_isIso B S hS _)
    (isProper_yoneda_map B S hS q hq)

end AlgebraicGeometry.Space

end
