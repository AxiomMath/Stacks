module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIsColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitLevelTransitionCoherence

/-!
# Stacks 0EYN, second half, for sheaves of sets on Mathlib's small étale site, in adjoint form

Let `(X_i)` be an inverse system of schemes over a nonempty directed index with affine transition
morphisms and `X = lim X_i`, with projections `p_i : X ⟶ X_i`. The colimit half of
[Stacks, Tag 0EYN] says `𝓕 = colim_i p_i^{-1}p_{i, *}𝓕` for every sheaf `𝓕` on `X_étale`. Read
through the adjunctions, this is a descent statement about direct images only: a family of maps
`σ_i : p_{i, *}𝓕 ⟶ p_{i, *}𝒢` compatible with the identifications `p_{j, *} ≅ f_{ji, *}p_{i, *}`
is the family of direct images of a unique `χ : 𝓕 ⟶ 𝒢`.

The tree carries this for abelian sheaves
(`Stacks.EtaleCohomology.AffineLimitCohomology.isDirectImageDescent_of_levelBaseChange`). This file
proves it for sheaves of **sets**, on Mathlib's small étale sites, from the restriction form of
the statement for sheaves of sets with the levels read by base change,
`Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitType_levelBaseChange`, and the
faithfulness of restriction to a level,
`Stacks.EtaleCohomology.AffineLimitCohomology.hom_ext_of_levelRestrictionType`.

## Main definitions

* `Stacks.EtaleCohomology.AffineLimitCohomology.IsSetDirectImageCompatible` — the compatibility
  of a family of maps of direct images of sheaves of sets.

## Main results

* `Stacks.EtaleCohomology.AffineLimitCohomology.existsUnique_setDirectImageDescent` — **the
  descent of direct images**, for sheaves of sets.

## References

* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex levelToSmallEtale transitionScheme)

/-! ### The descent of direct images of sheaves of sets -/

section Descent

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}} (c : Cone D)

/-- **A family of maps of direct images of sheaves of sets, compatible with the identifications
along the factorisations of the projections.** For `a : i ⟶ j` in `Iᵒᵖ` the projection factors
as `p_j = p_i ≫ f_{ji}`, and `Stacks.EtaleCohomology.smallEtalePushforwardComp'`
identifies `f_{ji, *}p_{i, *}` with `p_{j, *}`; a family `σ_i : p_{i, *}𝓕 ⟶ p_{i, *}𝒢` is
compatible when `σ_j` is `f_{ji, *}σ_i` read through those identifications. This is
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsDirectImageCompatible` for sheaves of sets. -/
def IsSetDirectImageCompatible
    (𝓕 𝒢 : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) (Type (max u v + 1)))
    (σ : ∀ i : Iᵒᵖ, (smallEtalePushforward (c.π.app i) (Type (max u v + 1))).obj 𝓕 ⟶
      (smallEtalePushforward (c.π.app i) (Type (max u v + 1))).obj 𝒢) : Prop :=
  ∀ ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j),
    σ j =
      (smallEtalePushforwardComp' (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm
        (Type (max u v + 1))).inv.app 𝓕 ≫
        (systemPushforward D (Type (max u v + 1)) a).map (σ i) ≫
          (smallEtalePushforwardComp' (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm
        (Type (max u v + 1))).hom.app 𝒢

/-- **The compatibility of a family of maps of direct images of sheaves of sets, read on
sections.** -/
theorem isSetDirectImageCompatible_app {i j : Iᵒᵖ} (a : i ⟶ j)
    (𝓕 𝒢 : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) (Type (max u v + 1)))
    (σ : ∀ k : Iᵒᵖ, (smallEtalePushforward (c.π.app k) (Type (max u v + 1))).obj 𝓕 ⟶
      (smallEtalePushforward (c.π.app k) (Type (max u v + 1))).obj 𝒢)
    (hσ : IsSetDirectImageCompatible c 𝓕 𝒢 σ) (U : (D.obj j).Etale) :
    (σ j).hom.app (op U) =
      𝓕.obj.map ((smallEtaleBaseChangeComp'
          (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm).inv.app U).op ≫
        (σ i).hom.app (op ((smallEtaleBaseChange (D.map a)).obj U)) ≫
          𝒢.obj.map ((smallEtaleBaseChangeComp'
            (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm).hom.app U).op := by
  rw [hσ a]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  exact congrArg₂ (· ≫ ·) (Category.comp_id _)
    (congrArg₂ (· ≫ ·) rfl (Category.id_comp _))

end Descent

section Main

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map a)]

/-- **The family of maps on the levels is compatible with the transition datum**, for sheaves of
sets: `Stacks.EtaleCohomology.AffineLimitCohomology.levelFamily_compat` at `Type`. -/
theorem levelFamily_compat_set
    (𝓕 𝒢 : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) (Type (max u v + 1)))
    (σ : ∀ i : Iᵒᵖ, (smallEtalePushforward (c.π.app i) (Type (max u v + 1))).obj 𝓕 ⟶
      (smallEtalePushforward (c.π.app i) (Type (max u v + 1))).obj 𝒢)
    (hσ : IsSetDirectImageCompatible c 𝓕 𝒢 σ)
    {p q : (sys D c B hD hX hc).I} (b : q ⟶ p) (V : (sys D c B hD hX hc).C p) :
    (Functor.whiskerLeft (levelEtaleSite D c B hD hX hc p).op
        (σ (levelIndex D c B hD hX hc p)).hom).app (op V) =
      𝓕.obj.map ((levelBaseChangeCrossing_transition D c B hD hX hc b).hom.app V).op ≫
        (Functor.whiskerLeft (levelEtaleSite D c B hD hX hc q).op
            (σ (levelIndex D c B hD hX hc q)).hom).app
          (op (((sys D c B hD hX hc).u b).obj V)) ≫
          𝒢.obj.map ((levelBaseChangeCrossing_transition D c B hD hX hc b).inv.app V).op := by
  have hm := (congrArg (fun z ↦ 𝓕.obj.map (Quiver.Hom.op z))
    (levelBaseChangeCrossing_transition_hom_app D c B hD hX hc b V)).trans
      (𝓕.obj.map_comp _ _)
  have hk := (𝒢.obj.map_comp
      ((smallEtaleBaseChange (c.π.app (levelIndex D c B hD hX hc q))).map
        ((levelTransitionIso D c B hD hX hc b).hom.app V)).op
      ((levelBaseChangeCrossing_transition D c B hD hX hc b).inv.app V).op).symm.trans
    (congrArg (fun z ↦ 𝒢.obj.map (Quiver.Hom.op z))
      (levelBaseChangeCrossing_transition_inv_app_comp D c B hD hX hc b V))
  exact comp_comp_eq_of_naturality
    (isSetDirectImageCompatible_app c
      ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map b) 𝓕 𝒢 σ hσ
      ((levelEtaleSite D c B hD hX hc p).obj V))
    hm
    ((σ (levelIndex D c B hD hX hc q)).hom.naturality
      ((levelTransitionIso D c B hD hX hc b).hom.app V).op)
    hk

include B hD hX hc in
/-- **[Stacks, Tag 0EYN], second half, for sheaves of sets, with the inverse images removed.** Let
`(X_i)` be an inverse system of schemes over a nonempty directed index with affine transition
morphisms, all objects of a big étale site `B`, and `X = lim X_i`. For sheaves of sets `𝓕`, `𝒢` on
Mathlib's small étale site of `X`, every family `σ_i : p_{i, *}𝓕 ⟶ p_{i, *}𝒢` of maps of direct
images compatible with the identifications along the factorisations of the projections is the
family of direct images of a unique `χ : 𝓕 ⟶ 𝒢`. -/
theorem existsUnique_setDirectImageDescent
    (𝓕 𝒢 : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) (Type (max u v + 1)))
    (σ : ∀ i : Iᵒᵖ, (smallEtalePushforward (c.π.app i) (Type (max u v + 1))).obj 𝓕 ⟶
      (smallEtalePushforward (c.π.app i) (Type (max u v + 1))).obj 𝒢)
    (hσ : IsSetDirectImageCompatible c 𝓕 𝒢 σ) :
    ∃! χ : 𝓕 ⟶ 𝒢, ∀ i : Iᵒᵖ,
      (smallEtalePushforward (c.π.app i) (Type (max u v + 1))).map χ = σ i := by
  obtain ⟨χ, hχ, huniq⟩ := restrictionIsColimitType_levelBaseChange D c B hD hX hc 𝓕 𝒢
    (fun n ↦ Functor.whiskerLeft (levelEtaleSite D c B hD hX hc n).op
      (σ (levelIndex D c B hD hX hc n)).hom)
    (levelFamily_compat_set D c B hD hX hc 𝓕 𝒢 σ hσ)
  have hlev : ∀ n : (sys D c B hD hX hc).I,
      (smallEtalePushforward (c.π.app (levelIndex D c B hD hX hc n))
          (Type (max u v + 1))).map χ =
        σ (levelIndex D c B hD hX hc n) :=
    fun n ↦ hom_ext_of_levelRestrictionType D c B hD hX hc n _ _ fun V ↦ (hχ n V).symm
  have hgen : ∀ {k l : Iᵒᵖ} (a : k ⟶ l),
      (smallEtalePushforward (c.π.app k) (Type (max u v + 1))).map χ = σ k →
        (smallEtalePushforward (c.π.app l) (Type (max u v + 1))).map χ = σ l := by
    intro k l a hk
    rw [hσ a, ← hk]
    exact (NatIso.naturality_1
      (smallEtalePushforwardComp' (c.π.app k) (D.map a) (c.π.app l) (c.w a).symm
        (Type (max u v + 1))) χ).symm
  refine ⟨χ, fun i ↦ ?_, fun ψ hψ ↦ ?_⟩
  · exact hgen ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.counitIso.app i).hom
      (hlev ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.inverse.obj i))
  · refine huniq ψ fun n V ↦ ?_
    rw [← hψ (levelIndex D c B hD hX hc n)]
    rfl

end Main

end Stacks.EtaleCohomology.AffineLimitCohomology

end
