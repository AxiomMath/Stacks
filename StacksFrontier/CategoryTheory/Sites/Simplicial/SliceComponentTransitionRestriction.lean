module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CocontinuousPullbackSheafifyUnit
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceComponentRestrictionIso
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceTransitionInverseImageIso

/-!
# The simplicial transition of the restrictions of `a^{-1}𝒢`

Let `(C, J)` be a site with fibre products and `K` a simplicial semi-representable object.  For
an abelian sheaf `𝒢` on `C` the restrictions of `a^{-1}𝒢` to the simplicial components form a
system over the simplex category, whose transition along `φ : m ⟶ n` is
`CategoryTheory.SimplicialSiteSituation.fiberTransitionAb'`, the summand transformation of the
sum formula of Stacks 09WG.  On the other hand each restriction is restriction along the
localization functor `j_p` by
`CategoryTheory.SimplicialSemiRepresentable.situationComponentInverseImageSliceIso`, and those
restrictions form a system whose transition is the comparison
`CategoryTheory.SimplicialSemiRepresentable.sliceAbelianRestrictionCompIso` of
`j_m^{-1} r_φ^{-1}` with `j_n^{-1}`.

This file reduces the agreement of the two systems to one identity about restriction functors
alone, and that identity is the whole remaining content of the comparison of the resolution of
Stacks 0D78 with the Čech resolution of Stacks 01GE.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable`
  `.fiberTransitionAb_augmentationTransitionRestrictionIso`: the identity at a sheaf spelled as a
  restriction along `j_total`, which is where the content is.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.fiberTransitionAb_situationComponentInverseImageSliceIso`: **the two systems agree.**

## Implementation notes

Three things make the reduction work.  `situationComponentInverseImageSliceIso` is the comparison
of restrictions `componentAugmentationRestrictionIso` by
`situationComponentInverseImageSliceIso_eq`; those comparisons satisfy the cocycle law
`augmentationTransitionRestrictionIso_cocycle`; and both
`fiberTransitionAb'` and `situationTransitionInverseImageAbIso` are natural in the abelian sheaf
on the total site, so the passage from `a^{-1}𝒢` to its spelling as a restriction along
`j_total` is the same transport on both sides and cancels.

What is left is the identity at a sheaf *already* spelled as a restriction along `j_total`,
where the summand transformation has to be matched against the comparison
`augmentationTransitionRestrictionIso` of the restrictions along the two factorizations of `j_n`
through the total site.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialSiteSituation

universe u

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {Dm : Type u₃} [Category.{v₃} Dm] {Dn : Type u₄} [Category.{v₄} Dn]

/-- A retraction absorbs the morphism it is composed with: if `f ≫ g` is the identity then
`f ≫ g ≫ k` is `k`. -/
theorem comp_comp_eq_of_comp_eq_id {X Y Z : A} {f : X ⟶ Y} {g : Y ⟶ X}
    (h : f ≫ g = 𝟙 X) (k : X ⟶ Z) : f ≫ g ≫ k = k :=
  (Category.assoc f g k).symm.trans
    ((congrArg (fun t : X ⟶ X => t ≫ k) h).trans (Category.id_comp k))

/-- **Two systems of restrictions agree if they agree at one spelling of the source functor.**
Let `P` and `Q` be two descriptions of one functor `A ⥤ B`, let `Rm`, `Rn` restrict from `B`, let
`T` and `Rinv` be two descriptions of the transition `Dm ⥤ Dn` and `ft : Rm ⋙ T ⟶ Rn` the
transition of the first system.  Let `ρm`, `ρn` identify the restrictions of `Q` with functors
`Jm`, `Jn` out of `A`, let `sc : Jm ⋙ Rinv ≅ Jn` be the transition of the second system, and let
`atr` be a comparison satisfying the cocycle law against `ρm`, `ρn` and `sc`.  If `ft` agrees
with `atr` at `Q`, the two systems agree at `P`.

The transport from `P` to `Q` is the same on both sides — `ft` and the comparison `T ≅ Rinv` are
both natural — so it cancels, and what is left is the cocycle law and the hypothesis. -/
theorem NatTrans.comp_iso_app_eq_of_comp_iso_app
    {P Q : A ⥤ B} {Rm : B ⥤ Dm} {Rn : B ⥤ Dn} {T Rinv : Dm ⥤ Dn} {Jm : A ⥤ Dm} {Jn : A ⥤ Dn}
    (iso : P ≅ Q) (tIso : T ≅ Rinv) (ft : Rm ⋙ T ⟶ Rn)
    (ρm : Q ⋙ Rm ≅ Jm) (ρn : Q ⋙ Rn ≅ Jn) (sc : Jm ⋙ Rinv ≅ Jn)
    (atr : (Q ⋙ Rm) ⋙ Rinv ≅ Q ⋙ Rn)
    (hcoc : Functor.isoWhiskerRight ρm Rinv ≪≫ sc = atr ≪≫ ρn)
    (hiv : ∀ Y : A, ft.app (Q.obj Y) = tIso.hom.app (Rm.obj (Q.obj Y)) ≫ atr.hom.app Y)
    (X : A) :
    ft.app (P.obj X) ≫ Rn.map (iso.hom.app X) ≫ ρn.hom.app X =
      tIso.hom.app (Rm.obj (P.obj X)) ≫
        Rinv.map (Rm.map (iso.hom.app X) ≫ ρm.hom.app X) ≫ sc.hom.app X := by
  have h1 : ft.app (P.obj X) ≫ Rn.map (iso.hom.app X) =
      T.map (Rm.map (iso.hom.app X)) ≫ ft.app (Q.obj X) :=
    (ft.naturality (iso.hom.app X)).symm
  have h2 : tIso.hom.app (Rm.obj (P.obj X)) ≫ Rinv.map (Rm.map (iso.hom.app X)) =
      T.map (Rm.map (iso.hom.app X)) ≫ tIso.hom.app (Rm.obj (Q.obj X)) :=
    (tIso.hom.naturality (Rm.map (iso.hom.app X))).symm
  have hc : Rinv.map (ρm.hom.app X) ≫ sc.hom.app X = atr.hom.app X ≫ ρn.hom.app X :=
    congrArg (fun e => e.hom.app X) hcoc
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [hc, reassoc_of% h2, reassoc_of% h1, hiv X]
  simp only [Category.assoc]

end CategoryTheory

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- **The two systems of restrictions of `a^{-1}𝒢` agree**, granted the corresponding identity at
a sheaf already spelled as a restriction along `j_total`.

The transition `fiberTransitionAb'` of the restrictions of `a^{-1}𝒢`, followed by the
identification of the restriction of degree `n` with `j_n^{-1}`, is the identification of the
summand of Stacks 09WG with `r_φ^{-1}`, followed by `r_φ^{-1}` of the identification of degree
`m`, followed by the comparison of `j_m^{-1} r_φ^{-1}` with `j_n^{-1}`. -/
theorem fiberTransitionAb_situationComponentInverseImageSliceIso_of
    {m n : SimplexCategory} (φ : m ⟶ n)
    (hiv : ∀ G : Sheaf J Ab.{u},
      (SimplicialSiteSituation.fiberTransitionAb' (situation J K) φ).app
          (((totalForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
            ((situation J K).totalTopology) J).obj G) =
        (situationTransitionInverseImageAbIso J K φ).hom.app
            (((situation J K).restrictAb m).obj
              (((totalForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
                ((situation J K).totalTopology) J).obj G)) ≫
          (augmentationTransitionRestrictionIso J K φ).hom.app G)
    (G : Sheaf J Ab.{u}) :
    (SimplicialSiteSituation.fiberTransitionAb' (situation J K) φ).app
          ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
            (situationAugmentation J K)).obj G) ≫
        (situationComponentInverseImageSliceIso J K n).hom.app G =
      (situationTransitionInverseImageAbIso J K φ).hom.app
          (((situation J K).restrictAb m).obj
            ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
              (situationAugmentation J K)).obj G)) ≫
        ((componentTransitionFunctor J K φ).sheafPushforwardContinuous AddCommGrpCat.{u}
            ((situation J K).componentTopology n)
            ((situation J K).componentTopology m)).map
          ((situationComponentInverseImageSliceIso J K m).hom.app G) ≫
        (sliceAbelianRestrictionCompIso J K φ).hom.app G := by
  rw [situationComponentInverseImageSliceIso_hom_app,
    situationComponentInverseImageSliceIso_hom_app]
  exact NatTrans.comp_iso_app_eq_of_comp_iso_app (situationTotalInverseImageAbIso J K)
    (situationTransitionInverseImageAbIso J K φ)
    (SimplicialSiteSituation.fiberTransitionAb' (situation J K) φ)
    (componentAugmentationRestrictionIso J K m) (componentAugmentationRestrictionIso J K n)
    (sliceAbelianRestrictionCompIso J K φ) (augmentationTransitionRestrictionIso J K φ)
    (augmentationTransitionRestrictionIso_cocycle J K φ) hiv G

/-- The comparison of the restrictions along the two factorizations of `j_n` through the total
site is, on sections, restriction of the total-site sheaf along the Cartesian lifts of `φ`.

Both sides are `𝒢` applied to the image in `C` of a morphism of the total category, and both
those images are identities: for the Cartesian lift by
`CategoryTheory.SemiRepresentable.totalForget_map_ιNatTrans_app`, and for the transport because
the two factorizations of `j_n` agree on the nose. -/
theorem augmentationTransitionRestrictionIso_hom_app_hom {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf J Ab.{u}) :
    ((augmentationTransitionRestrictionIso J K φ).hom.app G).hom =
      Functor.whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := slices K) φ.op))
        ((totalForget K).op ⋙ G.obj) := by
  refine NatTrans.ext (funext fun Y => ?_)
  have hR : (Functor.whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := slices K) φ.op))
        ((totalForget K).op ⋙ G.obj)).app Y =
      G.obj.map (Quiver.Hom.op ((totalForget K).map
        ((Grothendieck.ιNatTrans (F := slices K) φ.op).app (Opposite.unop Y)))) := rfl
  have hL : ((augmentationTransitionRestrictionIso J K φ).hom.app G).hom.app Y =
      G.obj.map ((eqToIso (componentTransitionFunctor_comp_componentFunctor_comp_totalForget
        J K φ)).inv.app (Opposite.unop Y)).op := by
    have := totalForget_isContinuous_totalCategory J K
    have := componentFunctor_comp_totalForget_isContinuous J K m
    have := componentFunctor_comp_totalForget_isContinuous J K n
    rfl
  have happ : (eqToIso (componentTransitionFunctor_comp_componentFunctor_comp_totalForget
        J K φ)).inv.app (Opposite.unop Y) =
      𝟙 ((sliceForget K (op n)).obj (Opposite.unop Y)) :=
    (eqToHom_app
          (componentTransitionFunctor_comp_componentFunctor_comp_totalForget J K φ).symm
          (Opposite.unop Y)).trans
      (eqToHom_refl _ rfl)
  rw [hR, hL, totalForget_map_ιNatTrans_app]
  exact congrArg (fun t => G.obj.map (Quiver.Hom.op t)) happ

/-- **The transition of the restrictions of `a^{-1}𝒢` is the comparison of restrictions**, at an
abelian sheaf spelled as a restriction along `j_total`.

The summand transformation of Stacks 09WG goes out of a sheafification, so both sides are
determined by their composite with the sheafification unit.  After that unit the left-hand side is
restriction along the Cartesian lifts of `φ`
(`CategoryTheory.CocontinuousSimplicialSite.toSheafify_comp_fiberTransitionAb_inr_app'`), the
comparison of Stacks 00XR (1) contributes nothing
(`CategoryTheory.Functor`
`.toSheafify_comp_sheafPullbackCocontinuousIsoSheafPushforwardContinuous_hom_app`),
and the comparison of restrictions is that same restriction along the Cartesian lifts
(`augmentationTransitionRestrictionIso_hom_app_hom`). -/
theorem fiberTransitionAb_augmentationTransitionRestrictionIso {m n : SimplexCategory}
    (φ : m ⟶ n) (G : Sheaf J Ab.{u}) :
    (SimplicialSiteSituation.fiberTransitionAb' (situation J K) φ).app
        (((totalForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
          ((situation J K).totalTopology) J).obj G) =
      (situationTransitionInverseImageAbIso J K φ).hom.app
          (((situation J K).restrictAb m).obj
            (((totalForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
              ((situation J K).totalTopology) J).obj G)) ≫
        (augmentationTransitionRestrictionIso J K φ).hom.app G := by
  have := componentTransitionFunctor_isCocontinuous J K φ
  refine Sheaf.hom_ext_toSheafify _ _ ?_
  have ha := CocontinuousSimplicialSite.toSheafify_comp_fiberTransitionAb_inr_app'
    (simplicialSite J K) φ
    (((totalForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
      ((situation J K).totalTopology) J).obj G)
  have hb := Functor.toSheafify_comp_sheafPullbackCocontinuousIsoSheafPushforwardContinuous_hom_app
    (componentTransitionFunctor J K φ) AddCommGrpCat.{u}
    ((situation J K).componentTopology n) ((situation J K).componentTopology m)
    (((situation J K).restrictAb m).obj
      (((totalForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).totalTopology) J).obj G))
  exact ha.trans ((augmentationTransitionRestrictionIso_hom_app_hom J K φ G).symm.trans
    (comp_comp_eq_of_comp_eq_id hb
      ((augmentationTransitionRestrictionIso J K φ).hom.app G).hom).symm)

/-- **The two systems of restrictions of `a^{-1}𝒢` agree.**  This is
`fiberTransitionAb_situationComponentInverseImageSliceIso_of` with its hypothesis discharged by
`fiberTransitionAb_augmentationTransitionRestrictionIso`. -/
theorem fiberTransitionAb_situationComponentInverseImageSliceIso
    {m n : SimplexCategory} (φ : m ⟶ n) (G : Sheaf J Ab.{u}) :
    (SimplicialSiteSituation.fiberTransitionAb' (situation J K) φ).app
          ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
            (situationAugmentation J K)).obj G) ≫
        (situationComponentInverseImageSliceIso J K n).hom.app G =
      (situationTransitionInverseImageAbIso J K φ).hom.app
          (((situation J K).restrictAb m).obj
            ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
              (situationAugmentation J K)).obj G)) ≫
        ((componentTransitionFunctor J K φ).sheafPushforwardContinuous AddCommGrpCat.{u}
            ((situation J K).componentTopology n)
            ((situation J K).componentTopology m)).map
          ((situationComponentInverseImageSliceIso J K m).hom.app G) ≫
        (sliceAbelianRestrictionCompIso J K φ).hom.app G :=
  fiberTransitionAb_situationComponentInverseImageSliceIso_of J K φ
    (fiberTransitionAb_augmentationTransitionRestrictionIso J K φ) G

end CategoryTheory.SimplicialSemiRepresentable

end
