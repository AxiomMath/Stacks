module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.MemberLocalStep
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjRestrictIsoFactors
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectFunctoriality
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.IteratedSlice

/-!
# The product with an object of the big fppf site is the fibre product over the base

Let `T` be an object of the big fppf category over `S`, with scheme `X` and structure morphism
`f : X ⟶ S`. Two functors of sites carry a module on the big fppf site of `X` back to one on the
big fppf site of `S`: taking the product with `T` inside the big fppf category over `S` and reading
the result on `(Sch/X)_fppf` through the equivalence of Stacks 06WI, and taking the fibre product
with `X` over `S`. This file identifies them, together with their comparisons of structure sheaves,
and identifies the two resulting pushforwards of sheaves of modules.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.objStarPullbackIso`: the product with `T` is the fibre product
  over `S`, as functors of sites from the big fppf category over `S` to the big fppf category over
  the scheme of `T`.
* `AlgebraicGeometry.BigFppfOver.objForwardSharp`: the comparison of structure sheaves of the
  equivalence of Stacks 06WI read forwards, which is the identity.
* `AlgebraicGeometry.BigFppfOver.objStarPushforward`: the pushforward along the product with `T`
  preceded by the forward reindexing of Stacks 06WI.

## Main results

* `CategoryTheory.starIteratedSliceForwardIsoPullback_hom_app_left_comp_fst`: the isomorphism
  `H ⨯ G ≅ H ×_F G` of `CategoryTheory.starIteratedSliceForwardIsoPullback` carries the first
  projection of the fibre product to the second projection of the product.
* `AlgebraicGeometry.BigFppfOver.comparisonComp_objStarPullbackIso`: the two routes carry the same
  comparison of structure sheaves, the hypothesis of `SheafOfModules.pushforwardCongr₂`.
* `AlgebraicGeometry.BigFppfOver.objStarPullbackPushforwardIso`: the two right adjoints of
  restriction to an object of the big fppf site agree as pushforwards of sheaves of modules.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 04IR](https://stacks.math.columbia.edu/tag/04IR)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

section Slice

attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

variable {E : Type u} [Category.{v} E] {F G : E} (s : G ⟶ F) [HasPullbacks E]

/-- For `s : G ⟶ F` and `Z` an object of the slice `E/F`, the isomorphism `Z ⨯ (G/F) ≅ Z ×_F G` of
`CategoryTheory.starIteratedSliceForwardIsoPullback` carries the projection of the fibre product to
`Z` to the projection of the product to `Z`. -/
public theorem starIteratedSliceForwardIsoPullback_hom_app_left_comp_fst (Z : Over F) :
    ((starIteratedSliceForwardIsoPullback s).hom.app Z).left ≫ pullback.fst Z.hom s =
      (prod.snd : Over.mk s ⨯ Z ⟶ Z).left := by
  refine Eq.trans ?_ (congrArg CommaMorphism.left (Over.forgetAdjStar_counit_app (Over.mk s) Z))
  have h := congrArg CommaMorphism.left (Adjunction.rightAdjointUniq_hom_app_counit
    ((Over.mk s).iteratedSliceEquiv.symm.toAdjunction.comp (Over.forgetAdjStar (Over.mk s)))
    (Over.mapPullbackAdj s) Z)
  simp only [Over.comp_left] at h
  simp only [Adjunction.comp_counit_app] at h
  simp only [Over.comp_left] at h
  simp only [Over.forget_map, Over.mapPullbackAdj_counit_app, Over.homMk_left] at h
  exact h.trans (Category.id_comp _)

end Slice

end CategoryTheory

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- The product with `T` in the big fppf category over `S`, read on the big fppf site of the scheme
`X` of `T` through the equivalence of Stacks 06WI, is base change along the structure morphism
`f : X ⟶ S` of `T`. -/
public noncomputable def objStarPullbackIso :
    Over.star T ⋙ (objEquiv B S hS T).inverse ≅ Over.pullback T.hom :=
  starIteratedSliceForwardIsoPullback T.hom

/-- The identification of `T ⨯ Z` with `Z ×_S X` carries the projection of the fibre product to `Z`
to the projection of the product to `Z`. -/
public theorem objStarPullbackIso_hom_app_left (Z : BigFppfOver B S hS) :
    ((objStarPullbackIso B S hS T).hom.app Z).left ≫ pullback.fst Z.hom T.hom =
      (prod.snd : T ⨯ Z ⟶ Z).left :=
  starIteratedSliceForwardIsoPullback_hom_app_left_comp_fst T.hom Z

attribute [instance] isContinuous_objBaseChange

/-- Taking the product with `T` and then passing to the big fppf site of the scheme of `T` is a
continuous functor. -/
public instance isContinuous_starObjEquivInverse :
    (Over.star T ⋙ (objEquiv B S hS T).inverse).IsContinuous (topology B S hS)
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  haveI := isContinuous_objEquiv_inverse B S hS T
  Functor.isContinuous_comp _ _ _ ((topology B S hS).over T) _

/-- The comparison of structure sheaves of the equivalence of Stacks 06WI, read forwards: the
identity, a global function on the scheme of an object of the big fppf site of the scheme of `T`
being a global function on the same scheme read in the localization at `T`. -/
public noncomputable def objForwardSharp :
    (structureSheaf B S hS).over T ⟶
      ((objEquiv B S hS T).inverse.sheafPushforwardContinuous RingCat.{u}
        ((topology B S hS).over T)
        (topology B (objScheme B S hS T) (contains_objScheme B S hS T))).obj
        (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  𝟙 _

/-- The two routes round the square of ringed sites carry the same comparison of structure sheaves:
restricting a global function on the underlying scheme of `Z` along the first projection of the
fibre product and then along the comparison of Stacks 04IR is restricting it along the second
projection of the product `T ⨯ Z`. -/
public theorem comparisonComp_objStarPullbackIso :
    objBaseChangeSharp B S hS T ≫
        (Functor.sheafPushforwardContinuousNatTrans (objStarPullbackIso B S hS T).hom RingCat.{u}
          (topology B S hS)
          (topology B (objScheme B S hS T) (contains_objScheme B S hS T))).app
          (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)) =
      SheafOfModules.comparisonComp (SheafOfModules.pushforwardOver T)
        (objForwardSharp B S hS T) := by
  ext : 2
  funext Z
  show B.structureSheaf.obj.map
        (Quiver.Hom.op (pullback.fst (Over.hom Z.unop) (Over.hom T))) ≫
      B.structureSheaf.obj.map
        (Quiver.Hom.op ((objStarPullbackIso B S hS T).hom.app Z.unop).left) =
    B.structureSheaf.obj.map
        (Quiver.Hom.op (prod.snd : T ⨯ Z.unop ⟶ Z.unop).left) ≫ 𝟙 _
  exact (B.structureSheaf.obj.map_comp _ _).symm.trans
    ((congrArg (fun k ↦ B.structureSheaf.obj.map (Quiver.Hom.op k))
      (objStarPullbackIso_hom_app_left B S hS T Z.unop)).trans (Category.comp_id _).symm)

/-- The pushforward of sheaves of modules from the big fppf site of the scheme of `T` to that of
`S`: a module is read on the localization at `T` by the equivalence of Stacks 06WI and then pushed
forward along the product with `T`. -/
public noncomputable abbrev objStarPushforward :
    SheafOfModules.{u}
        (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)) ⥤
      SheafOfModules.{u} (structureSheaf B S hS) :=
  haveI := isContinuous_objEquiv_inverse B S hS T
  SheafOfModules.pushforward.{u} (objForwardSharp B S hS T) ⋙
    SheafOfModules.pushforward.{u}
      (SheafOfModules.pushforwardOver (R := structureSheaf B S hS) T)

/-- The pushforward along base change along the structure morphism of `T` is isomorphic to
`AlgebraicGeometry.BigFppfOver.objStarPushforward`, the pushforward along the product with `T`
preceded by the forward reindexing of Stacks 06WI. -/
public noncomputable def objStarPullbackPushforwardIso :
    SheafOfModules.pushforward.{u} (objBaseChangeSharp B S hS T) ≅
      objStarPushforward B S hS T :=
  haveI := isContinuous_objEquiv_inverse B S hS T
  haveI := isContinuous_starObjEquivInverse B S hS T
  SheafOfModules.pushforwardCongr₂.{u} _ (objStarPullbackIso B S hS T)
    (comparisonComp_objStarPullbackIso B S hS T) ≪≫
    (SheafOfModules.pushforwardComp.{u}
      (SheafOfModules.pushforwardOver (R := structureSheaf B S hS) T)
      (objForwardSharp B S hS T)).symm

end AlgebraicGeometry.BigFppfOver

end
