module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousSquareObjectwise
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteSheafPushforwardBaseChange

/-!
# The identity `f'_*(g')^{-1} = g^{-1}f_*` of Stacks 07AT on abelian sheaves

Let `f : 𝒳 ⟶ 𝒴` be a smooth (respectively flat) 1-morphism of algebraic stacks, `f'` its
restriction to the lisse-étale (respectively flat-fppf) sites and `g`, `g'` the inclusions of
those sites. The canonical map `g^{-1}f_* ⟶ f'_*(g')^{-1}` of Sites, Section 06UM is invertible
on sheaves of sets: that is
`AlgebraicGeometry.Stack.LisseEtale.bijective_subsiteRanBaseChange` and its flat-fppf sibling.
This file proves the same on **abelian** sheaves, which is the form Stacks 0GR3 consumes.

The canonical map on abelian sheaves is the base change transformation
`CategoryTheory.TwoSquare.ranBaseChange` of the commuting square of `f`, `f'` and the two
inclusions, with abelian coefficients. Its invertibility is reduced to the case of sets by
`Stacks.SheafOfModules.isIso_map_ranBaseChange_app_app_iff`: the forgetful functor of abelian
groups preserves the limits computing the right Kan extensions involved, being a right adjoint,
and reflects isomorphisms.

## Main definitions

* `CategoryTheory.SubsitePushforward.subsiteAbelianSheafBaseChange`: the canonical map
  `g^{-1}f_* ⟶ f'_*(g')^{-1}` on abelian sheaves.

## Main results

* `CategoryTheory.SubsitePushforward.isIso_subsiteAbelianSheafBaseChange`: it is invertible as soon
  as the canonical map of presheaves of sets is bijective at every sheaf.
* `AlgebraicGeometry.Stack.LisseEtale.isIso_abelianSheafBaseChange`: **Stacks 07AT** (1), the
  identity `f'_*(g')^{-1} = g^{-1}f_*` on abelian sheaves.
* `AlgebraicGeometry.Stack.FlatFppf.isIso_abelianSheafBaseChange`: **Stacks 07AT** (2), the same.

## References

* [Stacks Project, Tag 06UM](https://stacks.math.columbia.edu/tag/06UM)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SubsitePushforward

universe u₂ u₃ v₂ v₃ w

variable {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₃} 𝒴]
  (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳) {Q : ObjectProperty 𝒴}
  (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj))
  (J𝒳 : GrothendieckTopology 𝒳) (J𝒴 : GrothendieckTopology 𝒴)
  (J𝒳' : GrothendieckTopology P.FullSubcategory) (J𝒴' : GrothendieckTopology Q.FullSubcategory)
  [f.IsCocontinuous J𝒳 J𝒴] [(subsiteFunctor f P hPQ).IsCocontinuous J𝒳' J𝒴']
  [P.ι.IsContinuous J𝒳' J𝒳] [Q.ι.IsContinuous J𝒴' J𝒴]
  [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (subsiteFunctor f P hPQ).op.HasPointwiseRightKanExtension G]
  [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{w}, f.op.HasPointwiseRightKanExtension G]

/-- **The canonical map `g^{-1}f_* ⟶ f'_*(g')^{-1}` on abelian sheaves**, the base-change
transformation of the commuting square of `f`, its restriction `f'` and the two inclusions, read
on sheaves: the direct images are right Kan extensions of the underlying presheaves and the
inverse images are restrictions. This is the canonical map of Sites, Section 06UM. -/
def subsiteAbelianSheafBaseChange :
    f.sheafPushforwardCocontinuous AddCommGrpCat.{w} J𝒳 J𝒴 ⋙
        Q.ι.sheafPushforwardContinuous AddCommGrpCat.{w} J𝒴' J𝒴 ⟶
      P.ι.sheafPushforwardContinuous AddCommGrpCat.{w} J𝒳' J𝒳 ⋙
        (subsiteFunctor f P hPQ).sheafPushforwardCocontinuous AddCommGrpCat.{w} J𝒳' J𝒴' where
  app G := ObjectProperty.homMk
    (((subsiteRanSquare f P hPQ).ranBaseChange (D := AddCommGrpCat.{w})).app G.obj)
  naturality _ _ φ := ObjectProperty.hom_ext _
    (((subsiteRanSquare f P hPQ).ranBaseChange (D := AddCommGrpCat.{w})).naturality φ.hom)

variable [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w,
    (subsiteFunctor f P hPQ).op.HasPointwiseRightKanExtension G]
  [∀ G : 𝒳ᵒᵖ ⥤ Type w, f.op.HasPointwiseRightKanExtension G]

/-- **The canonical map on abelian sheaves is invertible when the one on sheaves of sets is.** If
the canonical map of presheaves of sets is bijective at every object of the subsite of `𝒴`, at the
underlying presheaf of sets of every abelian sheaf, then `g^{-1}f_* ⟶ f'_*(g')^{-1}` is an
isomorphism of functors on abelian sheaves. -/
theorem isIso_subsiteAbelianSheafBaseChange
    (H : ∀ (G : Sheaf J𝒳 AddCommGrpCat.{w}) (y : Q.FullSubcategory),
      Function.Bijective (((subsiteRanBaseChange f P hPQ).app
        (G.obj ⋙ forget AddCommGrpCat.{w})).app (op y))) :
    IsIso (subsiteAbelianSheafBaseChange f P hPQ J𝒳 J𝒴 J𝒳' J𝒴') := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro G
  have hT : IsIso ((subsiteRanBaseChange f P hPQ).app (G.obj ⋙ forget AddCommGrpCat.{w})) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun z => (isIso_iff_bijective _).mpr (H G z.unop)
  have hA : IsIso (((subsiteRanSquare f P hPQ).ranBaseChange (D := AddCommGrpCat.{w})).app
      G.obj) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro z
    have := (Stacks.SheafOfModules.isIso_map_ranBaseChange_app_app_iff
      (subsiteRanSquare f P hPQ) (forget AddCommGrpCat.{w}) G.obj z).2
        (inferInstanceAs (IsIso (((subsiteRanBaseChange f P hPQ).app
          (G.obj ⋙ forget AddCommGrpCat.{w})).app z)))
    exact isIso_of_reflects_iso _ (forget AddCommGrpCat.{w})
  have h' : IsIso ((sheafToPresheaf J𝒴' AddCommGrpCat.{w}).map
    ((subsiteAbelianSheafBaseChange f P hPQ J𝒳 J𝒴 J𝒳' J𝒴').app G)) := hA
  exact isIso_of_reflects_iso _ (sheafToPresheaf J𝒴' AddCommGrpCat.{w})

end CategoryTheory.SubsitePushforward

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

attribute [local instance] hasPointwiseRightKanExtension_homFunctor

/-- The underlying presheaf of sets of an abelian sheaf is a sheaf of sets. -/
theorem isSheaf_comp_forget_of_sheaf {C : Type*} [Category C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) : Presieve.IsSheaf J (G.obj ⋙ forget AddCommGrpCat.{w}) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf J G.obj (forget AddCommGrpCat.{w}) G.property)

namespace LisseEtale

attribute [local instance] hasPointwiseRightKanExtension_inclusion_comp_homFunctor
  hasPointwiseRightKanExtension_primedSiteFunctor

variable (hf : AlgebraicStacks.IsSmooth B S hS f)

/-- **Stacks 07AT** (1) on abelian sheaves: for a smooth 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks, the canonical map `g^{-1}f_* ⟶ f'_*(g')^{-1}` of Sites, Section 06UM, from the restriction
to the lisse-étale site of `𝒴` of the direct image along `f` to the direct image along the
restriction `f'` of the restriction to the lisse-étale site of `𝒳`, is an isomorphism of functors
on abelian sheaves. -/
theorem isIso_abelianSheafBaseChange :
    letI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
      (etaleTopology B)).2
    letI := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
    letI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    letI := isContinuous_inclusion.{u, w} B S hS 𝒴 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒴)
    IsIso (SubsitePushforward.subsiteAbelianSheafBaseChange.{_, _, _, _, u + 1}
      f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳) (smoothObject_map.{u, w} B S hS f hf)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
      (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴)) :=
  let := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).2
  let := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
  let := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  let := isContinuous_inclusion.{u, w} B S hS 𝒴 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒴)
  SubsitePushforward.isIso_subsiteAbelianSheafBaseChange _ _ _ _ _ _ _
    (fun G y => bijective_subsiteRanBaseChange B S hS f hf _ (isSheaf_comp_forget_of_sheaf G) y)

end LisseEtale

namespace FlatFppf

attribute [local instance] hasPointwiseRightKanExtension_inclusion_comp_homFunctor
  hasPointwiseRightKanExtension_primedSiteFunctor

variable (hf : AlgebraicStacks.IsFlat B S hS f)

/-- **Stacks 07AT** (2) on abelian sheaves: for a flat 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks, the canonical map `g^{-1}f_* ⟶ f'_*(g')^{-1}` of Sites, Section 06UM, from the restriction
to the flat-fppf site of `𝒴` of the direct image along `f` to the direct image along the
restriction `f'` of the restriction to the flat-fppf site of `𝒳`, is an isomorphism of functors
on abelian sheaves. -/
theorem isIso_abelianSheafBaseChange :
    letI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
    letI := isCocontinuous_subsiteFunctor B S hS f hf
    letI := isContinuous_inclusion' B S hS 𝒳
    letI := isContinuous_inclusion' B S hS 𝒴
    IsIso (SubsitePushforward.subsiteAbelianSheafBaseChange.{_, _, _, _, u + 1}
      f.hom.hom.toFunctor (flatObject B S hS 𝒳.val) (flatObject_map B S hS f hf)
      (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology)
      (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴)) :=
  let := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
  let := isCocontinuous_subsiteFunctor B S hS f hf
  let := isContinuous_inclusion' B S hS 𝒳
  let := isContinuous_inclusion' B S hS 𝒴
  SubsitePushforward.isIso_subsiteAbelianSheafBaseChange _ _ _ _ _ _ _
    (fun G y => bijective_subsiteRanBaseChange B S hS f hf _ (isSheaf_comp_forget_of_sheaf G) y)

end FlatFppf

end AlgebraicGeometry.Stack
