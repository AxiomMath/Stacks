module

public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackRestrictionImmersion
public import StacksFrontier.CategoryTheory.FiberedCategory.CoGrothendieckMapEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.OfPresheaf
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.UliftHomEquivalenceOver

/-!
# Isomorphic presheaves of groupoids present equivalent categories fibred in groupoids

Let `F` and `G` be presheaves of groupoids on a category `𝒞` and let `η : F ≅ G` be an isomorphism
between them. The Grothendieck construction turns each into a category fibred in
groupoids over `𝒞`, and `CategoryTheory.presheafOfGroupoidsMap` turns `η.hom` into a 1-morphism
between them. This file records that that 1-morphism is an **equivalence over `𝒞`** in the sense of
`CategoryTheory.Functor.IsEquivalenceOver`, and that so is its morphism-universe lift.

## Main results

* `CategoryTheory.full_presheafOfGroupoidsMap` and
  `CategoryTheory.faithful_presheafOfGroupoidsMap`: the induced 1-morphism is fully faithful.
* `CategoryTheory.isFibredOneMorphism_presheafOfGroupoidsMap`: the 1-morphism induced by any
  morphism of presheaves of groupoids is a 1-morphism of fibred categories over `𝒞`.
* `CategoryTheory.isEquivalenceOver_presheafOfGroupoidsMap`: it is an equivalence over `𝒞` when the
  morphism is an isomorphism.
* `CategoryTheory.isEquivalenceOver_uliftHomMap_presheafOfGroupoidsMap`: so is its
  morphism-universe lift.

## References

* [Stacks Project, Tag 0049](https://stacks.math.columbia.edu/tag/0049)
* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
-/

@[expose] public section

open CategoryTheory Opposite Pseudofunctor
open scoped Pseudofunctor.CoGrothendieck Pseudofunctor.StrongTrans

universe v₁ v₂ v₃ u₁ u₂

namespace CategoryTheory

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {F G : 𝒞ᵒᵖ ⥤ Grpd.{v₂, u₂}}

/-! ### The components are isomorphisms of categories -/

/-- Every component of the strong transformation underlying
`CategoryTheory.presheafOfGroupoidsMap η.hom` is an isomorphism of `Cat`. -/
theorem isIso_app_strongTransOfNatTrans_whiskerRight (η : F ≅ G) (a : LocallyDiscrete 𝒞ᵒᵖ) :
    IsIso ((strongTransOfNatTrans (Functor.whiskerRight η.hom Grpd.forgetToCat)).app a) :=
  (Grpd.forgetToCat.mapIso (Iso.app η a.as)).isIso_hom

/-! ### The induced 1-morphism is fully faithful -/

/-- The 1-morphism induced by an isomorphism of presheaves of groupoids is full. -/
theorem full_presheafOfGroupoidsMap (η : F ≅ G) : (presheafOfGroupoidsMap η.hom).Full :=
  Pseudofunctor.CoGrothendieck.full_map _
    (fun a => have := isIso_app_strongTransOfNatTrans_whiskerRight η a
      Pseudofunctor.CoGrothendieck.full_of_isIso _)
    (fun a => have := isIso_app_strongTransOfNatTrans_whiskerRight η a
      Pseudofunctor.CoGrothendieck.faithful_of_isIso _)

/-- The 1-morphism induced by an isomorphism of presheaves of groupoids is faithful. -/
theorem faithful_presheafOfGroupoidsMap (η : F ≅ G) : (presheafOfGroupoidsMap η.hom).Faithful :=
  Pseudofunctor.CoGrothendieck.faithful_map _
    (fun a => have := isIso_app_strongTransOfNatTrans_whiskerRight η a
      Pseudofunctor.CoGrothendieck.faithful_of_isIso _)

/-- Every object of the target Grothendieck construction is, over an identity of `𝒞`, isomorphic
to an image of the 1-morphism induced by an isomorphism of presheaves of groupoids. -/
theorem hasVerticalPreimages_presheafOfGroupoidsMap (η : F ≅ G) :
    Functor.HasVerticalPreimages (presheafOfGroupoids F).p (presheafOfGroupoids G).p
      (presheafOfGroupoidsMap η.hom) :=
  Pseudofunctor.CoGrothendieck.hasVerticalPreimages_map _
    (isIso_app_strongTransOfNatTrans_whiskerRight η)

/-! ### 1-morphism of fibred categories, and the equivalence over the base -/

/-- The functor induced by a morphism of presheaves of groupoids is a 1-morphism of fibred
categories over `𝒞`. -/
theorem isFibredOneMorphism_presheafOfGroupoidsMap (η : F ⟶ G) :
    (presheafOfGroupoids F).p.IsFibredOneMorphism (presheafOfGroupoids G).p
      (presheafOfGroupoidsMap η) where
  comp_eq := presheafOfGroupoidsMap_comp η
  map_isStronglyCartesian := by
    intro R T f a b φ h
    have hlift := Functor.isHomLift_map_of_comp_eq (presheafOfGroupoidsMap_comp η) f φ
    exact (isFiberedInGroupoids_presheafOfGroupoids G).isStronglyCartesian_homLift f _

/-- The 1-morphism induced by an isomorphism of presheaves of groupoids is an equivalence over
`𝒞`. -/
noncomputable def isEquivalenceOver_presheafOfGroupoidsMap (η : F ≅ G) :
    Functor.IsEquivalenceOver (presheafOfGroupoids F).p (presheafOfGroupoids G).p
      (presheafOfGroupoidsMap η.hom) :=
  Pseudofunctor.CoGrothendieck.isEquivalenceOver_map _
    (isIso_app_strongTransOfNatTrans_whiskerRight η)

/-- The morphism-universe lift of the 1-morphism induced by an isomorphism of presheaves of
groupoids is an equivalence over `𝒞`. -/
noncomputable def isEquivalenceOver_uliftHomMap_presheafOfGroupoidsMap (η : F ≅ G) :
    Functor.IsEquivalenceOver
      (Functor.uliftHomProj (presheafOfGroupoids F).p :
        ULiftHom.{v₃} (presheafOfGroupoids F).obj ⥤ 𝒞)
      (Functor.uliftHomProj (presheafOfGroupoids G).p :
        ULiftHom.{v₃} (presheafOfGroupoids G).obj ⥤ 𝒞)
      (Functor.uliftHomMap (presheafOfGroupoidsMap η.hom) :
        ULiftHom.{v₃} (presheafOfGroupoids F).obj ⥤ ULiftHom.{v₃} (presheafOfGroupoids G).obj) :=
  Functor.isEquivalenceOver_uliftHomMap (presheafOfGroupoidsMap_comp η.hom)
    (full_presheafOfGroupoidsMap η) (faithful_presheafOfGroupoidsMap η)
    (hasVerticalPreimages_presheafOfGroupoidsMap η)

end CategoryTheory

end
