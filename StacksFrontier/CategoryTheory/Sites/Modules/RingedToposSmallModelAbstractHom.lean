module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSmallModel

/-!
# The equi-universe small model of a ringed topos, compared abstractly

`AlgebraicGeometry.RingedTopos.toSmallModelHom` and
`AlgebraicGeometry.RingedTopos.fromSmallModelHom` compare a ringed topos with its equi-universe
model as `AlgebraicGeometry.RingedToposSiteHom`s: their geometric datum is the continuous functor
comparing the site with a small model of it.  Part of the ringed-topos development — the
localization of Stacks 04IF, the flatness statement of Stacks 05VD — is stated instead for an
`AlgebraicGeometry.RingedToposHom`, whose geometric datum is a morphism of the underlying
*topoi*.  This file records the same two comparisons in that shape, at free universes.

Nothing new is proved.  The morphism of topoi is Mathlib's equivalence of sheaf categories
`CategoryTheory.Equivalence.sheafCongr` for the comparison of the site with its small model, read
as an adjunction; the structure map is
`AlgebraicGeometry.RingedTopos.smallModelStructureIso`, read through the identification of the
abstract direct image of sheaves of commutative rings with restriction along the comparison of
sites.

## Main definitions

* `AlgebraicGeometry.RingedTopos.smallModelToposMorphism`: the comparison of the model with the
  ringed topos it models, as a morphism of topoi.
* `AlgebraicGeometry.RingedTopos.pushforwardCommRingIsoSmallModel`: the abstract direct image of
  sheaves of commutative rings along that morphism of topoi is restriction along the comparison
  of sites.
* `AlgebraicGeometry.RingedTopos.toSmallModelAbstractHom`: the comparison as an
  `AlgebraicGeometry.RingedToposHom` `(model) ⟶ X`.
* `AlgebraicGeometry.RingedTopos.fromSmallModelAbstractHom`: its inverse, `X ⟶ (model)`.

## Main results

* `AlgebraicGeometry.RingedTopos.isEquivalence_smallModelToposMorphism_pushforward` and
  `AlgebraicGeometry.RingedTopos.isIso_toSmallModelAbstractHom_fSharp`: the comparison is an
  *equivalence* of ringed topoi — its direct image of sheaves of sets is an equivalence of
  categories and its structure map is an isomorphism.  These are what make
  `AlgebraicGeometry.RingedToposHom.inverse` available, and so what makes the transport of a
  morphism of ringed topoi to the model lose nothing.

## Implementation notes

The direct image of sheaves of sets is an equivalence *because it is the inverse of
`CategoryTheory.Equivalence.sheafCongr`*, on the nose, so the instance is
`inferInstanceAs`.  The two instances about the structure projection
`(toSmallModelAbstractHom X).toToposHom` are restatements: a structure projection does not unfold
at instance transparency, so the instance found at the unprojected spelling is not found at the
projected one, which is the spelling `AlgebraicGeometry.RingedToposHom.inverse` demands.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w v u

namespace AlgebraicGeometry.RingedTopos

variable (X : RingedTopos.{v, u, w}) [EssentiallySmall.{w} X.C]

/-- **The comparison of the equi-universe model with the ringed topos it models, as a morphism of
topoi.**  Its inverse image is restriction of sheaves of sets along the comparison of the site
with its small model and its direct image is restriction back along it; the two are the functor
and the inverse of Mathlib's equivalence of sheaf categories
`CategoryTheory.Equivalence.sheafCongr`, on the nose, so the adjunction is that equivalence read
as an adjunction and the left exactness of the inverse image is unconditional. -/
def smallModelToposMorphism :
    MorphismOfTopoi (smallModel.{w} X.J X.O).Topos X.Topos where
  inverseImage := (equivSmallModel.{w} X.C).inverse.sheafPushforwardContinuous (Type w)
    (smallModelTopology.{w} X.J) X.J
  pushforward := (equivSmallModel.{w} X.C).functor.sheafPushforwardContinuous (Type w)
    X.J (smallModelTopology.{w} X.J)
  adj := (Equivalence.sheafCongr X.J (smallModelTopology.{w} X.J)
    (equivSmallModel.{w} X.C) (Type w)).toAdjunction
  preservesFiniteLimits := Functor.preservesFiniteLimits_sheafPushforwardContinuous
    (smallModelTopology.{w} X.J) X.J (equivSmallModel.{w} X.C).inverse (Type w)

/-- The direct image of sheaves of sets along the comparison is an equivalence of topoi, being
the inverse of `CategoryTheory.Equivalence.sheafCongr`. -/
instance isEquivalence_smallModelToposMorphism_pushforward :
    (smallModelToposMorphism.{w} X).pushforward.IsEquivalence :=
  inferInstanceAs ((Equivalence.sheafCongr X.J (smallModelTopology.{w} X.J)
    (equivSmallModel.{w} X.C) (Type w)).inverse.IsEquivalence)

variable [X.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **The abstract direct image of sheaves of commutative rings along the comparison is
restriction along the comparison of sites.**  The identification is the identity on sections. -/
def pushforwardCommRingIsoSmallModel :
    pushforwardCommRingFunctor.{w, w, w, w, v, u} (smallModelToposMorphism.{w} X) ≅
      (equivSmallModel.{w} X.C).functor.sheafPushforwardContinuous CommRingCat.{w}
        X.J (smallModelTopology.{w} X.J) :=
  NatIso.ofComponents
    (fun O ↦ restrictionCommRingIso X.J (smallModelTopology.{w} X.J)
      (equivSmallModel.{w} X.C).functor O)
    (fun a ↦ restrictionCommRingIso_naturality X.J (smallModelTopology.{w} X.J)
      (equivSmallModel.{w} X.C).functor a)

/-- **The comparison of the model with the ringed topos it models, as an abstract morphism of
ringed topoi** `(model) ⟶ X`.  The geometric datum is
`AlgebraicGeometry.RingedTopos.smallModelToposMorphism` and the structure map is the unit
isomorphism `AlgebraicGeometry.RingedTopos.smallModelStructureIso` read through
`AlgebraicGeometry.RingedTopos.pushforwardCommRingIsoSmallModel`. -/
def toSmallModelAbstractHom : RingedToposHom (smallModel.{w} X.J X.O) X where
  toToposHom := smallModelToposMorphism.{w} X
  fSharp := (smallModelStructureIso.{w} X.J X.O).hom ≫
    ((pushforwardCommRingIsoSmallModel.{w} X).app (smallModelStructureSheaf.{w} X.J X.O)).inv

/-- The morphism of topoi underlying `AlgebraicGeometry.RingedTopos.toSmallModelAbstractHom` is
`AlgebraicGeometry.RingedTopos.smallModelToposMorphism`. -/
@[simp]
theorem toSmallModelAbstractHom_toToposHom :
    (toSmallModelAbstractHom.{w} X).toToposHom = smallModelToposMorphism.{w} X := rfl

/-- The structure map of `AlgebraicGeometry.RingedTopos.toSmallModelAbstractHom` is
`AlgebraicGeometry.RingedTopos.smallModelStructureIso` followed by the inverse of the component of
`AlgebraicGeometry.RingedTopos.pushforwardCommRingIsoSmallModel` at the structure sheaf. -/
@[simp]
theorem toSmallModelAbstractHom_fSharp :
    (toSmallModelAbstractHom.{w} X).fSharp = (smallModelStructureIso.{w} X.J X.O).hom ≫
      ((pushforwardCommRingIsoSmallModel.{w} X).app
        (smallModelStructureSheaf.{w} X.J X.O)).inv := rfl

/-- **The structure map of the comparison is an isomorphism**, being a composite of two
isomorphisms.  With the direct image an equivalence of topoi, this says that the comparison is an
equivalence of ringed topoi and not merely a morphism. -/
instance isIso_toSmallModelAbstractHom_fSharp :
    IsIso (toSmallModelAbstractHom.{w} X).fSharp :=
  (smallModelStructureIso.{w} X.J X.O ≪≫
    ((pushforwardCommRingIsoSmallModel.{w} X).app
      (smallModelStructureSheaf.{w} X.J X.O)).symm).isIso_hom

/-- The direct image of sheaves of sets along the morphism of topoi underlying
`AlgebraicGeometry.RingedTopos.toSmallModelAbstractHom` is an equivalence of categories. -/
instance isEquivalence_toSmallModelAbstractHom_pushforward :
    (toSmallModelAbstractHom.{w} X).toToposHom.pushforward.IsEquivalence :=
  isEquivalence_smallModelToposMorphism_pushforward.{w} X

/-- **The inverse of the comparison**, an abstract morphism of ringed topoi `X ⟶ (model)`.  Its
geometric datum is the comparison's read backwards and its structure map is the inverse of the
inverse-image form of the comparison's. -/
def fromSmallModelAbstractHom : RingedToposHom X (smallModel.{w} X.J X.O) :=
  (toSmallModelAbstractHom.{w} X).inverse

end AlgebraicGeometry.RingedTopos

end
