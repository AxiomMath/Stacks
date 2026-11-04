module

public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Morphism
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute

/-!
# The ringed total site of a simplicial semi-representable localization

Let `X` be a ringed site and `K` a simplicial semi-representable object of its underlying site.
The total localization of `K` carries the pulled-back structure sheaf `a⁻¹ O_X`, and the pair is
again a ringed site. The canonical augmentation of the total localization is then a morphism of
ringed topoi to the ringed topos of `X`: its underlying geometric morphism is the localization
augmentation, and its structure map is adjoint to the identification of the pulled-back
structure sheaf with the inverse image of `O_X` on sheaves of commutative rings.

The localized situation of a site with a sheaf of rings, an object `X` of it, and a simplicial
semi-representable object of the slice category over `X` is bundled as
`LocalizedRingedSituation`; the construction above applies to its slice ringed site.

## Main definitions

* `AlgebraicGeometry.SemiRepresentable.Simplicial.LocalizedRingedSituation`: a site with a sheaf
  of commutative rings, an object of the site, and a simplicial semi-representable object of the
  slice category over that object.
* `AlgebraicGeometry.SemiRepresentable.Simplicial.totalRingedSite`: the total localization
  together with the pulled-back structure sheaf, as a ringed site.
* `AlgebraicGeometry.SemiRepresentable.Simplicial.ringedAugmentation`: the canonical morphism of
  ringed topoi from the total localization to the base.

## Implementation notes

A `AlgebraicGeometry.RingedTopos` takes its structure sheaf in the same universe as the sets its
topos is made of, while the localization augmentation enlarges that universe to accommodate the
right Kan extension defining its direct image. The augmentation is therefore built for a ringed
site whose sections already live in a universe containing the site and the simplicial
semi-representable object (`ringedAugmentationOfLargeSections`), and the general case is obtained
by lifting the sections of the structure sheaf into such a universe
(`liftedRingedSite`).

The structure map is adjoint to
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, which identifies the inverse image of a
sheaf of commutative rings along restriction with that restriction itself; this pins the
structure map down rather than leaving it an arbitrary isomorphism.

## References

* [Stacks Project, Tag 0D9X](https://stacks.math.columbia.edu/tag/0D9X)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SemiRepresentable.Simplicial
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe x v u w

namespace AlgebraicGeometry.SemiRepresentable.Simplicial

/-- A site with a sheaf of commutative rings, an object `X` of the site, and a simplicial
semi-representable object of the slice category over `X`. -/
structure LocalizedRingedSituation.{x', w', v', u'} (C : Type u') [Category.{v'} C] where
  /-- The Grothendieck topology on the underlying category. -/
  J : GrothendieckTopology C
  /-- The sheaf of commutative rings on the site. -/
  O : Sheaf J CommRingCat.{w'}
  /-- The object at which the site is localized. -/
  X : C
  /-- The simplicial semi-representable object of the slice category over `X`. -/
  K : SimplicialObject (FormalCoproduct.{x'} (Over X))

namespace LocalizedRingedSituation

/-- The restriction of the structure sheaf to the slice site over `X`. -/
abbrev OX {C : Type u} [Category.{v} C]
    (S : LocalizedRingedSituation.{x, w, v, u} C) : Sheaf (S.J.over S.X) CommRingCat.{w} :=
  S.O.over S.X

end LocalizedRingedSituation

/-- The total localization of a simplicial semi-representable object over a ringed site, together
with its pulled-back structure sheaf, is a ringed site. -/
@[stacks 0D9X "ringed_total_site"]
def totalRingedSite (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) : AlgebraicGeometry.RingedSite where
  C := TotalLocalization K
  J := totalLocalizationTopology K X.J
  O := pulledBackStructureSheaf X K

/-- Lift a sheaf of commutative rings into any universe containing both its sections and the
site. This is `AlgebraicGeometry.SheafOfModules.sheafULift` with the target universe allowed to
be larger than the one that functor produces. -/
def sheafCommRingULift.{z, uu, vv, ww} {C : Type uu} [Category.{vv} C]
    (J : GrothendieckTopology C) :
    Sheaf J CommRingCat.{ww} ⥤ Sheaf J CommRingCat.{max ww uu vv z} where
  obj O :=
    { obj := O.obj ⋙ AlgebraicGeometry.SheafOfModules.commRingCatULift.{ww, max uu vv z}
      property := by
        have : HasLimitsOfSize.{vv, max vv uu} CommRingCat.{max ww uu vv z} :=
          hasLimitsOfSizeShrink.{vv, max vv uu, max ww uu vv z, max ww uu vv z} _
        refine (Presheaf.isSheaf_iff_isSheaf_comp J _
          (forget CommRingCat.{max ww uu vv z})).mpr ?_
        change Presheaf.IsSheaf J ((O.obj ⋙ forget CommRingCat) ⋙ uliftFunctor.{max uu vv z})
        exact Presheaf.isSheaf_comp_of_isSheaf _ _ _
          ((sheafCompose J (forget CommRingCat)).obj O).property }
  map f := ⟨Functor.whiskerRight f.hom
    AlgebraicGeometry.SheafOfModules.commRingCatULift.{ww, max uu vv z}⟩

/-- A ringed site with the sections of its structure sheaf lifted into a universe large enough
to contain the total localization of a simplicial semi-representable object. -/
abbrev liftedRingedSite (X : AlgebraicGeometry.RingedSite.{u, v, w}) :
    AlgebraicGeometry.RingedSite.{u, v, max x u v w} where
  C := X.C
  J := X.J
  O := (sheafCommRingULift.{x, u, v, w} X.J).obj X.O

/-- The canonical morphism of ringed topoi from the total localization of a simplicial
semi-representable object to its base, for a ringed site whose structure sheaf already has
sections in a universe containing the total localization. -/
def ringedAugmentationOfLargeSections (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    AlgebraicGeometry.RingedToposHom
      (AlgebraicGeometry.RingedSite.ringedTopos.{max x u v, v, w}
        (totalRingedSite.{x, v, u, max x u v w} X K))
      (AlgebraicGeometry.RingedSite.ringedTopos.{u, v, max x w} X) where
  toToposHom := localizationAugmentation.{x, v, u, w} K X.J
  fSharp :=
    (commRingImageAdjunction (localizationAugmentation.{x, v, u, w} K X.J)).homEquiv _ _
      (restrictionCommRingIso (totalLocalizationTopology K X.J) X.J
        (totalLocalizationFunctor K) X.O).hom

/-- The total localization of a simplicial semi-representable object over a ringed site has a
canonical augmentation to the base as a morphism of ringed topoi. -/
@[stacks 0D9X "ringed_augmentation"]
def ringedAugmentation (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    AlgebraicGeometry.RingedToposHom
      (AlgebraicGeometry.RingedSite.ringedTopos.{max x u v, v, w}
        (totalRingedSite.{x, v, u, max x u v w} (liftedRingedSite.{x, v, u, w} X) K))
      (AlgebraicGeometry.RingedSite.ringedTopos.{u, v, max x w}
        (liftedRingedSite.{x, v, u, w} X)) :=
  ringedAugmentationOfLargeSections.{x, v, u, w} (liftedRingedSite.{x, v, u, w} X) K

end AlgebraicGeometry.SemiRepresentable.Simplicial

end
