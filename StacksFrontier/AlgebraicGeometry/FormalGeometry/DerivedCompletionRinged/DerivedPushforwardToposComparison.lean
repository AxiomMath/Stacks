module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi
import StacksCore.Tactic.StacksAttribute

/-!
# The unbounded derived direct image does not depend on the presentation of the morphism

A morphism of ringed sites `f : X ⟶ Y` presents a morphism of ringed topoi in two ways: as the
two-field `AlgebraicGeometry.RingedToposHom`, whose geometric morphism is an adjoint pair, and as
the site-presented `AlgebraicGeometry.RingedToposSiteHom`, whose geometric morphism is the
continuous functor of the underlying sites. Each has its own unbounded derived direct image, and
`AlgebraicGeometry.RingedSite.Hom.pushforwardToposIso` already identifies the two underived
direct images of sheaves of modules. This file carries that identification to the total right
derived functors: they are right derived functors of isomorphic functors on the homotopy
category, so `CategoryTheory.Functor.rightDerivedNatIso` compares them.

This is one of the identifications the reduction of [Stacks, Tag 03CR] needs in order to state
[Stacks, Tag 099J] for a morphism of ringed topoi: the ringed-sites proof of Tag 099J is written
with the site-presented derived direct image, while the square of Tag 03CR is a square of
two-field morphisms of ringed topoi.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.pushforwardHomotopyToposIso`: the two degreewise direct
  images on the homotopy category agree.
* `AlgebraicGeometry.RingedSite.Hom.derivedPushforwardToposIso`: the two unbounded derived
  direct images agree.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] CategoryTheory.sheafCompose
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)

attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

/-- Additivity of the direct image of the two-field presentation, at the universes of a
morphism of ringed sites. It must be the global instance's own term: the additivity is an
instance argument of `CategoryTheory.Functor.mapHomotopyCategory`, so a second proof of it
would give a second degreewise direct image, and the right-derived-functor instances of
`Stacks.Cohomology.DerivedPushforward` are registered at the global one. -/
local instance additive_pushforwardModules :
    (AlgebraicGeometry.RingedToposHom.pushforwardModules f.ringedToposHom).Additive :=
  AlgebraicGeometry.RingedToposHom.pushforwardModules_additive f.ringedToposHom

/-- Existence of the unbounded right derived functor of the degreewise direct image of the
two-field presentation, at the universes of a morphism of ringed sites. -/
local instance hasPointwiseRightDerivedFunctor_pushforwardOnHomotopy :
    (Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy.{u, u, u, u, u, u}
      f.ringedToposHom).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
        (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy_hasRightDerivedFunctor
    f.ringedToposHom

/-- **The two degreewise direct images of complexes agree.** This is
`AlgebraicGeometry.RingedSite.Hom.pushforwardToposIso` applied degreewise, which is functorial
in the direct image by `CategoryTheory.NatTrans.mapHomotopyCategory`. -/
def Hom.pushforwardHomotopyToposIso :
    (AlgebraicGeometry.RingedToposHom.pushforwardModules
        f.ringedToposHom).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      f.toRingedToposSiteHom.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ) := by
  letI : f.toRingedToposSiteHom.pushforwardTopos.Additive := f.pushforwardTopos_additive
  letI : f.ringedToposHom.pushforwardModules.Additive :=
    AlgebraicGeometry.RingedToposHom.pushforwardModules_additive f.ringedToposHom
  exact {
    hom := NatTrans.mapHomotopyCategory
      (F := f.ringedToposHom.pushforwardModules) (G := f.toRingedToposSiteHom.pushforwardTopos)
      f.pushforwardToposIso.hom (ComplexShape.up ℤ)
    inv := NatTrans.mapHomotopyCategory
      (F := f.toRingedToposSiteHom.pushforwardTopos) (G := f.ringedToposHom.pushforwardModules)
      f.pushforwardToposIso.inv (ComplexShape.up ℤ)
    hom_inv_id := by
      rw [← NatTrans.mapHomotopyCategory_comp, f.pushforwardToposIso.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
    inv_hom_id := by
      rw [← NatTrans.mapHomotopyCategory_comp, f.pushforwardToposIso.inv_hom_id,
        NatTrans.mapHomotopyCategory_id] }

/-- **The unbounded derived direct image does not depend on the presentation of the morphism of
ringed topoi.** Both are total right derived functors, along `DerivedCategory.Qh` and at the
quasi-isomorphisms, of the two degreewise direct images, and those are isomorphic by
`AlgebraicGeometry.RingedSite.Hom.pushforwardHomotopyToposIso`. -/
def Hom.derivedPushforwardToposIso :
    Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u, u, u}
        f.ringedToposHom ≅
      derivedPushforward.{u} f.toRingedToposSiteHom := by
  letI : (DerivedCategory.Qh (C := SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).IsLocalization
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ)) :=
    DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhQuasiIso
  letI : (pushforwardOnHomotopy.{u} f.toRingedToposSiteHom).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ)) :=
    pushforward_hasRightDerivedFunctor f.toRingedToposSiteHom
  -- the two constructions register their right-derived-functor instances at two spellings of
  -- the ring sheaf of `X`, which are the same sheaf; the statement below is at the spelling of
  -- the two-field presentation, and the site-presented instance is carried across.
  haveI hsite : (derivedPushforward.{u} f.toRingedToposSiteHom).IsRightDerivedFunctor
      (derivedPushforwardUnit.{u} f.toRingedToposSiteHom)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
        (ComplexShape.up ℤ)) :=
    Functor.instIsRightDerivedFunctorTotalRightDerivedTotalRightDerivedUnit
      (pushforwardOnHomotopy.{u} f.toRingedToposSiteHom)
      (DerivedCategory.Qh (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ))
  exact Functor.rightDerivedNatIso
    (Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u, u, u}
      f.ringedToposHom)
    (derivedPushforward.{u} f.toRingedToposSiteHom)
    ((Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy.{u, u, u, u, u, u}
      f.ringedToposHom).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
          (ComplexShape.up ℤ)))
    (derivedPushforwardUnit.{u} f.toRingedToposSiteHom)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
      (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight f.pushforwardHomotopyToposIso DerivedCategory.Qh)

end AlgebraicGeometry.RingedSite

end
