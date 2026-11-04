module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomLocal
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackToposSquare
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map of Stacks 0GMX and restriction to a slice site

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites, given by a continuous functor
`u : D ⥤ C`, let `F`, `G` be sheaves of `O_D`-modules and let `V` be an object of `D`. The
canonical map `f^* Hom_{O_D}(F, G) ⟶ Hom_{O_C}(f^*F, f^*G)` of Stacks 0GMX and the canonical map
of the morphism `f_V` that Stacks 04J0 localizes `f` to at `V` run between objects that the two
localization results of the development identify: the base change of Tag 04J0 and the
localization of internal Hom of Tag 0E8H. This file assembles those identifications into the two
legs of the square comparing the two maps, and records that the restriction of the canonical map
is invertible as soon as that square commutes and the localized canonical map is.

This is the step the proof of Stacks 0GN2 for a locally finitely presented `F` needs: the
covering of `C` by objects `u(V)` over which `F` acquires a finite global presentation is
`Stacks.SheafOfModules.InternalHom.coversTop_obj_hasFiniteGlobalPresentation`, invertibility is
local on `C` in the restriction form
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over`, and the global case over a
presentation-as-a-property is
`Stacks.SheafOfModules.InternalHom.isIso_pullbackInternalHomMap_of_hasFiniteGlobalPresentation`.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.restrictedPullbackIso`: **Tag 04J0** for the pullback of
  sheaves of modules, in the spelling the canonical map of Stacks 0GMX is built with.
* `Stacks.SheafOfModules.InternalHom.restrictionSourceIso` and
  `Stacks.SheafOfModules.InternalHom.restrictionTargetIso`: the two legs comparing the
  restriction of the canonical map of Stacks 0GMX with the canonical map of the localized
  morphism.

## References

* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Stacks.SheafOfModules.InternalHom

universe u

section Restriction

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  (F G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (V : Y.C)

/-- **Tag 04J0 for the pullback of sheaves of modules, at one object and in the spelling the
canonical map of Stacks 0GMX is built with.** Restricting `f^*A` to the slice over `u(V)` is
pulling `A|_V` back along the localized morphism of Stacks 04J0.

The localization square `AlgebraicGeometry.RingedSite.Hom.localizedPullbackToposSquare` is
stated for the site-presented pullback `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`,
whereas `Stacks.SheafOfModules.InternalHom.pullbackInternalHomMap` is built over the pullback of
the two-field morphism of ringed topoi; the two are identified by
`AlgebraicGeometry.RingedSite.Hom.pullbackToposIso`, uniqueness of left adjoints, and the square
is conjugated by it on both sides. -/
noncomputable def restrictedPullbackIso
    (A : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ((ringedSitePullback f).obj A).over (f.u.obj V) ≅
      (ringedSitePullback (f.localized V)).obj (A.over V) :=
  (_root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (f.u.obj V)).mapIso
      ((AlgebraicGeometry.RingedSite.Hom.pullbackToposIso f).app A) ≪≫
    (AlgebraicGeometry.RingedSite.Hom.localizedPullbackToposSquare f V).app A ≪≫
      ((AlgebraicGeometry.RingedSite.Hom.pullbackToposIso (f.localized V)).app (A.over V)).symm

/-- **The source of the restricted canonical map, transported to the localized site.**
Restricting `f^* Hom_{O_D}(F, G)` to the slice over `u(V)` is pulling
`Hom_{O_V}(F|_V, G|_V)` back along the localized morphism: the base change of Tag 04J0 followed
by the localization of internal Hom of Tag 0E8H. -/
noncomputable def restrictionSourceIso :
    ((ringedSitePullback f).obj
        ((internalHomSecondFunctor Y.J Y.O F).obj G)).over (f.u.obj V) ≅
      (ringedSitePullback (f.localized V)).obj
        ((internalHomSecondFunctor (Y.over V).J (Y.over V).O (F.over V)).obj (G.over V)) :=
  restrictedPullbackIso f V ((internalHomSecondFunctor Y.J Y.O F).obj G) ≪≫
    (ringedSitePullback (f.localized V)).mapIso
      ((Stacks.SheafOfModules.ExtensionByZero.internalHomRestrictionNatIso Y V F).app G)

/-- **The target of the restricted canonical map, transported to the localized site.**
Restricting `Hom_{O_C}(f^*F, f^*G)` to the slice over `u(V)` is
`Hom_{O_{u(V)}}(f_V^*(F|_V), f_V^*(G|_V))`: the localization of internal Hom of Tag 0E8H
followed by the base change of Tag 04J0 in each variable, the second variable through the
functoriality of `internalHomSecondFunctor` and the first through the comparison
`Stacks.SheafOfModules.InternalHom.internalHomPre`, which is invertible at an isomorphism. -/
noncomputable def restrictionTargetIso :
    ((internalHomSecondFunctor X.J X.O ((ringedSitePullback f).obj F)).obj
        ((ringedSitePullback f).obj G)).over (f.u.obj V) ≅
      (internalHomSecondFunctor (X.over (f.u.obj V)).J (X.over (f.u.obj V)).O
          ((ringedSitePullback (f.localized V)).obj (F.over V))).obj
        ((ringedSitePullback (f.localized V)).obj (G.over V)) := by
  haveI : IsIso (restrictedPullbackIso f V F).symm.hom :=
    ⟨(restrictedPullbackIso f V F).symm.inv, (restrictedPullbackIso f V F).symm.hom_inv_id,
      (restrictedPullbackIso f V F).symm.inv_hom_id⟩
  haveI : IsIso (internalHomPre (X.over (f.u.obj V)).O (restrictedPullbackIso f V F).symm.hom) :=
    @isIso_internalHomPre (X.over (f.u.obj V)).C (X.over (f.u.obj V)).category
      (X.over (f.u.obj V)).J (X.over (f.u.obj V)).O
      (((ringedSitePullback f).obj F).over (f.u.obj V))
      ((ringedSitePullback (f.localized V)).obj (F.over V))
      (restrictedPullbackIso f V F).symm.hom
      ⟨(restrictedPullbackIso f V F).symm.inv, (restrictedPullbackIso f V F).symm.hom_inv_id,
        (restrictedPullbackIso f V F).symm.inv_hom_id⟩
  exact (Stacks.SheafOfModules.ExtensionByZero.internalHomRestrictionNatIso X (f.u.obj V)
        ((ringedSitePullback f).obj F)).app ((ringedSitePullback f).obj G) ≪≫
    (internalHomSecondFunctor (X.over (f.u.obj V)).J (X.over (f.u.obj V)).O
        (((ringedSitePullback f).obj F).over (f.u.obj V))).mapIso (restrictedPullbackIso f V G) ≪≫
      (asIso (internalHomPre (X.over (f.u.obj V)).O
        (restrictedPullbackIso f V F).symm.hom)).app
          ((ringedSitePullback (f.localized V)).obj (G.over V))

/-- **The restricted canonical map is invertible once it is the localized canonical map read
through the two comparisons.** The hypothesis `hsq` is the commutativity of the square formed by
the restriction of the canonical map of Stacks 0GMX, the canonical map of the localized morphism
of Stacks 04J0, and `restrictionSourceIso`, `restrictionTargetIso`. -/
private theorem isIso_over_of_square
    (h : IsIso (pullbackInternalHomMap (f.localized V) (F.over V) (G.over V)))
    (hsq : _root_.SheafOfModules.Hom.over (pullbackInternalHomMap f F G) (f.u.obj V) =
      (restrictionSourceIso f F G V).hom ≫
        pullbackInternalHomMap (f.localized V) (F.over V) (G.over V) ≫
          (restrictionTargetIso f F G V).inv) :
    IsIso (_root_.SheafOfModules.Hom.over (pullbackInternalHomMap f F G) (f.u.obj V)) :=
  hsq ▸ ((restrictionSourceIso f F G V) ≪≫ (@asIso _ _ _ _ _ h) ≪≫
    (restrictionTargetIso f F G V).symm).isIso_hom

end Restriction

end Stacks.SheafOfModules.InternalHom

end
