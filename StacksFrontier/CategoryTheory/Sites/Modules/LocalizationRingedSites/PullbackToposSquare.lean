module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Pullback
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare

/-!
# The localization square for the site-presented pullback of sheaves of modules

Let `f : X ⟶ Y` be a morphism of ringed sites, let `W` be an object of the target site and put
`U = u(W)`. Stacks 04J0 part (2) supplies a 2-isomorphism of *morphisms of ringed topoi* between
the two composites of the localization square

```
  (Sh(C/U), O_U)   --j_U-->  (Sh(C), O)
       | f'                     | f
  (Sh(D/W), O'_W)  --j_W-->  (Sh(D), O')
```

and Stacks 04IX identifies the pullback of sheaves of modules along a localization morphism with
restriction to the slice site. This file turns the two into a commuting square of pullbacks of
sheaves of modules, written with the *site-presented* pullback
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` that the derived pullback of Stacks 06YY is
built over:

```
  f^* ⋙ (- |_U)  ≅  (- |_W) ⋙ (f')^*
```

## The assembly

`AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso` carries the 2-isomorphism of
Stacks 04J0 part (2) to an isomorphism of the pullbacks of its two composites, and
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso` splits each composite into the two
pullbacks it is made of. The four resulting factors are then rewritten one at a time: the two
localization factors by Stacks 04IX and the two factors of `f` and `f'` by
`AlgebraicGeometry.RingedSite.Hom.pullbackModulesToposIso`.

Both rewritings cross the boundary between the two formalizations of a morphism of ringed topoi
— the two-field one of Stacks 01D3 part (2), which is the one that composes and therefore the
one the 2-isomorphism is about, and the four-field one of the modules development, which is the
one the pullback of sheaves of modules and Stacks 04IX are stated over. Two bridges are
provided for that:

* `AlgebraicGeometry.RingedToposHom.pullbackModulesViaComparisonIso`, which transports along
  `AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom`, the equality of the
  two four-field readings of a two-field morphism of ringed topoi; and
* `AlgebraicGeometry.RingedSite.toRingedToposModulesHom_localizationRingedToposHom`, which says
  that for the localization morphism the two presentations are *equal*, both forms of the
  structure map being the identity on underlying sheaves of sets.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.pullbackModulesViaComparisonIso`: the pullback of sheaves of
  modules of the two-field morphism of ringed topoi is the pullback of the four-field one it
  determines.
* `AlgebraicGeometry.RingedSite.localizationPullbackToposIsoRestriction`: Stacks 04IX for the
  two-field localization morphism of ringed topoi.
* `AlgebraicGeometry.RingedSite.Hom.pullbackToposIso`: the pullback of sheaves of modules along
  the two-field morphism of ringed topoi of a morphism of ringed sites is the site-presented
  pullback.
* `AlgebraicGeometry.RingedSite.Hom.localizedPullbackModulesSquare`: the localization square for
  the pullback of sheaves of modules of the modules development.
* `AlgebraicGeometry.RingedSite.Hom.localizedPullbackToposSquare`: the same square for the
  site-presented pullback.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The two formalizations of Stacks 03D6 part (2) agree.** The pullback of sheaves of modules
built for the two-field morphism of ringed topoi of Stacks 01D3 part (2) is the pullback built
for the four-field morphism of the modules development that it determines.

It is the passage by which the composition and 2-isomorphism calculus of the two-field morphism —
which is the structure that *composes* — becomes available to the statements of the modules
development.

This is the `CategoryTheory.eqToIso` of
`AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom`: the two four-field
morphisms of ringed topoi are not merely both left adjoint to isomorphic direct images, they are
*equal*, so the comparison of their pullbacks is a transport along an equality and is computable
on sections. It was formerly the `CategoryTheory.Adjunction.leftAdjointUniq` of
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` and
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModulesViaComparison`, which has no
description on sections at all.

The hypotheses are written out rather than taken from the section's `variable` block because the
two `AddCommGrpCat` sheaf-composition hypotheses on the source site are no longer used by the
construction, and dropping them would change this declaration's interface and that of every
consumer stated in the section. -/
def pullbackModulesViaComparisonIso {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (f : RingedToposHom X Y) :
    f.toModulesHom.pullbackModules ≅
      f.toRingedToposModulesHom.pullbackModules :=
  eqToIso (congrArg (fun h ↦ h.pullbackModules) f.toModulesHom_eq_toRingedToposModulesHom)

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.RingedSite

universe u

/-! ## The localization morphism in its two presentations -/

section Localization

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- The inverse-image form of the structure map of the localization morphism of ringed topoi,
read at the level of sheaves of rings, is the identification of the inverse image of the
structure sheaf with its restriction to the slice site. Both are the identity on underlying
sheaves of sets, and a morphism of sheaves of rings is determined by its underlying morphism of
sheaves of sets. -/
theorem localizationRingedToposHom_ringFsharpInverseImage :
    (X.localizationRingedToposHom U).ringFsharpInverseImage = X.overInverseImageFsharp U :=
  (sheafCompose (X.J.over U) (forget RingCat.{u})).map_injective
    ((X.forgetRing_localizationRingedToposHom_fSharpInverseImage U).trans
      (X.overInverseImageFsharp_ringSheafMap U).symm)

/-- The direct-image form of the structure map of the localization morphism of ringed topoi,
read at the level of sheaves of rings, is the direct-image form of the localization structure
map of the modules development: both are the adjunct of the same inverse-image form. -/
theorem localizationRingedToposHom_ringFsharp :
    (X.localizationRingedToposHom U).ringFsharp = X.overFsharpAdjoint U :=
  congrArg ((ringImageAdjunction (X.overMorphismOfTopoi U)).homEquiv _ _)
    (X.localizationRingedToposHom_ringFsharpInverseImage U)

/-- **The two presentations of the localization morphism of ringed topoi are equal.** The
four-field morphism of the modules development determined by the two-field localization morphism
of Stacks 04IX *is* the localization morphism of the modules development: the underlying
morphism of topoi is the same on the nose, and the two forms of the structure map agree by
`localizationRingedToposHom_ringFsharp` and
`localizationRingedToposHom_ringFsharpInverseImage`. -/
theorem toRingedToposModulesHom_localizationRingedToposHom :
    (X.localizationRingedToposHom U).toRingedToposModulesHom = X.localizationMorphism U := by
  have hi := X.localizationRingedToposHom_ringFsharpInverseImage U
  have hs := X.localizationRingedToposHom_ringFsharp U
  unfold AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom localizationMorphism
  congr 1

variable [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 04IX for the two-field localization morphism of ringed topoi.** Pullback of sheaves
of modules along the localization morphism at `U`, taken through the morphism of ringed topoi of
Stacks 01D3 part (2), is restriction to the localized site.

This is `AlgebraicGeometry.RingedSite.localizationPullbackIsoRestriction` carried across
`AlgebraicGeometry.RingedToposHom.pullbackModulesViaComparisonIso` and the equality of the two
presentations of the localization morphism. -/
def localizationPullbackToposIsoRestriction :
    (X.localizationRingedToposHom U).toModulesHom.pullbackModules ≅
      SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U :=
  RingedToposHom.pullbackModulesViaComparisonIso (X := ringedTopos (X.over U))
      (Y := ringedTopos X) (X.localizationRingedToposHom U) ≪≫
    eqToIso (congrArg (fun h ↦ h.pullbackModules)
      (X.toRingedToposModulesHom_localizationRingedToposHom U)) ≪≫
    X.localizationPullbackIsoRestriction U

end Localization

/-! ## The localization square -/

section Square

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The pullback of sheaves of modules along the two-field morphism of ringed topoi of a
morphism of ringed sites is the site-presented pullback of
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`.

This composes `AlgebraicGeometry.RingedToposHom.pullbackModulesViaComparisonIso` with
`AlgebraicGeometry.RingedSite.Hom.pullbackModulesToposIso`, and is the form in which the
site-presented pullback — the one the derived pullback of Stacks 06YY is built over — receives
statements proved about composites of two-field morphisms of ringed topoi. -/
def Hom.pullbackToposIso :
    f.ringedToposHom.toModulesHom.pullbackModules ≅
      f.toRingedToposSiteHom.pullbackTopos :=
  RingedToposHom.pullbackModulesViaComparisonIso (X := ringedTopos X) (Y := ringedTopos Y)
      f.ringedToposHom ≪≫
    f.pullbackModulesToposIso

variable (W : Y.C)
  [HasWeakSheafify (X.J.over (f.u.obj W)) AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj W)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Y.J.over W) AddCommGrpCat.{u}]
  [(Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The localization square of Stacks 04J0 for the pullback of sheaves of modules.** Pulling a
sheaf of `O'`-modules back along `f` and then along the localization at `U = u(W)` is the same as
pulling it back along the localization at `W` and then along the localized morphism `f'`.

Both composites are the pullback along a composite of morphisms of ringed topoi, and those two
composites are 2-isomorphic by Stacks 04J0 part (2); the square is the invariance of the pullback
under a 2-isomorphism, `AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso`, with each
composite split by `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso`. -/
def Hom.localizedPullbackModulesSquare :
    f.ringedToposHom.toModulesHom.pullbackModules ⋙
        (X.localizationRingedToposHom (f.u.obj W)).toModulesHom.pullbackModules ≅
      (Y.localizationRingedToposHom W).toModulesHom.pullbackModules ⋙
        (f.localizedRingedToposHom W).toModulesHom.pullbackModules :=
  (RingedToposHom.pullbackModulesCompIso (X := ringedTopos (X.over (f.u.obj W)))
        (Y := ringedTopos X) (Z := ringedTopos Y)
        (X.localizationRingedToposHom (f.u.obj W)) f.ringedToposHom).symm ≪≫
    (f.localizedRingedSquare W).pullbackModulesIso.symm ≪≫
      RingedToposHom.pullbackModulesCompIso (X := ringedTopos (X.over (f.u.obj W)))
        (Y := ringedTopos (Y.over W)) (Z := ringedTopos Y)
        (f.localizedRingedToposHom W) (Y.localizationRingedToposHom W)

/-- **The localization square of Stacks 04J0 for the site-presented pullback of sheaves of
modules.** Pulling a sheaf of `O'`-modules back along `f` and then restricting to the slice over
`U = u(W)` is the same as restricting to the slice over `W` and then pulling back along the
localized morphism `f'`.

This is `AlgebraicGeometry.RingedSite.Hom.localizedPullbackModulesSquare` with its four factors
rewritten: the two localization pullbacks by Stacks 04IX
(`localizationPullbackToposIsoRestriction`) and the two pullbacks along `f` and `f'` by
`AlgebraicGeometry.RingedSite.Hom.pullbackToposIso`. It is the underived square over which the
derived localization square of the derived pullback is formed. -/
def Hom.localizedPullbackToposSquare :
    f.toRingedToposSiteHom.pullbackTopos ⋙
        SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj W) ≅
      SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W ⋙
        (f.localized W).toRingedToposSiteHom.pullbackTopos :=
  (Functor.isoWhiskerRight f.pullbackToposIso.symm
        (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj W))).trans
    ((Functor.isoWhiskerLeft
          (f.ringedToposHom.toModulesHom.pullbackModules)
          (X.localizationPullbackToposIsoRestriction (f.u.obj W)).symm).trans
      ((f.localizedPullbackModulesSquare W).trans
        ((Functor.isoWhiskerRight (Y.localizationPullbackToposIsoRestriction W)
              (f.localizedRingedToposHom W).toModulesHom.pullbackModules).trans
          (Functor.isoWhiskerLeft
            (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W)
            (f.localized W).pullbackToposIso))))

end Square

end AlgebraicGeometry.RingedSite

end
