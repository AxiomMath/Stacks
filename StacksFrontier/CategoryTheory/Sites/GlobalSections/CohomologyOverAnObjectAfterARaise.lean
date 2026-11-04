module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SiteEquivalenceGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyOverAnObject
public import StacksFrontier.CategoryTheory.Sites.Localization.SliceDenseSubsite

/-!
# Cohomology over an object of a site whose morphisms have been raised

`Stacks.Cohomology.OverObjectCohomology.h'IsoHOver` identifies `CategoryTheory.Sheaf.H'` — the
cohomology of an abelian sheaf over an *object* of a site — with the global cohomology of the
restriction of that sheaf to the slice site. Mathlib's `CategoryTheory.Sheaf.H'` exists only when
the coefficient universe is the *morphism* universe of the site, so for a site whose objects live
above its morphisms — the small étale site of a scheme is the example — it is unavailable at the
coefficient universe in which the sheaves of interest live, and the standard repair is to raise
the morphism universe with `CategoryTheory.AsSmall`.

This file carries the comparison across such a raise. Let `G : C ⥤ D` be an equivalence of
categories which is at the same time the inclusion of a dense subsite, `J` on `C` and `K` on `D`,
with the morphisms of `D` in the coefficient universe. Then for `U : C` the cohomology of an
abelian sheaf on `(D, K)` over the object `G U` is the global cohomology, on the slice
`(Over U, J.over U)` of the *unraised* site, of its restriction there. No cohomology of `(C, J)`
at the coefficient universe is formed, so no `Ext`-group that does not exist is mentioned.

## Main definitions

* `Stacks.Cohomology.OverObjectCohomology.sliceRestrict` — restriction of an abelian sheaf on the
  slice of `(D, K)` at `G U` to the slice of `(C, J)` at `U`, along `CategoryTheory.Over.post G`.

## Main results

* `Stacks.Cohomology.OverObjectCohomology.sliceCohomologyFunctorIsoOfEquivalence` — the global
  cohomology of the slice of `(D, K)` at `G U` is the global cohomology of the slice of `(C, J)`
  at `U`, in every degree and naturally in the abelian sheaf.
* `Stacks.Cohomology.OverObjectCohomology.h'IsoSliceH` — **cohomology over the object `G U` is
  global cohomology on the slice of the unraised site at `U`.** This is the transport the raise
  needs: it composes `h'IsoHOver` with the previous isomorphism.

## Implementation notes

`CategoryTheory.Over.post G` is a dense subsite inclusion of the two slices
(`CategoryTheory.Functor.isDenseSubsite_overPost`), hence continuous, cocontinuous and an
equivalence on abelian sheaves, so
`Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence` applies to it. That
lemma allows the two sites to have independent morphism universes but demands that their objects
share one. That is the only reason the raised site is declared as `D : Type (max u v)` with
`Category.{max u v} D`, which is the shape `CategoryTheory.AsSmall` produces: both slices then
have objects in `Type (max u v)`, their morphisms being in `Type v` and `Type (max u v)`.

The extension by zero on `(D, K)` enters as an explicit adjunction, exactly as in
`h'IsoHOver`; `CategoryTheory.Functor.sheafAdjunctionContinuous` provides one whenever the left
Kan extension along `(Over.forget (G U)).op` exists.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.OverObjectCohomology

universe v u

variable {C : Type u} [Category.{v} C] {D : Type (max u v)} [Category.{max u v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsEquivalence] [G.IsDenseSubsite J K] (U : C)

attribute [local instance] CategoryTheory.Functor.isDenseSubsite_overPost

section Slice

variable [∀ Y : (Over (G.obj U))ᵒᵖ,
    HasLimitsOfShape (StructuredArrow Y (Over.post (X := U) G).op) AddCommGrpCat.{max u v}]

/-- **Restriction of an abelian sheaf on the slice of `(D, K)` at `G U` to the slice of `(C, J)`
at `U`**, along `CategoryTheory.Over.post G`. -/
abbrev sliceRestrict :
    Sheaf (K.over (G.obj U)) AddCommGrpCat.{max u v} ⥤ Sheaf (J.over U) AddCommGrpCat.{max u v} :=
  (Over.post (X := U) G).sheafPushforwardContinuous AddCommGrpCat.{max u v}
    (J.over U) (K.over (G.obj U))

variable [HasSheafify (J.over U) AddCommGrpCat.{max u v}]
  [HasSheafify (K.over (G.obj U)) AddCommGrpCat.{max u v}]
  [HasExt.{max u v} (Sheaf (J.over U) AddCommGrpCat.{max u v})]
  [HasExt.{max u v} (Sheaf (K.over (G.obj U)) AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf (J.over U) AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf (K.over (G.obj U)) AddCommGrpCat.{max u v})]

/-- **Raising the morphism universe of a site does not change the cohomology of a slice.** For
every degree `p`,

`H^p(C/U, F|_{C/U}) ≅ H^p(D/G U, F)`

naturally in the abelian sheaf `F` on the slice of `(D, K)` at `G U`, where `H^p` is
`CategoryTheory.Sheaf.functorH`, the `Ext`-groups out of the constant sheaf on `ℤ`.

`CategoryTheory.Over.post G` is a dense subsite inclusion of the two slices, so restriction along
it is an equivalence of abelian sheaf categories, and an equivalence of sites changes neither the
constant sheaf on `ℤ` nor the injective objects, hence not the `Ext`-groups out of the constant
sheaf. -/
def sliceCohomologyFunctorIsoOfEquivalence (p : ℕ) :
    sliceRestrict J K G U ⋙
        Sheaf.functorH.{max u v, max u v, v, max u v} (J.over U) p ≅
      Sheaf.functorH.{max u v, max u v, max u v, max u v} (K.over (G.obj U)) p :=
  Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence.{max u v, v, max u v,
    max u v} (J.over U) (K.over (G.obj U)) (Over.post (X := U) G) p

end Slice

section Comparison

variable [HasSheafify K AddCommGrpCat.{max u v}]
  [HasSheafify (J.over U) AddCommGrpCat.{max u v}]
  [HasSheafify (K.over (G.obj U)) AddCommGrpCat.{max u v}]
  [HasExt.{max u v} (Sheaf K AddCommGrpCat.{max u v})]
  [HasExt.{max u v} (Sheaf (J.over U) AddCommGrpCat.{max u v})]
  [HasExt.{max u v} (Sheaf (K.over (G.obj U)) AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf (J.over U) AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf (K.over (G.obj U)) AddCommGrpCat.{max u v})]
  [∀ Y : (Over (G.obj U))ᵒᵖ,
    HasLimitsOfShape (StructuredArrow Y (Over.post (X := U) G).op) AddCommGrpCat.{max u v}]
  [PreservesFiniteLimits (K.overPullback AddCommGrpCat.{max u v} (G.obj U))]
  [PreservesFiniteColimits (K.overPullback AddCommGrpCat.{max u v} (G.obj U))]
  [(K.overPullback AddCommGrpCat.{max u v} (G.obj U)).PreservesInjectiveObjects]
  {L : Sheaf (K.over (G.obj U)) AddCommGrpCat.{max u v} ⥤ Sheaf K AddCommGrpCat.{max u v}}

/-- **Cohomology over an object of a site whose morphisms have been raised is global cohomology
on the slice of the unraised site.** For `G : C ⥤ D` an equivalence of categories exhibiting
`(C, J)` as a dense subsite of `(D, K)`, an object `U : C`, an abelian sheaf `F` on `(D, K)` with
coefficients in the morphism universe of `D`, and a degree `n`,

`H^n(G U, F) ≅ H^n(C/U, F|_{C/U})`.

The left hand side is Mathlib's `CategoryTheory.Sheaf.H'`, available on `(D, K)` because the
coefficients are the morphisms of `D`; the right hand side is the global cohomology of the slice
of `(C, J)` at `U`, which is where a site with objects above its morphisms — such as the small
étale site of a scheme — has its cohomology.

The two steps are `h'IsoHOver`, which turns cohomology over `G U` into global cohomology on the
slice of `(D, K)`, and `sliceCohomologyFunctorIsoOfEquivalence`, which carries that back across
the raise. -/
def h'IsoSliceH (adj : L ⊣ K.overPullback AddCommGrpCat.{max u v} (G.obj U))
    (F : Sheaf K AddCommGrpCat.{max u v}) (n : ℕ) :
    Sheaf.H' F n (G.obj U) ≅
      (Sheaf.functorH.{max u v, max u v, v, max u v} (J.over U) n).obj
        ((sliceRestrict J K G U).obj (F.over (G.obj U))) :=
  h'IsoHOver.{max u v, max u v, max u v} K (G.obj U) adj F n ≪≫
    ((sliceCohomologyFunctorIsoOfEquivalence J K G U n).app (F.over (G.obj U))).symm

end Comparison

end Stacks.Cohomology.OverObjectCohomology

end
