module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleLocalizationCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyOverAnObjectAfterARaise
public import StacksFrontier.CategoryTheory.Sites.Pretopology.AsSmallSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheaf
public import StacksFrontier.Cotangent.CohomologyPresheaf.SiteSectionsComparison
public import StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology over an object of the small étale site is the étale cohomology of its scheme

Let `B` be a big étale site containing a scheme `X` and let `V` be an object of the small étale
site of `X`. Four spellings of "the cohomology of an abelian sheaf over `V`" occur in this
library — Mathlib's `CategoryTheory.Sheaf.H'` over the object, the global cohomology of the slice
site at the object, the étale cohomology of the *scheme* of `V`, and the right derived functors of
`CategoryTheory.sheafSections` over the object — and this file joins them.

Mathlib's `CategoryTheory.Sheaf.H'`, the cohomology of a sheaf over an *object* of a site, exists
only when the coefficient universe is the *morphism* universe of the site. The objects of
`AlgebraicGeometry.SmallEtale B X hX` live in `Type (u + 1)` and its morphisms in `Type u`, while
the library's `Stacks.EtaleCohomology.etaleCohomologyFunctor` has coefficients
`AddCommGrpCat.{u + 1}`; so `Sheaf.H'` is simply unavailable at that spelling, and the standard
repair — the one `StacksFrontier/AlgebraicGeometry/EtaleCohomology/MayerVietoris.lean` and the
cohomology of Stacks 09YP already use — is to raise the morphism universe with
`CategoryTheory.AsSmall`. This file carries the comparison through the raise and composes it with
the geometric half already in the library:

`H^n(AsSmall.up V, F) ≅ H^n(X_étale/V, F|_V) ≅ H^n_étale(V, F|_{V_étale})`,

the first isomorphism being
`Stacks.Cohomology.OverObjectCohomology.h'IsoSliceH` at the raise and the second
`Stacks.EtaleCohomology.SmallEtaleLocalization.localizationCohomologyFunctorIso`.

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleRaised.raisedTopology` — the small étale topology of `X` with
  its morphism universe raised to the universe of its objects.
* `Stacks.EtaleCohomology.SmallEtaleRaised.raisedSliceRestrict` — restriction of an abelian sheaf
  on the slice of the raised site at `AsSmall.up V` to the slice of the small étale site at `V`.
* `Stacks.EtaleCohomology.SmallEtaleRaised.raisedSliceCohomologyFunctor` — the cohomology of the
  slice of the raised site at `AsSmall.up V`, the `Ext`-groups out of its constant sheaf on `ℤ`.
* `Stacks.EtaleCohomology.SmallEtaleRaised.raisedObjectToSmallEtale` — the abelian sheaf on the
  small étale site of the *scheme* of `V` that an abelian sheaf on the slice of the raised site
  at `AsSmall.up V` comes from.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleRaised.raisedSliceCohomologyFunctorIso` — **the raise**: the
  global cohomology of the slice of the raised site at `AsSmall.up V` is the global cohomology of
  the slice of the small étale site at `V`, in every degree and naturally in the sheaf.
* `Stacks.EtaleCohomology.SmallEtaleRaised.h'IsoSliceCohomology` — cohomology over the object
  `AsSmall.up V` of the raised site is the global cohomology of the slice of the small étale site
  of `X` at `V`.
* `Stacks.EtaleCohomology.SmallEtaleRaised.raisedSliceCohomologyFunctorIsoEtaleCohomology` and
  `Stacks.EtaleCohomology.SmallEtaleRaised.h'IsoEtaleCohomology` — **the composite**: cohomology
  over the object `AsSmall.up V` is the library's étale cohomology of the scheme of `V`.
* `Stacks.EtaleCohomology.SmallEtaleRaised.rightDerivedSheafSectionsIsoEtaleCohomology` — the same
  group as the `p`-th right derived functor of `sheafSections` over `AsSmall.up V`, which is the
  fourth spelling: the cohomology that Stacks 09YP and the Čech comparison produce.
* `Stacks.EtaleCohomology.SmallEtaleRaised.rightDerivedSheafToPresheafObjIso` — Stacks 03AY on the
  raised site: the right derived functors of the inclusion of abelian sheaves into abelian
  presheaves are the cohomology presheaves.

## Implementation notes

The raise is `CategoryTheory.AsSmall.up`, which is an equivalence of categories and the inclusion
of a dense subsite (`CategoryTheory.AsSmall.isDenseSubsite_up`), so the general transport
`Stacks.Cohomology.OverObjectCohomology.h'IsoSliceH` applies with no further hypothesis. Its
inputs are discharged here: the four facts abelian sheaf cohomology needs on the raised site and
on its slice, the exactness of restriction to a slice, and — the one genuinely analytic input —
that restriction to a slice preserves injective objects, which is
`overPullback_preservesInjective` of
`StacksFrontier/Homology/Injectives/Sheaf/InternalHomExact.lean`, available because the universe
condition `UnivLE.{max u v, w}` of that file is satisfied on the raised site, where objects,
morphisms and coefficients all live in `Type (u + 1)`.

The extension by zero is Mathlib's `CategoryTheory.Functor.sheafPullback` along
`Over.forget (AsSmall.up V)`, whose left Kan extension exists because the raised site is small in
the coefficient universe.

`V` is an arbitrary object of the small étale site of `X`, `X` an arbitrary scheme of `B`, the
sheaf arbitrary and the degree arbitrary: no affineness, no open immersion and no bound on the
degree is assumed.

No tag attribute is placed. What is compared here are four of this library's and Mathlib's own
definitions of one group; the closest statement of the source, Stacks 03F3(2), is the same
comparison for modules over a ringed site rather than for abelian sheaves, and it is already
discussed by
`StacksFrontier/CategoryTheory/Sites/GlobalSections/CohomologyOverAnObject.lean`. In particular
nothing of Stacks 03Q6 is registered here: this file supplies the identification of the cohomology
that Stacks 09YP computes with the étale cohomology functor over an *arbitrary* object of the
site, which is one of that tag's open obligations, but the tag's remaining gaps — quasi-compact
quasi-separated rather than affine `X`, and the system of sheaves being a system of inverse
images — are untouched.

## References

* [Stacks 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks 03AY](https://stacks.math.columbia.edu/tag/03AY)
* [Stacks 04HR](https://stacks.math.columbia.edu/tag/04HR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe u

namespace Stacks.EtaleCohomology.SmallEtaleRaised

open AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.EtaleCohomology.SmallEtaleLocalization

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-! ### The raised small étale site -/

/-- **The small étale site of `X` with its morphism universe raised** to the universe of its
objects, carrying the étale precoverage transported along `CategoryTheory.AsSmall.down`. This is
the site on which `CategoryTheory.Sheaf.H'` with coefficients `AddCommGrpCat.{u + 1}` exists. -/
abbrev raisedTopology :
    GrothendieckTopology (AsSmall.{u + 1} (AlgebraicGeometry.SmallEtale B X hX)) :=
  ((SmallEtale.precoverage B X hX).comap AsSmall.down).toGrothendieck

attribute [local instance] CategoryTheory.AsSmall.isDenseSubsite_up

/-- Raising the morphism universe of the small étale site is an equivalence of categories. -/
theorem isEquivalence_asSmallUp :
    (AsSmall.up : AlgebraicGeometry.SmallEtale B X hX ⥤
      AsSmall.{u + 1} (AlgebraicGeometry.SmallEtale B X hX)).IsEquivalence :=
  (AsSmall.equiv : AlgebraicGeometry.SmallEtale B X hX ≌
    AsSmall.{u + 1} (AlgebraicGeometry.SmallEtale B X hX)).isEquivalence_functor

attribute [local instance] isEquivalence_asSmallUp

/-- Abelian sheaves on the raised small étale site admit sheafification. -/
theorem hasSheafify_raised : HasSheafify (raisedTopology B X hX) AddCommGrpCat.{u + 1} :=
  CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u + 1, u + 1} _

attribute [local instance] hasSheafify_raised

/-- Abelian sheaves on the raised small étale site are locally `(u + 1)`-small. -/
theorem locallySmall_raised :
    LocallySmall.{u + 1} (Sheaf (raisedTopology B X hX) AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Sheaf.locallySmall_of_small.{u + 1, u + 1, u + 1, u + 1, u + 2}
    (raisedTopology B X hX) AddCommGrpCat.{u + 1}

attribute [local instance] locallySmall_raised

/-- Abelian sheaves on the raised small étale site have enough injectives. -/
theorem enoughInjectives_raised :
    EnoughInjectives (Sheaf (raisedTopology B X hX) AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u + 1, u + 1, u + 2}
    (raisedTopology B X hX) AddCommGrpCat.{u + 1}

attribute [local instance] enoughInjectives_raised

/-- `Ext`-groups of abelian sheaves on the raised small étale site exist. -/
theorem hasExt_raised :
    HasExt.{u + 1} (Sheaf (raisedTopology B X hX) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

attribute [local instance] hasExt_raised

/-- Abelian sheaves on a slice of the raised small étale site admit sheafification. -/
theorem hasSheafify_raisedSlice
    (W : AsSmall.{u + 1} (AlgebraicGeometry.SmallEtale B X hX)) :
    HasSheafify ((raisedTopology B X hX).over W) AddCommGrpCat.{u + 1} :=
  CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u + 1, u + 1} _

attribute [local instance] hasSheafify_raisedSlice

/-- Abelian sheaves on a slice of the raised small étale site are locally `(u + 1)`-small. -/
theorem locallySmall_raisedSlice
    (W : AsSmall.{u + 1} (AlgebraicGeometry.SmallEtale B X hX)) :
    LocallySmall.{u + 1} (Sheaf ((raisedTopology B X hX).over W) AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Sheaf.locallySmall_of_small.{u + 1, u + 1, u + 1, u + 1, u + 2}
    ((raisedTopology B X hX).over W) AddCommGrpCat.{u + 1}

attribute [local instance] locallySmall_raisedSlice

/-- Abelian sheaves on a slice of the raised small étale site have enough injectives. -/
theorem enoughInjectives_raisedSlice
    (W : AsSmall.{u + 1} (AlgebraicGeometry.SmallEtale B X hX)) :
    EnoughInjectives (Sheaf ((raisedTopology B X hX).over W) AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u + 1, u + 1, u + 2}
    ((raisedTopology B X hX).over W) AddCommGrpCat.{u + 1}

attribute [local instance] enoughInjectives_raisedSlice

/-- `Ext`-groups of abelian sheaves on a slice of the raised small étale site exist. -/
theorem hasExt_raisedSlice (W : AsSmall.{u + 1} (AlgebraicGeometry.SmallEtale B X hX)) :
    HasExt.{u + 1} (Sheaf ((raisedTopology B X hX).over W) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

attribute [local instance] hasExt_raisedSlice

/-- **Restriction to a slice of the raised small étale site preserves injective objects.** This
is the one analytic input of the comparison with cohomology over an object: the extension by zero
`j_!` along the localization of a site is exact, so its right adjoint — restriction to the slice
— preserves injectives. It is `overPullback_preservesInjective`, whose universe condition
`UnivLE.{max u v, w}` holds here because the objects, the morphisms and the coefficients of the
raised site all live in `Type (u + 1)`. -/
theorem preservesInjectiveObjects_raisedOverPullback
    (W : AsSmall.{u + 1} (AlgebraicGeometry.SmallEtale B X hX)) :
    ((raisedTopology B X hX).overPullback AddCommGrpCat.{u + 1} W).PreservesInjectiveObjects where
  injective_obj {F} hF := by
    let := hF
    exact overPullback_preservesInjective (raisedTopology B X hX) W F

attribute [local instance] preservesInjectiveObjects_raisedOverPullback

/-! ### Cohomology over an object of the raised site -/

variable (V : AlgebraicGeometry.SmallEtale B X hX)

/-- The object of the raised small étale site that `V` becomes. -/
abbrev raise : AsSmall.{u + 1} (AlgebraicGeometry.SmallEtale B X hX) := AsSmall.up.obj V

attribute [local instance] hasSheafify_slice locallySmall_slice enoughInjectives_slice hasExt_slice

/-- **Restriction of an abelian sheaf on the slice of the raised site at `AsSmall.up V` to the
slice of the small étale site of `X` at `V`.** It is an equivalence on abelian sheaves. -/
abbrev raisedSliceRestrict :
    Sheaf ((raisedTopology B X hX).over (raise B X hX V)) AddCommGrpCat.{u + 1} ⥤
      Sheaf (sliceTopology B X hX V) AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.OverObjectCohomology.sliceRestrict (SmallEtale.topology B X hX)
    (raisedTopology B X hX) AsSmall.up V

/-- **The `p`-th cohomology functor of the slice of the raised site at `AsSmall.up V`**: the
`Ext`-groups out of the constant sheaf on `ℤ`. Its coefficients and its morphisms share the
universe `u + 1`, so this is the cohomology that `CategoryTheory.Sheaf.H'` over `AsSmall.up V`
compares to. -/
abbrev raisedSliceCohomologyFunctor (p : ℕ) :
    Sheaf ((raisedTopology B X hX).over (raise B X hX V)) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1} :=
  Sheaf.functorH.{u + 1, u + 1, u + 1, u + 1} ((raisedTopology B X hX).over (raise B X hX V)) p

/-- **The raise costs nothing on a slice.** For every degree `p`,

`H^p(X_étale/V, F|_{X_étale/V}) ≅ H^p((AsSmall X_étale)/AsSmall.up V, F)`

naturally in the abelian sheaf `F` on the slice of the raised site at `AsSmall.up V`.

`CategoryTheory.AsSmall.up` is an equivalence of categories and a dense subsite inclusion, hence
so is its localization `CategoryTheory.Over.post AsSmall.up`, and restriction along an equivalence
of sites changes neither the constant sheaf on `ℤ` nor the injective objects, hence not the
`Ext`-groups out of the constant sheaf. -/
def raisedSliceCohomologyFunctorIso (p : ℕ) :
    raisedSliceRestrict B X hX V ⋙ sliceCohomologyFunctor B X hX V p ≅
      raisedSliceCohomologyFunctor B X hX V p :=
  Stacks.Cohomology.OverObjectCohomology.sliceCohomologyFunctorIsoOfEquivalence.{u, u + 1}
    (SmallEtale.topology B X hX) (raisedTopology B X hX) AsSmall.up V p

/-- The extension by zero along the localization of the raised site at `AsSmall.up V`, as an
adjunction: Mathlib's `CategoryTheory.Functor.sheafPullback` along `Over.forget (AsSmall.up V)`,
left adjoint to restriction to the slice. -/
abbrev raisedExtensionByZeroAdj :
    (Over.forget (raise B X hX V)).sheafPullback AddCommGrpCat.{u + 1}
        ((raisedTopology B X hX).over (raise B X hX V)) (raisedTopology B X hX) ⊣
      (raisedTopology B X hX).overPullback AddCommGrpCat.{u + 1} (raise B X hX V) :=
  Functor.sheafAdjunctionContinuous (Over.forget (raise B X hX V)) AddCommGrpCat.{u + 1}
    ((raisedTopology B X hX).over (raise B X hX V)) (raisedTopology B X hX)

/-- **Cohomology over an object of the raised small étale site is global cohomology on the slice
of the small étale site.** For an abelian sheaf `F` on the raised small étale site of `X`, a
degree `p` and an object `V` of the small étale site,

`H^p(AsSmall.up V, F) ≅ H^p(X_étale/V, F|_{X_étale/V})`,

the left hand side being Mathlib's `CategoryTheory.Sheaf.H'`, which exists on the raised site
because its morphisms and the coefficients share the universe `u + 1`, and the right hand side
the global cohomology of the slice of the *unraised* small étale site at `V`.

This is the transport the raise needs: it is
`Stacks.Cohomology.OverObjectCohomology.h'IsoSliceH` at `CategoryTheory.AsSmall.up`. -/
def h'IsoSliceCohomology
    (F : Sheaf (raisedTopology B X hX) AddCommGrpCat.{u + 1}) (p : ℕ) :
    Sheaf.H' F p (raise B X hX V) ≅
      (sliceCohomologyFunctor B X hX V p).obj
        ((raisedSliceRestrict B X hX V).obj (F.over (raise B X hX V))) :=
  Stacks.Cohomology.OverObjectCohomology.h'IsoSliceH.{u, u + 1} (SmallEtale.topology B X hX)
    (raisedTopology B X hX) AsSmall.up V (raisedExtensionByZeroAdj B X hX V) F p

/-! ### The composite: étale cohomology of the scheme of `V` -/

attribute [local instance] hasSheafify_obj locallySmall_obj enoughInjectives_obj hasExt_obj

/-- **The abelian sheaf on the small étale site of the scheme of `V` that an abelian sheaf on the
slice of the raised site at `AsSmall.up V` comes from.** Restrict across the raise, then across
the localization equivalence of Stacks 04HR. -/
abbrev raisedObjectToSmallEtale :
    Sheaf ((raisedTopology B X hX).over (raise B X hX V)) AddCommGrpCat.{u + 1} ⥤
      Sheaf (objTopology B X hX V) AddCommGrpCat.{u + 1} :=
  raisedSliceRestrict B X hX V ⋙ restrictToObject B X hX V

/-- **The cohomology of the slice of the raised site at `AsSmall.up V` is the étale cohomology of
the scheme of `V`.** For every degree `p`,

`H^p((AsSmall X_étale)/AsSmall.up V, F) ≅ H^p_étale(V, F')`

naturally in the abelian sheaf `F` on that slice, where `F'` is the abelian sheaf on the small
étale site of the scheme of `V` that `F` comes from (`raisedObjectToSmallEtale`) and the right
hand side is the library's `Stacks.EtaleCohomology.etaleCohomologyFunctor`.

This is `raisedSliceCohomologyFunctorIso` composed with
`Stacks.EtaleCohomology.SmallEtaleLocalization.localizationCohomologyFunctorIso`, the geometric
half: the small étale site of the scheme of `V` is the localization of the small étale site of `X`
at `V`. -/
def raisedSliceCohomologyFunctorIsoEtaleCohomology (p : ℕ) :
    raisedSliceCohomologyFunctor B X hX V p ≅
      raisedObjectToSmallEtale B X hX V ⋙
        Stacks.EtaleCohomology.etaleCohomologyFunctor B
          ⟨V.obj.left.obj, V.obj.left.property⟩ p :=
  (raisedSliceCohomologyFunctorIso B X hX V p).symm ≪≫
    Functor.isoWhiskerLeft _ (localizationCohomologyFunctorIso B X hX V p).symm ≪≫
    (Functor.associator _ _ _).symm

/-- **Cohomology over an object of the small étale site is the étale cohomology of its scheme.**
For an abelian sheaf `F` on the raised small étale site of `X`, an object `V` of the small étale
site of `X` and a degree `p`,

`H^p(AsSmall.up V, F) ≅ H^p_étale(V, F|_{V_étale})`,

the left hand side being Mathlib's `CategoryTheory.Sheaf.H'` — the `Ext`-group from the free
abelian sheaf generated by the object `AsSmall.up V` — and the right hand side the library's
`Stacks.EtaleCohomology.etaleCohomologyFunctor` of the *scheme* underlying `V`, applied to the
abelian sheaf on the small étale site of that scheme which `F` restricts to.

This is the statement the comparison was missing: it composes the universe raise
(`h'IsoSliceCohomology`) with the geometric half
(`Stacks.EtaleCohomology.SmallEtaleLocalization.localizationCohomologyFunctorIso`). `V` is
arbitrary — no affineness and no open immersion — and so are `X`, `F` and `p`. -/
@[sga "4 V 2.2" "H^q(X, special case"]
def h'IsoEtaleCohomology
    (F : Sheaf (raisedTopology B X hX) AddCommGrpCat.{u + 1}) (p : ℕ) :
    Sheaf.H' F p (raise B X hX V) ≅
      (Stacks.EtaleCohomology.etaleCohomologyFunctor B
          ⟨V.obj.left.obj, V.obj.left.property⟩ p).obj
        ((raisedObjectToSmallEtale B X hX V).obj (F.over (raise B X hX V))) :=
  h'IsoSliceCohomology B X hX V F p ≪≫
    ((localizationCohomologyFunctorIso B X hX V p).app
      ((raisedSliceRestrict B X hX V).obj (F.over (raise B X hX V)))).symm

/-! ### The right-derived sections spelling -/

/-- Abelian sheaves on the raised small étale site have injective resolutions. -/
theorem hasInjectiveResolutions_raised :
    HasInjectiveResolutions (Sheaf (raisedTopology B X hX) AddCommGrpCat.{u + 1}) :=
  inferInstance

attribute [local instance] hasInjectiveResolutions_raised

/-- **Stacks 03AY on the raised small étale site.** The `p`-th right derived functor of the
inclusion of abelian sheaves into abelian presheaves, evaluated at an abelian sheaf `G` on the
raised small étale site of `X`, is the `p`-th cohomology presheaf of `G`.

This records that `Stacks.Cohomology.rightDerivedObjIsoCohomologyPresheaf` *does* apply after the
raise: it is stated for a `CategoryTheory.SmallCategory` with coefficients in the one universe of
its objects and morphisms, which the raised site is and the small étale site itself — objects in
`Type (u + 1)`, morphisms in `Type u` — is not. -/
@[sga "4 IV 4.8" "special case", sga "4 V 2.4.2" "ℋ^q(M) = (X ↦ H^q(X"]
def rightDerivedSheafToPresheafObjIso
    (G : Sheaf (raisedTopology B X hX) AddCommGrpCat.{u + 1}) (p : ℕ) :
    ((sheafToPresheaf (raisedTopology B X hX) AddCommGrpCat.{u + 1}).rightDerived p).obj G ≅
      G.cohomologyPresheaf p :=
  Stacks.Cohomology.rightDerivedObjIsoCohomologyPresheaf (raisedTopology B X hX) G p

/-- **The right derived functors of sections over an object of the raised small étale site are
the étale cohomology of the scheme of that object.** For an abelian sheaf `F` on the raised small
étale site of `X`, an object `V` of the small étale site and a degree `p`,

`R^p Γ(AsSmall.up V, F) ≅ H^p_étale(V, F|_{V_étale})`.

The left hand side is the fourth spelling of cohomology over an object that occurs in this
library: the right derived functors of `CategoryTheory.sheafSections` over the object, which is
the cohomology Stacks 09YP and the Čech-to-cohomology comparison produce. It is identified with
Mathlib's `CategoryTheory.Sheaf.H'` by
`Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections` — which applies because the
raised site is a small category with its coefficients in the universe of its morphisms — and
from there `h'IsoEtaleCohomology` carries it to the étale cohomology of the scheme of `V`. -/
def rightDerivedSheafSectionsIsoEtaleCohomology
    (F : Sheaf (raisedTopology B X hX) AddCommGrpCat.{u + 1}) (p : ℕ) :
    (((sheafSections (raisedTopology B X hX) AddCommGrpCat.{u + 1}).obj
          (op (raise B X hX V))).rightDerived p).obj F ≅
      (Stacks.EtaleCohomology.etaleCohomologyFunctor B
          ⟨V.obj.left.obj, V.obj.left.property⟩ p).obj
        ((raisedObjectToSmallEtale B X hX V).obj (F.over (raise B X hX V))) :=
  (Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections
      (raisedTopology B X hX) F p (raise B X hX V)).symm ≪≫
    h'IsoEtaleCohomology B X hX V F p

end Stacks.EtaleCohomology.SmallEtaleRaised

end
