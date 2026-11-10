module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
import StacksCore.Tactic.StacksAttribute

/-!
# The derived adjunction and the ordinary counit, for a morphism of ringed topoi

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi.  Stacks 07A6 asserts that the
total left derived pullback `Lf^*` of Stacks 06YY is left adjoint to the total right derived
direct image `Rf_*` of Stacks 07A5, and Stacks 0FPI asserts that the counit of that adjunction
is the one induced by the ordinary counit `f^*f_* ⟶ id`: the square

```
Lf^* f_* 𝒦 ⟶ f^* f_* 𝒦
    ↓               ↓
Lf^* Rf_* 𝒦 ⟶       𝒦
```

commutes in `D(𝒪)`, its upper edge being the comparison `Lf^* ⟶ f^*`, its left edge `Lf^*`
applied to the comparison `f_* ⟶ Rf_*`, its lower edge the counit of the derived adjunction and
its right edge the ordinary counit.

Both are proved here for an `AlgebraicGeometry.RingedToposHom` — the two-field morphism of
ringed topoi of Stacks 01D3, part (2): a morphism of the underlying *topoi* together with the
structure map, with no functor between the underlying sites — and with no hypothesis beyond
those that make the two categories of modules exist.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackOfToposHom.kFlatLeftDerivedPullback`: the Stacks 06YY datum
  for an arbitrary morphism of ringed topoi, at the resolving class of K-flat complexes with
  flat terms.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction`: **Stacks 07A6**, the
  adjunction `Lf^* ⊣ Rf_*`, unconditionally.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction_counit_fac`: **Stacks 0FPI**,
  the commutativity of the square above.

## Implementation notes

*What this file does.*
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/PullbackAdjunction.lean` proves
Stacks 07A6 and the counit factorization *relative to* a
`Stacks.Cohomology.DerivedPushforward.LeftDerivedPullback f`, the bundle in which Stacks 06YY is
expected to supply `Lf^*`: a resolving class on `K(Mod(𝒪'))`, the existence of resolutions in it,
and the fact that degreewise pullback inverts quasi-isomorphisms between its objects.  It
declines the two attributes for that reason and records that they belong on the specialization
at the K-flat complexes.  This file is that specialization: the resolving half of the bundle is
Stacks 06YS, `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat`,
and the exactness half is Stacks 06YY's own exactness clause,
`Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat`, which holds along
*every* morphism of ringed topoi.  So nothing is deferred and the two statements below carry no
hypothesis on `f`.

*Why this is not a generalization of the ringed-site statements.*
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedAdjunction` (Stacks 07A6) and
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction_counit_fac` (Stacks 0FPI) are
stated for an `AlgebraicGeometry.RingedToposSiteHom` together with the hypothesis
`f.u.IsMorphismOfSites`, i.e. for a morphism of ringed topoi *presented by a continuous functor
between the underlying sites*.  A `RingedToposHom` has no such functor — the small étale ringed
topos of an algebraic space is the standing example, the base change of an étale scheme chart
along a non-representable morphism being an algebraic space and not a chart — so the two data
are different and neither statement has the other as an instance.  The degreewise functors
differ accordingly: the ringed-site chain runs on
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`, Mathlib's `SheafOfModules.pullback`, and
this one on `AlgebraicGeometry.RingedToposHom.pullbackModules`, the inverse image of Stacks 03D2
followed by extension of scalars, which is the formula of Stacks 03D6, part (2).  Identifying
the two along `AlgebraicGeometry.RingedToposSiteHom.toToposHom` would need a comparison
isomorphism of the two pullbacks and is not constructed here; see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackOfToposHom.lean`.

*Universes.*  Both ringed topoi are at `AlgebraicGeometry.RingedTopos.{u, u, u}`, although
`Lf^*` itself (`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback`), `Rf_*`
(`Stacks.Cohomology.DerivedPushforward.derivedPushforward`) and the conditional statements of
`PullbackAdjunction` all exist with the six universes of the two ringed topoi free.  The
narrowing is the *exactness* half of the datum's, and it is **not** the resolving half's.
The resolving half is free: Stacks 06YS is
`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize`, which resolves by flat
modules at three independent universes rather than by a direct sum of extensions by zero indexed
by sections over objects, and the class it resolves,
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat`, is stated at
independent universes too, so both reach the small étale ringed topos of an algebraic space,
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`, whose objects live in `Type (u + 1)` while its
sections live in `Type u`.  Assembling `kFlatLeftDerivedPullback` through
`LeftDerivedPullback.ofResolving` with the two ringed topoi free leaves exactly one unsatisfied
argument, and it is the exactness half:
`Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat`, itself declared at
one universe.  Widening *that* is therefore the one input a consumer at those universes still
needs from this file; its own three independent forcings — Stacks 0G6R and through it
Stacks 05VD, Stacks 0G7C, and the mapping-cone closure of the K-flat class — are recorded in the
implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/KFlatPullbackOfToposHom.lean` and of
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/RestrictionDerivedDirectImage.lean`, which examines
them at the corners of Stacks 075N.  It is the *only* such input: the conditional
Stacks 07A6 of `PullbackAdjunction` does not ask for `UnivLE` between the source's site and
section universes, which at such a ringed topos reads the unsynthesizable `UnivLE.{u + 1, u}`;
it asks `CategoryTheory.IsGrothendieckAbelian` of the source modules directly, which
`AlgebraicGeometry.Space.isGrothendieckAbelian_modules` supplies there.  So
`Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunction` does apply at
`AlgebraicGeometry.Space.smallEtaleRingedToposHom`, given the Stacks 06YY bundle.

*The bundle at the class of all complexes.*
`CategoryTheory.SimplicialSiteSituation.leftDerivedPullbackOfIsIsoFSharp` builds a
`LeftDerivedPullback` for a morphism whose structure map is invertible, taking *all* complexes as
the resolving class.  It is not subsumed by `kFlatLeftDerivedPullback`, even though its
hypothesis is stronger: what its consumers use is that the comparison `Lf^* ⟶ f^*` is then
invertible on *every* complex, which the K-flat class does not give.

*The unit of `Rf_*` is written out.*  The left edge of the square is the comparison
`f_* ⟶ Rf_*`, and the statement spells it as
`(pushforwardOnHomotopy f).totalRightDerivedUnit`, as the conditional statement in
`PullbackAdjunction` does, rather than giving it a name next to
`Stacks.Cohomology.DerivedPushforward.derivedPushforward`.  The name is already taken in that
namespace: `Stacks.Cohomology.DerivedPushforward.derivedPushforwardUnit`, in
`StacksFrontier/CategoryTheory/Sites/Simplicial/RingedToposMorphismDerivedPushforward.lean`, is the
same abbreviation at `RingedTopos.{u, u, u}` with its two ringed topoi as explicit arguments.
Lifting it to `DerivedPushforward/Existence.lean` beside `derivedPushforward`, at the six free
universes and with those arguments implicit, is the right home for it and would let both this
statement and that module read it off a name; it is a change to an existing signature in another
subtree and is left alone here.

*The derived category model.*  `CategoryTheory.HasDerivedCategory.standard` is installed as a
file-local instance at high priority, as it is in the two modules this one draws on: the locally
small model `SheafOfModules.hasDerivedCategory` was a global instance and does apply at these
universes, so without the priority the statements below would be about a different model from the
ones they are deduced from.

## References

* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat hasResolutions_isKFlat)

noncomputable section

universe v u w v' u' w'

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

open AlgebraicGeometry.RingedToposHom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))]

/-- **The Stacks 06YY datum for an arbitrary morphism of ringed topoi**, at the class of K-flat
complexes of `𝒪'`-modules with flat terms.

Its resolving half is Stacks 06YS,
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat`, which is a
statement about the target alone, and its exactness half is the exactness clause of
Stacks 06YY, `pullbackInvertsQuasiIso_isKFlat`, which holds along every morphism of ringed
topoi.  So the bundle exists for every `f`, with no hypothesis. -/
def kFlatLeftDerivedPullback (f : RingedToposHom X Y) : LeftDerivedPullback f :=
  LeftDerivedPullback.ofResolving f (IsKFlat (Y := Y))
    (fun M ↦ hasResolutions_isKFlat (Y := Y) M)
    (fun s hs hK hM ↦ pullbackInvertsQuasiIso_isKFlat f s hs hK hM)

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

/-- **Stacks 07A6 for a morphism of ringed topoi.**  The total left derived pullback `Lf^*` is
left adjoint to the total right derived direct image `Rf_*`,
`Hom_{D(𝒪)}(Lf^*𝒢, ℱ) = Hom_{D(𝒪')}(𝒢, Rf_*ℱ)`, bifunctorially in the unbounded derived
categories.

This is `Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunction`, Stacks 07A6
relative to the Stacks 06YY datum, at the datum `kFlatLeftDerivedPullback`; the hypothesis for
whose sake the attribute is withheld there is discharged, so there is none left. -/
@[stacks 07A6 "for a morphism of ringed topoi in the two-field sense of Tag 01D3, part (2) --
a morphism of the underlying topoi together with the structure map, with no continuous functor
between the underlying sites -- and with no hypothesis beyond those making the two categories of
modules exist"]
def derivedAdjunction (f : RingedToposHom X Y) :
    derivedPullback f ⊣ derivedPushforward (X := X) (Y := Y) f :=
  derivedPullbackPushforwardAdjunction f (kFlatLeftDerivedPullback f)

/-- **Stacks 0FPI for a morphism of ringed topoi.**  For a complex `𝒦` of `𝒪`-modules the square

```
Lf^* f_* 𝒦 ⟶ f^* f_* 𝒦
    ↓               ↓
Lf^* Rf_* 𝒦 ⟶       𝒦
```

commutes in `D(𝒪)`: its upper edge is the comparison `Lf^* ⟶ f^*` of Stacks 06YY at `f_*𝒦`, its
left edge is `Lf^*` applied to the comparison `f_* ⟶ Rf_*`, its lower edge is the counit of the
derived adjunction `Lf^* ⊣ Rf_*` of Stacks 07A6 at `Rf_*𝒦`, and its right edge is the ordinary
counit `f^*f_*𝒦 ⟶ 𝒦` of Stacks 03D7.

The derived counit is by construction the one induced by the ordinary one, which is exactly this
commutativity, so the proof is
`Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunction_counit_fac` at the
datum `kFlatLeftDerivedPullback`.

The square is stated for an object of the unbounded homotopy category rather than for a cochain
complex, which is the form the comparison maps of the two derived functors take and is more
general: a complex gives such an object through `HomotopyCategory.quotient`. -/
@[stacks 0FPI "for a morphism of ringed topoi in the two-field sense of Tag 01D3, part (2) --
a morphism of the underlying topoi together with the structure map, with no continuous functor
between the underlying sites -- and with no hypothesis beyond those making the two categories of
modules exist; stated at an object of the unbounded homotopy category, which a complex gives
through `HomotopyCategory.quotient`"]
theorem derivedAdjunction_counit_fac (f : RingedToposHom X Y)
    (K : HomotopyCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) :
    (derivedPullback f).map
        (((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit DerivedCategory.Qh
          (sourceQuasiIso X)).app K) ≫
        (derivedAdjunction f).counit.app (DerivedCategory.Qh.obj K) =
      (derivedPullbackComparison f).app ((pushforwardMapHomotopy f).obj K) ≫
        DerivedCategory.Qh.map ((pullbackAdjPushforwardMapHomotopy f).counit.app K) :=
  derivedPullbackPushforwardAdjunction_counit_fac f (kFlatLeftDerivedPullback f) K

end Stacks.Cohomology.DerivedPullbackOfToposHom

end

end
