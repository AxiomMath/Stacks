module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap

/-!
# The derived base change map transposed along the bottom of the square

Let

```
X' --g'--> X
|f'        |f
S' --g-->  S
```

be a commutative square of ringed spaces.
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap` of [Stacks, Tag 08HY] is a map
`Lg^* (Rf_* K) ⟶ Rf'_* (Lg'^* K)`, and
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_adjoint` characterises it by its
transpose under the derived adjunction **of the right-hand leg** `Lf'^* ⊣ Rf'_*`.

This file computes its transpose under the derived adjunction **along the bottom**,
`Lg^* ⊣ Rg_*`.  That transpose is a map `Rf_* K ⟶ Rg_* (Rf'_* (Lg'^* K))`, and the answer is the
one the source uses whenever it reads a base change map through `g_*`: it is the derived
pushforward along `f` of the **derived unit** of `Lg'^* ⊣ Rg'_*`, followed by the comparison of
the two iterated derived pushforwards around the square.

## Main definitions

All in the namespace `Stacks.Cohomology.DerivedBaseChange`.

* `Mate.derivedPushforwardComparisonSquare`: the comparison `Rf_* (Rg'_* M) ⟶ Rg_* (Rf'_* M)` of
  the two iterated derived pushforwards around the square — the mate of the derived base change
  map along the two adjunctions `Lg'^* ⊣ Rg'_*` and `Lg^* ⊣ Rg_*` of the square's two horizontal
  morphisms.
* `Mate.derivedPushforwardComparisonMap`: its component at a complex.

## Main results

* `Mate.derivedBaseChangeMap_unit_fac` and `derivedBaseChangeMap_unit_fac`: **the derived base
  change map transposed along the bottom of the square.**  The derived pushforward along `f` of
  the derived unit of `Lg'^* ⊣ Rg'_*`, followed by the comparison of the two iterated derived
  pushforwards, is the derived unit of `Lg^* ⊣ Rg_*` followed by the derived pushforward along
  `g` of the derived base change map.
* `Mate.derivedBaseChangeMap_homEquiv`: the same identity read as a transposition — the transpose
  of the derived base change map under `Lg^* ⊣ Rg_*` is the derived pushforward of the derived
  unit followed by the comparison.
* `Mate.derivedPushforwardComparisonSquare_eq_conjugateEquiv` and
  `derivedPushforwardComparisonSquare_eq_conjugateEquiv`: the comparison of the two iterated
  derived pushforwards is the conjugate, under the two composite derived adjunctions, of the
  comparison of the two iterated derived pullbacks — so it is an isomorphism exactly when that
  comparison is, and in particular at a square of ringed spaces, where the latter is built from
  two isomorphisms.

## Implementation notes

*Everything here is one Mathlib lemma applied once.*  `CategoryTheory.unit_mateEquiv` is the
component of the transposed mates correspondence, and
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare` is by definition
`CategoryTheory.mateEquiv` of the comparison of the two iterated derived pullbacks.  So the main
identity is that lemma at the derived adjunctions of the square's two horizontal morphisms, with
no rewriting; and the identification of the iterated-pushforward comparison is
`CategoryTheory.iterated_mateEquiv_conjugateEquiv`, which says that the mate of a mate is a
conjugate.

*Why the generic `Mate` forms come first.*  This is the discipline the rest of this directory
records for the same cube of eight categories and sixteen functors: a statement whose subterms
are variables of abstract categories costs the kernel nothing to match.  The `Mate` versions
here take the four adjunctions and the two comparison isomorphisms as arguments and mention no
ringed space.

*Why the canonical statements are spelled with `Mate.derivedPushforwardComparisonSquare` and
`Mate.derivedBaseChangeSquare` and not with a wrapper.*  The transpose identity
composes `Rf_*` of the derived unit of `Lg'^* ⊣ Rg'_*` with the comparison, so the kernel has to
see the target of the first factor, `(Lg'^* ⋙ Rg'_*)(K)` -- a composite functor applied to an
object -- as the source of the second, `Rg'_*(Lg'^*(K))`.  With `Lg'^*` and `Rg'_*` variables
those are the same term after one step.  At the canonical data they are the two spellings this
directory records as unaffordable, and the only way the application stays inside the budget is
for the statement to be written exactly as `Mate.derivedBaseChangeMap_unit_fac` writes it.

Three spellings behave as follows at the canonical data.  Writing both factors as components of the
`Mate` declarations, with the four adjunctions and two isomorphisms given explicitly, checks in
seconds.  Replacing *either* of the two by a wrapper over it fails with `(kernel) deterministic
timeout`: naming the comparison square `derivedPushforwardComparisonSquare g' f' f g sq` fails,
and so does naming the base change map `derivedBaseChangeMap g' f' f g sq K`, each on its own.
Making the wrapper an `abbrev` rather than a `def` does not help -- what costs the budget is not
the unfolding of the wrapper but the spelling of the objects its elaborated type fixes.  So no
wrapper over the comparison square is introduced at the canonical data: one would be unusable in
any statement about it.
Raising `maxHeartbeats` is not a way to finish.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

namespace Mate

variable {X' X S' S : RingedSpace.{u, u}}
  {Lf : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
  {Lg : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
  {Lf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Lg' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Lc : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
  {Rf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
  {Rg : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
  {Rg' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

/-- **The comparison of the two iterated derived pushforwards around the square**,
`Rg'_* ⋙ Rf_* ⟶ Rf'_* ⋙ Rg_*`: the mate of the derived base change map under the derived
adjunctions of the square's two horizontal morphisms.

Read at a complex `M` on `X'` it is a map `Rf_* (Rg'_* M) ⟶ Rg_* (Rf'_* M)`, comparing the two
routes around the square from `X'` to `S`. -/
def derivedPushforwardComparisonSquare : TwoSquare Rg' Rf' Rf Rg :=
  mateEquiv adjg' adjg (derivedBaseChangeSquare adjf adjf' eg ef)

/-- The comparison of the two iterated derived pushforwards, at a complex. -/
def derivedPushforwardComparisonMap
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))) :
    Rf.obj (Rg'.obj M) ⟶ Rg.obj (Rf'.obj M) :=
  (derivedPushforwardComparisonSquare adjf adjf' adjg adjg' eg ef).app M

/-- **The derived base change map transposed along the bottom of the square.**  The derived
pushforward along `f` of the derived unit of `Lg'^* ⊣ Rg'_*`, followed by the comparison of the
two iterated derived pushforwards, equals the derived unit of `Lg^* ⊣ Rg_*` followed by the
derived pushforward along `g` of the derived base change map.

This is `CategoryTheory.unit_mateEquiv` at the two horizontal adjunctions: the derived base
change map is by definition the mate of the comparison of the two iterated derived pullbacks, and
that lemma is the component of the transposed mates correspondence. -/
theorem derivedBaseChangeMap_unit_fac
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    Rf.map (adjg'.unit.app K) ≫
        (derivedPushforwardComparisonSquare adjf adjf' adjg adjg' eg ef).app (Lg'.obj K) =
      adjg.unit.app (Rf.obj K) ≫
        Rg.map ((derivedBaseChangeSquare adjf adjf' eg ef).app K) :=
  unit_mateEquiv adjg' adjg (derivedBaseChangeSquare adjf adjf' eg ef) K

/-- **The transpose of the derived base change map under `Lg^* ⊣ Rg_*`.**  It is the derived
pushforward along `f` of the derived unit of `Lg'^* ⊣ Rg'_*`, followed by the comparison of the
two iterated derived pushforwards.

This is `derivedBaseChangeMap_unit_fac` read through
`CategoryTheory.Adjunction.homEquiv_unit`. -/
theorem derivedBaseChangeMap_homEquiv
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    adjg.homEquiv (Rf.obj K) (Rf'.obj (Lg'.obj K))
        ((derivedBaseChangeSquare adjf adjf' eg ef).app K) =
      Rf.map (adjg'.unit.app K) ≫
        (derivedPushforwardComparisonSquare adjf adjf' adjg adjg' eg ef).app (Lg'.obj K) := by
  rw [Adjunction.homEquiv_unit]
  exact (derivedBaseChangeMap_unit_fac adjf adjf' adjg adjg' eg ef K).symm

/-- **The comparison of the two iterated derived pushforwards is the conjugate of the comparison
of the two iterated derived pullbacks**, under the two composite derived adjunctions
`Lf^* ⋙ Lg'^* ⊣ Rg'_* ⋙ Rf_*` and `Lg^* ⋙ Lf'^* ⊣ Rf'_* ⋙ Rg_*`.

The mate of a mate is a conjugate — `CategoryTheory.iterated_mateEquiv_conjugateEquiv` — and the
derived base change map is the mate of the pullback comparison, so iterating once more returns
the conjugate of that comparison.  In particular the iterated-pushforward comparison is an
isomorphism as soon as the iterated-pullback comparison is, which at a square of ringed spaces it
is: there it is built from the two composition isomorphisms of [Stacks, Tag 0D5S]. -/
theorem derivedPushforwardComparisonSquare_eq_conjugateEquiv :
    (derivedPushforwardComparisonSquare adjf adjf' adjg adjg' eg ef).natTrans =
      conjugateEquiv (adjf.comp adjg') (adjg.comp adjf')
        (derivedPullbackSquare eg ef).natTrans :=
  iterated_mateEquiv_conjugateEquiv adjf adjf' adjg adjg' (derivedPullbackSquare eg ef)

end Mate

section Canonical

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- **The derived base change map of a commutative square of ringed spaces, transposed along the
bottom of the square.**  The derived pushforward along `f` of the derived unit of
`Lg'^* ⊣ Rg'_*`, followed by the comparison of the two iterated derived pushforwards, equals the
derived unit of `Lg^* ⊣ Rg_*` followed by the derived pushforward along `g` of the derived base
change map of [Stacks, Tag 08HY].

`derivedBaseChangeMap_adjoint` characterises the derived base change map by its transpose under
the adjunction of the square's right-hand leg; this is its transpose under the adjunction along
the bottom, and it is the form in which the source reads a base change map through `g_*`.

Both base change maps are written as components of the `Mate` declarations rather than through a
wrapper, and this module's implementation notes record the measurement that forces that. -/
theorem derivedBaseChangeMap_unit_fac
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPushforward f).map ((derivedAdjunction g').unit.app K) ≫
        (Mate.derivedPushforwardComparisonSquare (derivedAdjunction f) (derivedAdjunction f')
          (derivedAdjunction g) (derivedAdjunction g')
          (derivedPullbackCompIsoLeft g' f' f g sq)
          (derivedPullbackCompIsoCanonical g' f)).app ((derivedPullback g').obj K) =
      (derivedAdjunction g).unit.app ((derivedPushforward f).obj K) ≫
        (derivedPushforward g).map
          ((Mate.derivedBaseChangeSquare (derivedAdjunction f) (derivedAdjunction f')
            (derivedPullbackCompIsoLeft g' f' f g sq)
            (derivedPullbackCompIsoCanonical g' f)).app K) :=
  Mate.derivedBaseChangeMap_unit_fac (derivedAdjunction f) (derivedAdjunction f')
    (derivedAdjunction g) (derivedAdjunction g') (derivedPullbackCompIsoLeft g' f' f g sq)
    (derivedPullbackCompIsoCanonical g' f) K

/-- **The comparison of the two iterated derived pushforwards around a commutative square of
ringed spaces is the conjugate of the comparison of the two iterated derived pullbacks.**  The
latter is built from the two composition isomorphisms of [Stacks, Tag 0D5S] and is therefore an
isomorphism, so the conjugate is one too
(`CategoryTheory.conjugateEquiv_of_iso`). -/
theorem derivedPushforwardComparisonSquare_eq_conjugateEquiv :
    (Mate.derivedPushforwardComparisonSquare (derivedAdjunction f) (derivedAdjunction f')
        (derivedAdjunction g) (derivedAdjunction g')
        (derivedPullbackCompIsoLeft g' f' f g sq)
        (derivedPullbackCompIsoCanonical g' f)).natTrans =
      conjugateEquiv ((derivedAdjunction f).comp (derivedAdjunction g'))
        ((derivedAdjunction g).comp (derivedAdjunction f'))
        (derivedPullbackSquare g' f' f g sq).natTrans :=
  Mate.derivedPushforwardComparisonSquare_eq_conjugateEquiv (derivedAdjunction f)
    (derivedAdjunction f') (derivedAdjunction g) (derivedAdjunction g')
    (derivedPullbackCompIsoLeft g' f' f g sq) (derivedPullbackCompIsoCanonical g' f)

end Canonical

end

end Stacks.Cohomology.DerivedBaseChange

end
