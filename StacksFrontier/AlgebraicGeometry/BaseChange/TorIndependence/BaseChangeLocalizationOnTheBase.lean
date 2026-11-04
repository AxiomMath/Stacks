module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeLocalOnTheBase
import StacksCore.Tactic.StacksAttribute

/-!
# The derived base-change map restricted to an open of the base

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of ringed spaces and let `j : T ⟶ S'` be an open immersion, with

```
X_T --k--> X'
|          |
f_T        f'
v          v
T ---j---> S'
```

Cartesian.  The restriction along `j` of the derived base-change map of Stacks 08HY for the
original square *is* — up to the two composition isomorphisms of Stacks 0D5S, which are
isomorphisms — the derived base-change map of the outer rectangle, the square with verticals
`f` and `f_T` and horizontals `k ≫ g'` and `j ≫ g`.  Hence the one is invertible exactly when
the other is.

This is the form in which the first step of the proof of Stacks 0DJ9 — *"to check the map is an
isomorphism we may work locally on `S'`"* — consumes the localization step.  The localization
step itself,
`Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions`, says that
the base-change map of a Cartesian square whose horizontal arrows are open immersions is
invertible; what the reduction needs in addition is that the restricted base-change map and the
base-change map of the restricted square agree, and that is a single application of the
horizontal pasting law of Stacks 0ATM.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.isIso_derivedPullback_map_derivedBaseChangeMap_iff_scheme`:
  for a Cartesian square of schemes and an open immersion `j : T ⟶ S'` of schemes, with the
  Cartesian square over `T` taken to be the canonical pullback, the restriction along `j` of the
  base-change map is invertible exactly when the base-change map of the outer rectangle is.  The
  statement for ringed spaces is
  `Stacks.Cohomology.DerivedBaseChange.isIso_derivedPullback_map_derivedBaseChangeMap_iff`.

## Implementation notes

The statement is at `CategoryTheory.HasDerivedCategory.standard`, the model at which
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap` and the pasting laws of
Stacks 0ATL and Stacks 0ATM are declared.  Nothing is claimed about the locally small model.

The statement for ringed spaces takes the Cartesian square over `T` and both open immersions
as inputs, since the forgetful functor from schemes need not preserve a Cartesian square without
one leg being an open immersion.  The scheme-level statement supplies them from
`Stacks.Cohomology.DerivedBaseChange.isPullback_toShHom_of_isOpenImmersion`.

No tag is carried.  Stacks 0ATM is registered on
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_comp_horizontal` and the open-immersion
case of Stacks 0DJ9's localization step on
`isIso_derivedBaseChangeMap_of_isOpenImmersions`; the statement below is those two read
together, and the source states neither separately.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0ATM](https://stacks.math.columbia.edu/tag/0ATM)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **The base-change map of a square of schemes, restricted to an open of the base.**  For a
commutative square of schemes with verticals `f`, `f'` and horizontals `g'`, `g`, and an open
immersion `j : T ⟶ S'`, the derived pullback along `j` of the derived base-change map of
Stacks 08HY is invertible exactly when the base-change map of the square obtained by replacing
`S'` by `T` and `X'` by `T ×_{S'} X'` is.

This is the shape in which the reduction *"we may work locally on `S'`"* of Stacks 0DJ9 uses the
localization step: the right-hand side is the conclusion of Stacks 0DJ9 for the square over `T`,
and the left-hand side is the restriction to `T` of the conclusion over `S'`.  Together with a
criterion detecting invertibility in `D(𝒪_{S'})` on an open cover it reduces Stacks 0DJ9 to the
case of an affine `S'`. -/
public theorem isIso_derivedPullback_map_derivedBaseChangeMap_iff_scheme
    {X' X S' S T : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (j : T ⟶ S') [AlgebraicGeometry.IsOpenImmersion j]
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    IsIso ((derivedPullback j.toLRSHom.toShHom).map
        (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
          g.toLRSHom.toShHom sq K)) ↔
      IsIso (derivedBaseChangeMap
        ((pullback.fst f' j).toLRSHom.toShHom ≫ g'.toLRSHom.toShHom)
        (pullback.snd f' j).toLRSHom.toShHom f.toLRSHom.toShHom
        (j.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
        (hcomp_square (pullback.fst f' j).toLRSHom.toShHom g'.toLRSHom.toShHom
          (pullback.snd f' j).toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
          j.toLRSHom.toShHom g.toLRSHom.toShHom sq
          (isPullback_toShHom_of_isOpenImmersion (pullback.fst f' j) (pullback.snd f' j) f' j
            (IsPullback.of_hasPullback f' j)).w) K) :=
  have : AlgebraicGeometry.IsOpenImmersion (pullback.fst f' j) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsOpenImmersion)
      (IsPullback.of_hasPullback f' j).flip inferInstance
  isIso_derivedPullback_map_derivedBaseChangeMap_iff (pullback.fst f' j).toLRSHom.toShHom
    g'.toLRSHom.toShHom (pullback.snd f' j).toLRSHom.toShHom f'.toLRSHom.toShHom
    f.toLRSHom.toShHom j.toLRSHom.toShHom g.toLRSHom.toShHom sq
    (isPullback_toShHom_of_isOpenImmersion (pullback.fst f' j) (pullback.snd f' j) f' j
      (IsPullback.of_hasPullback f' j)) K

end Stacks.Cohomology.DerivedBaseChange

end
