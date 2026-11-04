module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
import StacksCore.Tactic.StacksAttribute

/-!
# The ordinary and the derived comparisons of a morphism of ringed spaces, as mates

Let

```
X' --g'--> X
|f'        |f
S' --g-->  S
```

be a commutative square of ringed spaces. Two base change maps are attached to it: the
**derived** one, `Lg^* Rf_* ⟶ Rf'_* L(g')^*` of [Stacks, Tag 08HY]
(`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap`), and the **ordinary** one,
`g^* f_* ⟶ f'_* (g')^*`. Identifying them is what a statement about the *sections* of the derived
base change map needs, because `derivedBaseChangeMap_adjoint` characterises that map only by its
transpose under the derived adjunctions while sections see the ordinary unit and counit. The
comparison of the ordinary with the derived counit is [Stacks, Tag 0FP1] —
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_counit_fac` — and it is
stated for a **single** morphism, as an equality of two particular composites.

This file recasts 0FP1 in the form in which it can be assembled across a square at all: both
base change maps are **mates**, `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap` being
`CategoryTheory.mateEquiv` of the comparison of iterated pullbacks, and the two comparison maps
of one morphism — `Lf^* ⟶ f^*` and `f_* ⟶ Rf_*` — are shown here to be mates of one another,
under the degreewise adjunction and the derived adjunction of that morphism. In that form 0FP1
enters the mate calculus of `CategoryTheory.mateEquiv_vcomp` and `mateEquiv_hcomp`, which is
how a statement about one morphism reaches a statement about a square.

## Main results

Both in the namespace `Stacks.Cohomology.DerivedBaseChange`.

* `mateEquiv_derivedPullbackComparison`: **[Stacks, Tag 0FP1] as a mate identity.** The
  comparison `Lf^* ⟶ f^*` and the comparison `f_* ⟶ Rf_*` are mates of one another under the
  degreewise adjunction `f^* ⊣ f_*` of [Stacks, Tag 0096] and the derived adjunction
  `Lf^* ⊣ Rf_*` of [Stacks, Tag 079W].
* `derivedPullbackComparison_eqToIso`: the comparison `Lk^* ⟶ k^*` commutes with the transport
  along an equality of morphisms of ringed spaces.

## Implementation notes

*Why the mate identity is the right form of 0FP1.* `derivedAdjunction_counit_fac` says that one
particular composite of the derived counit equals one particular composite of the ordinary one.
Mathlib's `CategoryTheory.mateEquiv_counit` says that the mate of a two-square satisfies exactly
such an identity, and `CategoryTheory.Adjunction.homEquiv` is injective, so the identity
*determines* the mate. Phrasing 0FP1 as `mateEquiv … (derivedPullbackComparison f) =
derivedPushforwardUnit f` therefore loses nothing, and it makes the tag usable wherever a mate
appears — in particular for the base change map, which is a mate by construction.

*The two comparisons are two-squares on the nose.*
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f` is
`f^* ⋙ Qh` and `pushforwardToDerivedCategory f` is `f_* ⋙ Qh`, so
`derivedPullbackComparison f : Qh ⋙ Lf^* ⟶ f^* ⋙ Qh` is a
`CategoryTheory.TwoSquare Qh f^* Lf^* Qh` and `derivedPushforwardUnit f : f_* ⋙ Qh ⟶ Qh ⋙ Rf_*`
is the two-square `mateEquiv` produces from it. No transport intervenes; the `TwoSquare.mk`
wrappers in the statement are the identity and are written only so that the elaborator does not
have to unfold `TwoSquare` to see which square is meant.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0FP1](https://stacks.math.columbia.edu/tag/0FP1)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

section OneMorphism

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **[Stacks, Tag 0FP1] as a mate identity.** For a morphism of ringed spaces `f`, the
comparison `Lf^* ⟶ f^*` of the derived with the degreewise pullback and the comparison
`f_* ⟶ Rf_*` of the degreewise with the derived pushforward are mates of one another, under the
degreewise adjunction `f^* ⊣ f_*` of [Stacks, Tag 0096] and the derived adjunction
`Lf^* ⊣ Rf_*` of [Stacks, Tag 079W].

`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_counit_fac` is the identity
`CategoryTheory.mateEquiv_counit` asserts of the mate, and the transposition bijection of the
derived adjunction is injective, so that identity pins the mate down. -/
theorem mateEquiv_derivedPullbackComparison :
    mateEquiv (homotopyPullbackPushforwardAdjunction f) (derivedAdjunction f)
        (TwoSquare.mk _ _ _ _ (derivedPullbackComparison f)) =
      TwoSquare.mk _ _ _ _ (derivedPushforwardUnit f) := by
  refine TwoSquare.ext _ _ fun K => ?_
  refine ((derivedAdjunction f).homEquiv _ _).symm.injective ?_
  simp only [Adjunction.homEquiv_counit]
  exact (mateEquiv_counit (homotopyPullbackPushforwardAdjunction f) (derivedAdjunction f)
      (TwoSquare.mk _ _ _ _ (derivedPullbackComparison f)) K).trans
    (derivedAdjunction_counit_fac f K).symm

/-- **The comparison `Lk^* ⟶ k^*` is compatible with transport along an equality of morphisms.**
Both the derived and the degreewise pullback are functions of the morphism, so an equality of
morphisms transports the comparison, compatibly with the transport of the degreewise pullback
along the same equality. -/
theorem derivedPullbackComparison_eqToIso {Z W : RingedSpace.{u, u}} {k₁ k₂ : Z ⟶ W}
    (e : k₁ = k₂)
    (N : HomotopyCategory (SheafOfModules.{u} (structureSheafRing W)) (ComplexShape.up ℤ)) :
    (derivedPullbackComparison k₁).app N ≫
        DerivedCategory.Qh.map ((eqToIso (congrArg (fun k : Z ⟶ W =>
          (modulePullback k).mapHomotopyCategory (ComplexShape.up ℤ)) e)).hom.app N) =
      (eqToIso (congrArg (fun k : Z ⟶ W => derivedPullback k) e)).hom.app
          (DerivedCategory.Qh.obj N) ≫
        (derivedPullbackComparison k₂).app N := by
  subst e
  simp

end OneMorphism

end Stacks.Cohomology.DerivedBaseChange

end
