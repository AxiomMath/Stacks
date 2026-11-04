module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedBaseChangeAgreesWithOrdinary

/-!
# The ordinary base change map transposed along the bottom of the square

Let

```
X' --g'--> X
|f'        |f
S' --g-->  S
```

be a commutative square of ringed spaces.  `Stacks.Cohomology.DerivedBaseChange`
`.homotopyBaseChangeSquare` is its **ordinary** base change map, the mate of the comparison of the
two iterated degreewise pullbacks under the degreewise adjunctions `k^* ⊣ k_*` of
[Stacks, Tag 0096] on the unbounded homotopy categories, and
`homotopyBaseChangeSquare_counit_fac` characterises it by its transpose under the adjunction of
the square's **right-hand leg**.

This file computes its transpose under the adjunction **along the bottom**: it is the degreewise
pushforward along `f` of the degreewise unit of `(g')^* ⊣ g'_*`, followed by the comparison of the
two iterated degreewise pushforwards around the square.

This is the analogue, at the degreewise adjunctions, of
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_unit_fac`, which does the same at the
derived adjunctions of [Stacks, Tag 079W].  The two are related by
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_fac`: the derived base change map of
the square agrees with the ordinary one, conjugated by the two comparisons of the models.

## Main definitions

* `Stacks.Cohomology.DerivedBaseChange.homotopyPushforwardComparisonSquare`: the comparison
  `f_* (g'_* M) ⟶ g_* (f'_* M)` of the two iterated degreewise pushforwards around the square,
  on the unbounded homotopy categories — the mate of the ordinary base change map along the two
  degreewise adjunctions of the square's two horizontal morphisms.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.homotopyBaseChangeSquare_unit_fac`: **the ordinary base
  change map transposed along the bottom of the square.**
* `Stacks.Cohomology.DerivedBaseChange.homotopyBaseChangeSquare_homEquiv`: the same identity read
  as a transposition.
* `Stacks.Cohomology.DerivedBaseChange.homotopyPushforwardComparisonSquare_eq_conjugateEquiv`: the
  comparison of the two iterated degreewise pushforwards is the conjugate, under the two
  composite degreewise adjunctions, of the comparison of the two iterated degreewise pullbacks —
  so it is an isomorphism exactly when that comparison is, and that one is built from the two
  degreewise composition isomorphisms.

## Implementation notes

*Each result is one Mathlib lemma applied once.*  `CategoryTheory.unit_mateEquiv` is the component
of the transposed mates correspondence and `homotopyBaseChangeSquare` is by definition
`CategoryTheory.mateEquiv` of the comparison of the two iterated degreewise pullbacks, so the
first result is that lemma at the two horizontal degreewise adjunctions with no rewriting; the
third is `CategoryTheory.iterated_mateEquiv_conjugateEquiv`, the mate of a mate being a
conjugate.

*The two base change maps in the statements are written as `CategoryTheory.mateEquiv` of
`homotopyBaseChangeSquare` and as `homotopyBaseChangeSquare` itself, not through a wrapper.*  At
the derived adjunctions, naming either factor through a wrapper — even a reducible one — turns the
application into a kernel timeout, because the kernel then has to reconcile `(g'^* ⋙ g'_*)(M)`
with `g'_*(g'^*(M))` at functors it cannot afford to unfold; the same spelling is used here.
`homotopyPushforwardComparisonSquare` is the same term as the `CategoryTheory.mateEquiv` written
in the statements.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0FP1](https://stacks.math.columbia.edu/tag/0FP1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- **The comparison of the two iterated degreewise pushforwards around the square**, as a
morphism of functors `g'_* ⋙ f_* ⟶ f'_* ⋙ g_*` on the unbounded homotopy categories: the mate of
the ordinary base change map `Stacks.Cohomology.DerivedBaseChange.homotopyBaseChangeSquare` under
the degreewise adjunctions of the square's two horizontal morphisms.

Read at a complex `M` of `𝒪_{X'}`-modules it is a map `f_* (g'_* M) ⟶ g_* (f'_* M)`, comparing
the two routes around the square from `X'` to `S`. -/
def homotopyPushforwardComparisonSquare :
    TwoSquare ((modulePushforward g').mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePushforward f').mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ)) :=
  mateEquiv (homotopyPullbackPushforwardAdjunction g')
    (homotopyPullbackPushforwardAdjunction g) (homotopyBaseChangeSquare g' f' f g sq)

/-- **The ordinary base change map transposed along the bottom of the square.**  The degreewise
pushforward along `f` of the degreewise unit of `(g')^* ⊣ g'_*`, followed by the comparison of the
two iterated degreewise pushforwards, equals the degreewise unit of `g^* ⊣ g_*` followed by the
degreewise pushforward along `g` of the ordinary base change map.

`homotopyBaseChangeSquare_counit_fac` characterises the ordinary base change map by its transpose
under the adjunction of the square's right-hand leg; this is its transpose under the adjunction
along the bottom. -/
theorem homotopyBaseChangeSquare_unit_fac
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((homotopyPullbackPushforwardAdjunction g').unit.app M) ≫
        (mateEquiv (homotopyPullbackPushforwardAdjunction g')
            (homotopyPullbackPushforwardAdjunction g)
            (homotopyBaseChangeSquare g' f' f g sq)).app
          (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M) =
      (homotopyPullbackPushforwardAdjunction g).unit.app
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        ((modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((homotopyBaseChangeSquare g' f' f g sq).app M) :=
  unit_mateEquiv (homotopyPullbackPushforwardAdjunction g')
    (homotopyPullbackPushforwardAdjunction g) (homotopyBaseChangeSquare g' f' f g sq) M

/-- **The transpose of the ordinary base change map under the degreewise adjunction
`g^* ⊣ g_*`.**  It is the degreewise pushforward along `f` of the degreewise unit of
`(g')^* ⊣ g'_*`, followed by the comparison of the two iterated degreewise pushforwards.

This is `homotopyBaseChangeSquare_unit_fac` read through
`CategoryTheory.Adjunction.homEquiv_unit`. -/
theorem homotopyBaseChangeSquare_homEquiv
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (homotopyPullbackPushforwardAdjunction g).homEquiv
        (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)
        (((modulePushforward f').mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M))
        ((homotopyBaseChangeSquare g' f' f g sq).app M) =
      ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((homotopyPullbackPushforwardAdjunction g').unit.app M) ≫
        (mateEquiv (homotopyPullbackPushforwardAdjunction g')
            (homotopyPullbackPushforwardAdjunction g)
            (homotopyBaseChangeSquare g' f' f g sq)).app
          (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M) := by
  rw [Adjunction.homEquiv_unit]
  exact (homotopyBaseChangeSquare_unit_fac g' f' f g sq M).symm

/-- **The comparison of the two iterated degreewise pushforwards is the conjugate of the
comparison of the two iterated degreewise pullbacks**, under the two composite degreewise
adjunctions. -/
theorem homotopyPushforwardComparisonSquare_eq_conjugateEquiv :
    (mateEquiv (homotopyPullbackPushforwardAdjunction g')
          (homotopyPullbackPushforwardAdjunction g)
          (homotopyBaseChangeSquare g' f' f g sq)).natTrans =
      conjugateEquiv ((homotopyPullbackPushforwardAdjunction f).comp
          (homotopyPullbackPushforwardAdjunction g'))
        ((homotopyPullbackPushforwardAdjunction g).comp
          (homotopyPullbackPushforwardAdjunction f'))
        (homotopyPullbackSquare g' f' f g sq).natTrans :=
  iterated_mateEquiv_conjugateEquiv (homotopyPullbackPushforwardAdjunction f)
    (homotopyPullbackPushforwardAdjunction f') (homotopyPullbackPushforwardAdjunction g)
    (homotopyPullbackPushforwardAdjunction g') (homotopyPullbackSquare g' f' f g sq)

end Stacks.Cohomology.DerivedBaseChange

end
