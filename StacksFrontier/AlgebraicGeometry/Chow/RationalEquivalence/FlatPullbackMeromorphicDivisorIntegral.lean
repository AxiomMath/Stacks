module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackMeromorphicSection
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisorIntegral
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback of the divisor of a meromorphic section to an integral scheme

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
integral and locally of finite type over `S` with `n = dim_δ(Y)`, let `f : X ⟶ Y` be flat of
relative dimension `r`, let `L` be an invertible `𝒪_Y`-module and let `s` be a nonzero
meromorphic section of `L`. Then

  `f^* div_L(s) = div_{f^*L}(f^*s)`

in `Z_{n + r - 1}(X)`, and consequently

  `f^*(c₁(L) ∩ [Y]) = c₁(f^*L) ∩ [X]`

in `A_{n + r - 1}(X)`.

## Main results

* `Stacks.Chow.flatPullback_meromorphicDivisorCycle` — the identity of cycles.
* `Stacks.Chow.mk_flatPullback_meromorphicDivisorCycle` — **Stacks 02SM**: the identity of
  classes in the Chow group.

## Implementation notes

The source proves the cycle identity and deduces the identity of classes from it; the same two
steps are taken here, the second being the image of the first under the quotient map.

The cycle identity is the local argument of the source run at a point: a generator of the stalk
`L_{f(x)}` expresses `s` as `g · s_{f(x)}` for a rational function `g` on `Y`, and over a
neighbourhood of `f(x)` on which `s_{f(x)}` generates both divisors are the principal divisor of
`g`, so the identity follows from `Stacks.Chow.flatPullback_principalDivisorCycle`, Stacks 02RR.
In the generic-stalk model such a `g` is a coordinate of `s` at `f(x)` in the sense of Stacks
02SF, the comparison of the two divisors at a single point is
`Stacks.Chow.meromorphicDivisorCycle_apply_eq_principalDivisorCycle_apply`, and that a coordinate
of `s` at `f(x)` pulls back to a coordinate of `f^*s` at `x` is
`Stacks.Divisors.IsCoordinateAt.pullback`.

The two sides of the cycle identity are compared as algebraic cycles rather than as elements of a
cycle group: the flat pullback of `div_L(s) ∈ Z_{n-1}(Y)` is built in `Z_{(n-1)+r}(X)` while
`div_{f^*L}(f^*s)` is built in `Z_{(n+r)-1}(X)`, and these indices are equal integers but
distinct terms. The identity of classes carries the transport between them,
`Stacks.Chow.val_cycleGroup_cast` being that it changes no coefficient.

The delta-dimension `n + r` of the source is a consequence of flatness rather than a hypothesis,
by `Stacks.Chow.schemeDeltaDimension_eq_add_of_flat`. So are the three instance hypotheses
carried below, all of them `Prop`s and none of them an assumption: `X` and `Y` are locally
Noetherian because they are locally of finite type over the base, by
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, and `f^*L` is invertible by
Stacks 0B8L, which is `Stacks.Chow.isInvertible_presheaf_pullback`. In the generic-stalk model of
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder` a meromorphic section of `L` on an integral
scheme is an element of the stalk `L_η` at the generic point, nonzero exactly when that element
is, its pullback along a dominant morphism is `Stacks.Divisors.genericStalkPullback`, and
`c₁(L) ∩ [Y]` is the class of `div_L(s)` for a nonzero `s`, which by
`Stacks.Chow.mk_meromorphicDivisorCycleOfInvertible_eq` does not depend on `s`.

## References

* [Stacks Project, Tag 02SM](https://stacks.math.columbia.edu/tag/02SM)
* [Stacks Project, Tag 02RR](https://stacks.math.columbia.edu/tag/02RR)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

attribute [local instance] isDominant_of_flat

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
  [IsLocallyNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sY = sX)
  (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) {n : ℤ}
  (hY : schemeDeltaDimension C sY = (n : EInt)) (L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
    ((Scheme.Modules.pullback f).obj L)]
  (s : L.presheaf.stalk (genericPoint Y))

/-! ### The identity of cycles -/

/-- **The flat pullback of the divisor of a meromorphic section to an integral scheme.** Let
`C = (S, δ)` be the base situation of chapter 42, let `X` and `Y` be integral and locally of
finite type over `S` with `n = dim_δ(Y)`, and let `f : X ⟶ Y` be flat of relative dimension `r`.
For an invertible module `L` on `Y` and a nonzero meromorphic section `s` of `L`,

  `f^* div_L(s) = div_{f^*L}(f^*s)`

in `Z_{n + r - 1}(X)`.

The two sides are compared as algebraic cycles because they are built in two gradings which are
equal integers and distinct terms; see the module documentation. -/
theorem flatPullback_meromorphicDivisorCycle (hs : s ≠ 0) :
    (flatPullback C sX sY f hbase r hf (n - 1)
        (meromorphicDivisorCycleOfInvertible C sY hY L s).val).1 =
      (meromorphicDivisorCycleOfInvertible C sX
        (schemeDeltaDimension_eq_add_of_flat C sX sY f hbase r hf hY)
        ((Scheme.Modules.pullback f).obj L) (genericStalkPullback f L s)).val.1 := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  -- a coordinate of `s` at the image of `x`, in the sense of Stacks 02SF
  obtain ⟨a, ha⟩ := exists_isCoordinateAt (isTrivializedNear_of_isInvertible L (f.base x)) s
  calc (flatPullback C sX sY f hbase r hf (n - 1)
          (meromorphicDivisorCycleOfInvertible C sY hY L s).val).1 x
      = (flatPullback C sX sY f hbase r hf (n - 1) (principalDivisorCycle C sY hY a)).1 x := by
        rw [flatPullback_apply, flatPullback_apply,
          meromorphicDivisorCycle_apply_eq_principalDivisorCycle_apply C sY hY L s ha]
    _ = (principalDivisorCycle C sX
          (schemeDeltaDimension_eq_add_of_flat C sX sY f hbase r hf hY)
          (dominantFunctionFieldMap f a)).1 x := by
        rw [flatPullback_principalDivisorCycle C sX sY f hbase r hf hY a (ha.ne_zero hs)]
    _ = (meromorphicDivisorCycleOfInvertible C sX
          (schemeDeltaDimension_eq_add_of_flat C sX sY f hbase r hf hY)
          ((Scheme.Modules.pullback f).obj L) (genericStalkPullback f L s)).val.1 x :=
        (meromorphicDivisorCycle_apply_eq_principalDivisorCycle_apply C sX
          (schemeDeltaDimension_eq_add_of_flat C sX sY f hbase r hf hY)
          ((Scheme.Modules.pullback f).obj L) (genericStalkPullback f L s) ha.pullback).symm

/-! ### Stacks 02SM -/

/-- **Stacks 02SM.** Let `C = (S, δ)` be the base situation of chapter 42, let `X` and `Y` be
integral and locally of finite type over `S` with `n = dim_δ(Y)`, and let `f : X ⟶ Y` be flat of
relative dimension `r`. For an invertible module `L` on `Y`,

  `f^*(c₁(L) ∩ [Y]) = c₁(f^*L) ∩ [X]`

in `A_{n + r - 1}(X)`, where either side is the class of the divisor of a nonzero meromorphic
section, read on `Y` and pulled back on the left and read on `X` on the right.

The integrality of `X` is a hypothesis of the source, which assumes both `X` and `Y` integral;
the case of a general `X` is subsumed by Stacks 02SS. -/
@[stacks 02SM "the flat pullback read on the divisor of a nonzero meromorphic section"]
theorem mk_flatPullback_meromorphicDivisorCycle (hs : s ≠ 0) :
    (QuotientAddGroup.mk ((show (n : ℤ) - 1 + (r : ℤ) = n + (r : ℤ) - 1 by ring) ▸
          flatPullback C sX sY f hbase r hf (n - 1)
            (meromorphicDivisorCycleOfInvertible C sY hY L s).val) :
        chowGroup C sX (n + (r : ℤ) - 1)) =
      QuotientAddGroup.mk (meromorphicDivisorCycleOfInvertible C sX
        (schemeDeltaDimension_eq_add_of_flat C sX sY f hbase r hf hY)
        ((Scheme.Modules.pullback f).obj L) (genericStalkPullback f L s)).val := by
  refine congrArg QuotientAddGroup.mk (Subtype.ext ?_)
  rw [val_cycleGroup_cast]
  exact flatPullback_meromorphicDivisorCycle C sX sY f hbase r hf hY L s hs

end Stacks.Chow

end
