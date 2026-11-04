module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.DivisorCycle
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionPullback
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback of the divisor of a meromorphic section

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
schemes locally of finite type over `S` with `Y` integral of delta-dimension `n`, let
`f : X ⟶ Y` be flat of relative dimension `r`, let `L` be an invertible `𝒪_Y`-module and let `s`
be a nonzero meromorphic section of `L`. The flat pullback of the divisor of `s` is

  `f^* div_L(s) = ∑_i n_i i_{i,*} div_{f^*L|_{X_i}}(s_i)`

as `(n + r - 1)`-cycles on `X`, where the sum runs over the irreducible components `X_i` of `X`
taken with their reduced structure, `i_i : X_i ⟶ X` is the inclusion, `s_i` is the pullback of
`s` along `f|_{X_i}` and `n_i` is the multiplicity of `X_i` in `X`, that is the coefficient of
`X_i` in the fundamental cycle `[X]_{n + r}`. This is
[Stacks, Tag 0EPJ](https://stacks.math.columbia.edu/tag/0EPJ).

## The reduction to the principal divisor

The source proves the identity by localizing on `Y`, writing `s` as a ratio of a global section
of `L` by a global function and invoking additivity. This file instead reduces it in one step to
the same identity for a rational function, which this repository already proves as
`Stacks.Chow.flatPullback_principalDivisor_eq_sum_components`
([Stacks, Tag 0EPH](https://stacks.math.columbia.edu/tag/0EPH)).

The identity is read coefficientwise at a point `x` of `X`. Both sides involve `s` only through
orders of vanishing at points lying over `y = f(x)`: the left hand side through
`ord_{Z, L}(s)` at `y`, and the right hand side through `ord_{Z_i, f^*L|_{X_i}}(s_i)` at the
points of the components above `x`. Pick a coordinate `a ∈ R(Y)` of `s` at `y` in the sense of
Stacks 02SF, that is a rational function with `s = a · m` for some basis `m` of the stalk `L_y`.
Then

* `ord_{Z, L}(s) = ord_y(a)` at `y`, by `Stacks.Divisors.orderOfVanishing_eq`;
* the image of `a` in `R(X_i)` is a coordinate of `s_i` at each point of `X_i` above `x`, by
  `Stacks.Divisors.IsCoordinateAt.pullback`, so the orders of vanishing of `s_i` there are those
  of that image.

So at `x` both sides of the identity for `s` agree with both sides of the identity for `a`, and
`Stacks.Chow.meromorphicDivisorCycle_apply_eq_principalDivisorCycle_apply` is that comparison of
coefficients in the form the two sides need. Nonvanishing of `s` enters exactly once, to make
the coordinate `a` nonzero, which Stacks 0EPH requires.

## The range of the sum

The source sums over the irreducible components of `X` of delta-dimension `n + r`. That
restriction is vacuous under the hypotheses: along a flat morphism of relative dimension `r` to
an integral scheme of delta-dimension `n` *every* irreducible component of the source has
delta-dimension `n + r`, which is
`Stacks.Chow.schemeDeltaDimension_integralComponentAt_comp` and is what supplies the grading of
each summand below. So the sum over all components is the sum the source writes, and this is the
same convention as `Stacks.Chow.flatPullback_principalDivisor_eq_sum_components`.

## How a meromorphic section is modelled

In the generic-stalk model of `StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder` a
meromorphic section of `L` on an integral scheme is an element of the stalk `L_η` at the generic
point and is nonzero exactly when that element is nonzero; its divisor cycle is
`Stacks.Chow.meromorphicDivisorCycleOfInvertible` and its pullback along a dominant morphism is
`Stacks.Divisors.genericStalkPullback`. See the module documentation of
`StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.DivisorCycle` for why the identification of
that model with the sheaf `K_X(L)` of Stacks 01X5 (2) is not available here.

## Main results

* `Stacks.Chow.meromorphicDivisorCycle_apply_eq_principalDivisorCycle_apply` — the divisor cycle
  of a meromorphic section and the principal divisor of a coordinate of it at a point have the
  same coefficient at that point.
* `Stacks.Chow.flatPullback_meromorphicDivisor_eq_sum_components` — **Stacks 0EPJ**.

## Implementation notes

The statement carries `letI` instances rather than hypotheses: that `Y` and each component are
locally Noetherian follows from being locally of finite type over the base, that each reduced
irreducible component of `X` is integral and dominates `Y` are consequences of flatness, and the
invertibility of the restriction of `L` to a component is Stacks 0B8L. None of them is an extra
assumption, and all of them are `Prop`s.

## References

* [Stacks Project, Tag 0EPJ](https://stacks.math.columbia.edu/tag/0EPJ)
* [Stacks Project, Tag 0EPH](https://stacks.math.columbia.edu/tag/0EPH)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### Invertibility of a restricted module -/

/-- **Stacks 0B8L** with the structure sheaf spelled as `Scheme.presheaf` and its sheaf condition
as `Scheme.ringCatSheaf.2` on *both* sides: the pullback of an invertible module along a morphism
of schemes is invertible. This is the spelling
`Stacks.Chow.meromorphicDivisorCycleOfInvertible` and
`Stacks.Divisors.isTrivializedNear_of_isInvertible` consume, so stating the hypothesis in it
avoids translating at every use. -/
theorem isInvertible_presheaf_pullback {Y : Scheme.{u}} (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    {W : Scheme.{u}} (g : W ⟶ Y) :
    AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj L) :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L :=
    ‹AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L›
  isInvertible_presheaf_modulePullback L g

/-! ### The divisor of a meromorphic section against the divisor of a coordinate -/

/-- **The coefficient of the divisor of a meromorphic section is the coefficient of the principal
divisor of a coordinate of it.** If the rational function `b` on an integral scheme `A` expresses
the meromorphic section `t` of the invertible module `M` in terms of a basis of the stalk `M_z`,
then `div_M(t)` and `div(b)` have the same coefficient at `z`.

At a point of codimension one this is the characterization of the order of vanishing by a
coordinate, [Stacks, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF); elsewhere both
coefficients vanish, since a cycle of delta-dimension `m - 1` on a scheme of delta-dimension `m`
is concentrated on the points of codimension one. The two cycles are of course *not* equal: `b`
is a coordinate at `z` only, and a different point calls for a different coordinate. -/
theorem meromorphicDivisorCycle_apply_eq_principalDivisorCycle_apply (C : ChowSituation.{u})
    {A : Scheme.{u}} (q : A ⟶ C.S) [LocallyOfFiniteType q] [IsIntegral A]
    [IsLocallyNoetherian A] {m : ℤ} (hm : schemeDeltaDimension C q = (m : EInt)) (M : A.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.presheaf A.ringCatSheaf.2 M]
    (t : M.presheaf.stalk (genericPoint A)) {b : A.functionField} {z : A}
    (hb : IsCoordinateAt M z t b) :
    ((meromorphicDivisorCycleOfInvertible C q hm M t).val : AlgebraicCycle A ℤ) z =
      (principalDivisorCycle C q hm b : AlgebraicCycle A ℤ) z := by
  have hval : ((meromorphicDivisorCycleOfInvertible C q hm M t).val : AlgebraicCycle A ℤ) z =
      ((meromorphicDivisorCycle C q hm (isTrivializedNear_of_isInvertible M) t).val :
        AlgebraicCycle A ℤ) z := rfl
  rw [hval, principalDivisorCycle_apply]
  by_cases hco : coheight z = 1
  · have hgen : (PrimeDivisor.ofCoheightOne z hco).genericPoint = z :=
      PrimeDivisor.genericPoint_ofCoheightOne z hco
    have h1 := meromorphicDivisorCycle_genericPoint C q hm
      (isTrivializedNear_of_isInvertible M) t (PrimeDivisor.ofCoheightOne z hco)
    have hb' : IsCoordinateAt M (PrimeDivisor.ofCoheightOne z hco).genericPoint t b := by
      rw [hgen]; exact hb
    have h2 := orderOfVanishing_eq (L := M)
      (isTrivializedNear_of_isInvertible M (PrimeDivisor.ofCoheightOne z hco).genericPoint) hb'
    rw [hgen] at h1 h2
    rw [h1, h2]
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hco b]
    exact meromorphicDivisorCycle_eq_zero C q hm (isTrivializedNear_of_isInvertible M) t z
      fun Z hZ ↦ hco (hZ ▸ PrimeDivisor.coheight_genericPoint Z)

/-! ### Stacks 0EPJ -/

/-- **Stacks 0EPJ.** Let `C = (S, δ)` be the base situation of chapter 42, let `X` and `Y` be
locally of finite type over `S` with `Y` integral of delta-dimension `n`, and let `f : X ⟶ Y` be
flat of relative dimension `r`. For an invertible module `L` on `Y` and a *nonzero* meromorphic
section `s` of `L`,

  `f^* div_L(s) = ∑_i n_i i_{i,*} div_{f^*L|_{X_i}}(s_i)`

as `(n + r - 1)`-cycles on `X`. The sum runs over the irreducible components `X_i` of `X` taken
with their reduced structure — each of these has delta-dimension `n + r` by
`Stacks.Chow.schemeDeltaDimension_integralComponentAt_comp`, so this is the sum over the
components of delta-dimension `n + r` that the source writes — `i_i : X_i ⟶ X` is the inclusion,
`s_i` is the pullback of `s` along `f|_{X_i}`, and `n_i` is the multiplicity of `X_i` in `X`,
read as the coefficient of `X_i` in the fundamental cycle `[X]_{n + r}`.

The identity is read coefficientwise at a point `x` of `X`, because the irreducible components
of a locally Noetherian scheme need not form a finite set: neither side is a finite sum of
cycles, and at a fixed point of `X` only finitely many components contribute. -/
@[stacks 0EPJ]
theorem flatPullback_meromorphicDivisor_eq_sum_components (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sY = sX) (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) {n : ℤ}
    (hY : schemeDeltaDimension C sY = (n : EInt)) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (s : L.presheaf.stalk (genericPoint Y)) (hs : s ≠ 0) (x : X) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    (flatPullback C sX sY f hbase r hf (n - 1)
        (meromorphicDivisorCycleOfInvertible C sY hY L s).val).1 x =
      ∑ᶠ W : irreducibleComponents X,
        (cycleAssociatedToClosedSubscheme C sX (𝟙 X) (n + (r : ℤ))).1 W.2.1.genericPoint *
          (letI : IsIntegral (integralComponentAt W.2.1.genericPoint).subscheme :=
             isIntegral_integralComponentAt _
           letI : IsLocallyNoetherian (integralComponentAt W.2.1.genericPoint).subscheme :=
             LocallyOfFiniteType.isLocallyNoetherian
               ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX)
           letI := isDominant_subschemeι_integralComponentAt_comp f W
           letI := isInvertible_presheaf_pullback L
             ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ f)
           (properPushforward C ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX) sX
             (integralComponentAt W.2.1.genericPoint).subschemeι rfl (n + (r : ℤ) - 1)
             (meromorphicDivisorCycleOfInvertible C
               ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX)
               (schemeDeltaDimension_integralComponentAt_comp C sX sY f hbase r hf hY W)
               ((Scheme.Modules.pullback
                 ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ f)).obj L)
               (genericStalkPullback
                 ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ f) L s)).val).1 x) := by
  classical
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  -- a coordinate of `s` at the image of `x`, in the sense of Stacks 02SF
  obtain ⟨a, ha⟩ := exists_isCoordinateAt (isTrivializedNear_of_isInvertible L (f.base x)) s
  have ha0 : a ≠ 0 := ha.ne_zero hs
  -- the identity for the rational function `a`, Stacks 0EPH
  have hEPH := flatPullback_principalDivisor_eq_sum_components C sX sY f hbase r hf hY a ha0 x
  -- the left hand sides agree, since `a` is a coordinate of `s` at `f x`
  have hleft : (flatPullback C sX sY f hbase r hf (n - 1)
        (meromorphicDivisorCycleOfInvertible C sY hY L s).val).1 x =
      (flatPullback C sX sY f hbase r hf (n - 1) (principalDivisorCycle C sY hY a)).1 x := by
    rw [flatPullback_apply, flatPullback_apply,
      meromorphicDivisorCycle_apply_eq_principalDivisorCycle_apply C sY hY L s ha]
  rw [hleft, hEPH]
  -- and the right hand sides agree component by component
  refine finsum_congr fun W ↦ ?_
  let : IsIntegral (integralComponentAt W.2.1.genericPoint).subscheme :=
    isIntegral_integralComponentAt _
  let : IsLocallyNoetherian (integralComponentAt W.2.1.genericPoint).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX)
  let := isDominant_subschemeι_integralComponentAt_comp f W
  let := isInvertible_presheaf_pullback L
    ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ f)
  congr 1
  by_cases hmem : x ∈ Set.range (integralComponentAt W.2.1.genericPoint).subschemeι.base
  · obtain ⟨z, hz⟩ := hmem
    have hbz : ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ f).base z = f.base x := by
      change f.base ((integralComponentAt W.2.1.genericPoint).subschemeι.base z) = f.base x
      rw [hz]
    have ha' : IsCoordinateAt L
        (((integralComponentAt W.2.1.genericPoint).subschemeι ≫ f).base z) s a := by
      rw [hbz]; exact ha
    rw [← hz, properPushforward_apply_image_of_isClosedImmersion,
      properPushforward_apply_image_of_isClosedImmersion]
    exact (meromorphicDivisorCycle_apply_eq_principalDivisorCycle_apply C
      ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX)
      (schemeDeltaDimension_integralComponentAt_comp C sX sY f hbase r hf hY W) _ _
      ha'.pullback).symm
  · rw [properPushforward_apply_of_notMem_range C _ sX _ rfl _ _ hmem,
      properPushforward_apply_of_notMem_range C _ sX _ rfl _ _ hmem]

end Stacks.Chow

end
