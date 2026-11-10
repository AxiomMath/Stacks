module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.DivisorCycle
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionPullback
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPullback

/-!
# Proper pushforward of the divisor of a pulled-back meromorphic section

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
integral and locally of finite type over `S` with `dim_δ(X) = dim_δ(Y) = n`, let `p : X ⟶ Y` be
a proper dominant morphism over `S`, let `L` be an `𝒪_Y`-module of rank one and let `s` be a
nonzero meromorphic section of `L`. Then

  `p_*(div_{p^*L}(p^*s)) = [R(X) : R(Y)] div_L(s)`.

This is the first displayed equation of
[Stacks, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST).

## The argument

The source says "since we are trying to prove an equality of cycles, we may work locally on `Y`.
Hence we may assume `L = 𝒪_Y`". The reduction carried out here is pointwise rather than local,
and needs no restriction of `L` to an open set: fix a point `y` of `Y` and a coordinate
`a ∈ R(Y)` of `s` at `y`, that is, a rational function with `s = a · m` for a basis `m` of the
stalk `L_y` (`Stacks.Divisors.exists_isCoordinateAt`). Then

* for **every** point `x` of `X` above `y`, the pullback of `m` is a basis of `(p^*L)_x` and the
  image of `a` in `R(X)` is a coordinate of `p^*s` there
  (`Stacks.Divisors.IsCoordinateAt.pullback`), so the coefficient of `div_{p^*L}(p^*s)` at `x`
  is the order of vanishing of that image — the coefficient of `div_X(a)` at `x`;
* the coefficient of the proper pushforward at `y` depends only on the coefficients above `y`
  (`Stacks.Chow.properPushforward_apply`), so the two pushforwards agree at `y`;
* the coefficient of `p_*(div_X(a))` at `y` is `[R(X) : R(Y)]` times that of `div_Y(a)`, which is
  `Stacks.Chow.properPushforward_principalDivisorCycle_algebraMap`, the case `L = 𝒪_Y` of the
  tag;
* and the coefficient of `div_L(s)` at `y` is the order of vanishing of `a` at `y`
  (`Stacks.Divisors.orderOfVanishing_eq`), or zero when `y` is no prime divisor's generic point,
  in which case the order of vanishing of `a` vanishes too.

## Main results

* `Stacks.Chow.properPushforward_meromorphicDivisorCycle` — the displayed equation.
* `Stacks.Chow.properPushforward_meromorphicDivisorCycleOfInvertible` — the same for an
  invertible `L`, the rank-one hypothesis discharged.

## Where the rest of the tag is

Tag 02ST has a second displayed equation, the consequence
`f_*(c_1(f^*L) ∩ [X]) = [R(X) : R(Y)] c_1(L) ∩ [Y] = c_1(L) ∩ f_*[X]` for the first Chern class
cap product. It is not in this file but it is in this library, as
`Stacks.Chow.properChowPushforward_firstChernClassCapOfInvertible_fundamentalCycle` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDominantPushforward`, which carries
`@[stacks 02ST "second displayed equation"]`; it sits in its own module because its third member
needs `f_*[X] = [R(X) : R(Y)] [Y]`, and hence the identification of the degree of an extension of
function fields with the residue degree of Stacks 02R4, which lives downstream of this file. So
the attribute on `Stacks.Chow.properPushforward_meromorphicDivisorCycleOfInvertible` is the
sub-labelled `@[stacks 02ST "first displayed equation"]`, naming the clause of the tag's covering
set that is proved here.

## What this is not

The rank-one hypothesis on `L` is `Stacks.Divisors.IsTrivializedNear` at every point, as
throughout `StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder`; that generalizes the source,
which asks `L` to be invertible. A meromorphic section is an element of the generic stalk `L_η`,
the model of `StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder`; the identification of that
model with a global section of `𝒦_Y(L)` is Stacks 01X5 (2), which this library does not have.
The local Noetherianity of `X` and `Y` is an instance hypothesis only because
`Stacks.Divisors.orderOfVanishing` is stated under it; it follows from the other hypotheses by
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`.

## References

* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-- **The first displayed equation of Stacks 02ST.** For a proper dominant morphism
`p : X ⟶ Y` of integral schemes locally of finite type over the base with
`dim_δ(X) = dim_δ(Y) = n`, a rank-one `𝒪_Y`-module `L` and a nonzero meromorphic section `s` of
`L`, the proper pushforward of the divisor cycle of `p^*s` is `[R(X) : R(Y)]` times the divisor
cycle of `s`.

The rank-one hypothesis generalizes the source, which asks `L` to be invertible, so the Stacks
attribute sits on `Stacks.Chow.properPushforward_meromorphicDivisorCycleOfInvertible` rather than
here. -/
theorem properPushforward_meromorphicDivisorCycle (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] {n : ℤ}
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hnY : schemeDeltaDimension C sY = (n : EInt))
    (p : X ⟶ Y) [IsProper p] [IsDominant p] (hp : p ≫ sY = sX)
    {L : Y.Modules} (hL : ∀ y : Y, IsTrivializedNear L y)
    (s : L.presheaf.stalk (genericPoint Y)) (hs : s ≠ 0) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap p).toAlgebra
    properPushforward C sX sY p hp (n - 1)
        (meromorphicDivisorCycle C sX hnX
          (fun x => (hL (p.base x)).pullback) (genericStalkPullback p L s)).val =
      (Module.finrank Y.functionField X.functionField : ℤ) •
        (meromorphicDivisorCycle C sY hnY hL s).val := by
  classical
  let _ : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap p).toAlgebra
  have halg : algebraMap Y.functionField X.functionField = dominantFunctionFieldMap p :=
    RingHom.algebraMap_toAlgebra _
  set hL' : ∀ x : X, IsTrivializedNear ((Scheme.Modules.pullback p).obj L) x :=
    fun x => (hL (p.base x)).pullback
  change properPushforward C sX sY p hp (n - 1)
      (meromorphicDivisorCycle C sX hnX hL' (genericStalkPullback p L s)).val =
    (Module.finrank Y.functionField X.functionField : ℤ) •
      (meromorphicDivisorCycle C sY hnY hL s).val
  apply Subtype.ext
  ext y
  -- a coordinate of `s` at `y`, which the whole fibre above `y` will use
  obtain ⟨a, ha⟩ := exists_isCoordinateAt (hL y) s
  have ha0 : a ≠ 0 := ha.ne_zero hs
  -- the two cycles on `X` have the same coefficient at every point above `y`
  have hfib : ∀ x : X, p.base x = y →
      ((meromorphicDivisorCycle C sX hnX hL' (genericStalkPullback p L s)).val :
          AlgebraicCycle X ℤ) x =
        ((principalDivisorCycle C sX hnX
          (algebraMap Y.functionField X.functionField a) : CycleGroup C sX (n - 1)) :
          AlgebraicCycle X ℤ) x := by
    intro x hxy
    subst hxy
    rw [principalDivisorCycle_apply]
    by_cases hx : ∃ Z : PrimeDivisor X, Z.genericPoint = x
    · obtain ⟨Z, rfl⟩ := hx
      rw [meromorphicDivisorCycle_genericPoint]
      refine orderOfVanishing_eq (hL' Z.genericPoint) ?_
      rw [halg]
      exact ha.pullback
    · have hne : ∀ Z : PrimeDivisor X, Z.genericPoint ≠ x := fun Z hZ => hx ⟨Z, hZ⟩
      have hcoh : coheight x ≠ 1 := fun h =>
        hne (PrimeDivisor.ofCoheightOne x h) (PrimeDivisor.genericPoint_ofCoheightOne x h)
      rw [meromorphicDivisorCycle_eq_zero C sX hnX hL' _ x hne,
        X.ord_eq_zero_of_coheight_neq_one hcoh]
  -- so the two pushforwards agree at `y`
  have hpush : (properPushforward C sX sY p hp (n - 1)
        (meromorphicDivisorCycle C sX hnX hL' (genericStalkPullback p L s)).val).val y =
      (properPushforward C sX sY p hp (n - 1)
        (principalDivisorCycle C sX hnX
          (algebraMap Y.functionField X.functionField a))).val y := by
    rw [properPushforward_apply, properPushforward_apply]
    exact finsum_congr fun x => finsum_congr fun hx => by
      rw [hfib x (by simpa using hx)]
  rw [hpush]
  have hnorm : (properPushforward C sX sY p hp (n - 1)
      (principalDivisorCycle C sX hnX (algebraMap Y.functionField X.functionField a)) :
        CycleGroup C sY (n - 1)) =
      (Module.finrank Y.functionField X.functionField : ℤ) • principalDivisorCycle C sY hnY a :=
    properPushforward_principalDivisorCycle_algebraMap C sX sY hnX hnY p hp a ha0
  rw [hnorm]
  -- the remaining comparison is the coefficient of `div_L(s)` against that of `div_Y(a)`
  have hcoeff : ((principalDivisorCycle C sY hnY a : CycleGroup C sY (n - 1)) :
        AlgebraicCycle Y ℤ) y =
      ((meromorphicDivisorCycle C sY hnY hL s).val : AlgebraicCycle Y ℤ) y := by
    rw [principalDivisorCycle_apply]
    by_cases hy : ∃ Z : PrimeDivisor Y, Z.genericPoint = y
    · obtain ⟨Z, rfl⟩ := hy
      rw [meromorphicDivisorCycle_genericPoint, orderOfVanishing_eq (hL Z.genericPoint) ha]
    · have hne : ∀ Z : PrimeDivisor Y, Z.genericPoint ≠ y := fun Z hZ => hy ⟨Z, hZ⟩
      have hcoh : coheight y ≠ 1 := fun h =>
        hne (PrimeDivisor.ofCoheightOne y h) (PrimeDivisor.genericPoint_ofCoheightOne y h)
      rw [meromorphicDivisorCycle_eq_zero C sY hnY hL s y hne,
        Y.ord_eq_zero_of_coheight_neq_one hcoh]
  simp [hcoeff]

/-- **The first displayed equation of Stacks 02ST.** For a proper dominant morphism `p : X ⟶ Y`
of integral schemes locally of finite type over the base with `dim_δ(X) = dim_δ(Y) = n`, an
invertible `𝒪_Y`-module `L` and a nonzero meromorphic section `s` of `L`, the proper pushforward
of the divisor cycle of `p^*s` is `[R(X) : R(Y)]` times the divisor cycle of `s`, as cycles.

These are the hypotheses the source states the tag under; the rank-one hypothesis of
`Stacks.Chow.properPushforward_meromorphicDivisorCycle` is discharged here by
`Stacks.Divisors.isTrivializedNear_of_isInvertible`. The tag's second displayed equation, the
first Chern class consequence, is in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDominantPushforward`, so the attribute names this
clause explicitly; see the module documentation. -/
@[stacks 02ST "first displayed equation"]
theorem properPushforward_meromorphicDivisorCycleOfInvertible (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] {n : ℤ}
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hnY : schemeDeltaDimension C sY = (n : EInt))
    (p : X ⟶ Y) [IsProper p] [IsDominant p] (hp : p ≫ sY = sX) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (s : L.presheaf.stalk (genericPoint Y)) (hs : s ≠ 0) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap p).toAlgebra
    properPushforward C sX sY p hp (n - 1)
        (meromorphicDivisorCycle C sX hnX
          (fun x => (isTrivializedNear_of_isInvertible L (p.base x)).pullback)
          (genericStalkPullback p L s)).val =
      (Module.finrank Y.functionField X.functionField : ℤ) •
        (meromorphicDivisorCycle C sY hnY (isTrivializedNear_of_isInvertible L) s).val :=
  properPushforward_meromorphicDivisorCycle C sX sY hnX hnY p hp
    (isTrivializedNear_of_isInvertible L) s hs

end Stacks.Chow

end
