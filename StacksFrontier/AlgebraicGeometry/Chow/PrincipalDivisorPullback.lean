module

public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Proper pushforward of the principal divisor of a pulled-back rational function

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
integral and locally of finite type over `S` with `dim_δ(X) = dim_δ(Y) = n`, and let `p : X ⟶ Y`
be a proper dominant morphism over `S`. For a nonzero rational function `g` on `Y`, pulled back
to `X` along the induced extension `R(Y) ⊆ R(X)` of function fields,

  `p_*(div_X(g)) = [R(X) : R(Y)] div_Y(g)`.

This is the displayed equation in the proof of
[Stacks, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST), that is, Tag 02ST in the case
`L = 𝒪_Y`, where a meromorphic section of `L` is a rational function. It follows from Tag 02RT,
`Stacks.Chow.properPushforward_principalDivisorCycle`, together with the identity
`Nm_{R(X)/R(Y)}(g) = g^{[R(X) : R(Y)]}` for `g ∈ R(Y)^*`, which is Mathlib's
`Algebra.norm_algebraMap`, and the additivity of the principal divisor in the function.

## Main results

* `AlgebraicGeometry.Scheme.ord_pow` — the order of vanishing of a power.
* `Stacks.Chow.principalDivisorCycle_pow` — `div(g^m) = m · div(g)`.
* `Stacks.Chow.properPushforward_principalDivisorCycle_algebraMap` — the displayed equation
  above.

## What this is not

No declaration here carries the `@[stacks 02ST]` attribute, and this is **not** Tag 02ST. The
tag states the identity

  `p_*(div_{p^*L}(p^*s)) = [R(X) : R(Y)] div_L(s)`

for an arbitrary invertible module `L` on `Y` and a nonzero meromorphic section `s` of `L`,
together with its consequence for the first Chern class cap product. Two things stand between
this file and that statement, and neither is here:

* the pullback `p^*s` of a meromorphic section. In the generic-stalk model used throughout
  `StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder` a meromorphic section of `L` is an
  element of the stalk `L_η` at the generic point, and no map
  `L_{η_Y} → (p^*L)_{η_X}` is defined anywhere in this repository. The ingredients for it are
  `AlgebraicGeometry.pullbackUnitSections` and its naturality in the open,
  `AlgebraicGeometry.pullbackUnitSections_naturality`, in
  `StacksDraft.AlgebraicGeometry.F3b.PullbackSections.Qcqs`;
* the identification of coordinates. `Stacks.Divisors.orderOfVanishing` reads
  `ord_{Z, L}(s)` through a basis of the stalk `L_ξ` at the generic point of `Z` and the
  coordinate of `s` in it (`Stacks.Divisors.IsCoordinateAt`). Reducing Tag 02ST to the equation
  of this file at each point `y` of `Y` amounts to: a basis `m` of `L_y` pulls back to a basis
  of `(p^*L)_x` for every `x` above `y`, and the coordinate of `p^*s` in it is the image of the
  coordinate of `s` in `m` under `R(Y) → R(X)`.

With those two in place the reduction is pointwise and needs no locality argument on `Y`: for
each `y` one basis of `L_y` serves the whole fibre `p^{-1}(y)`, and the equation below applies to
the single rational function it produces.

## References

* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 02RP](https://stacks.math.columbia.edu/tag/02RP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The order of vanishing of a power of a nonzero rational function is the multiple of its
order of vanishing, the companion of `AlgebraicGeometry.Scheme.ord_mul`. -/
theorem ord_pow {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {g : X.functionField} (hg : g ≠ 0) (m : ℕ) (x : X) :
    X.ord (g ^ m) x = m * X.ord g x := by
  induction m with
  | zero =>
    have h := X.ord_mul (x := x) (f := 1) (g := 1)
      (one_ne_zero (α := X.functionField)) (one_ne_zero (α := X.functionField))
    rw [one_mul] at h
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    omega
  | succ m ih =>
    rw [pow_succ, X.ord_mul (pow_ne_zero m hg) hg, ih]
    push_cast
    ring

end AlgebraicGeometry.Scheme

namespace Stacks.Chow

/-- **Stacks 02RP for a power.** The principal divisor of a power of a nonzero rational function
on an integral scheme of delta-dimension `n` is the corresponding multiple of its principal
divisor. -/
theorem principalDivisorCycle_pow (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] [IsIntegral X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) {g : X.functionField} (hg : g ≠ 0) (m : ℕ) :
    principalDivisorCycle C p hn (g ^ m) = (m : ℤ) • principalDivisorCycle C p hn g := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  change (principalDivisorCycle C p hn (g ^ m) : AlgebraicCycle X ℤ) z =
    (((m : ℤ) • principalDivisorCycle C p hn g : CycleGroup C p (n - 1)) : AlgebraicCycle X ℤ) z
  rw [principalDivisorCycle_apply C p hn (g ^ m) z, X.ord_pow hg m z]
  simp [principalDivisorCycle_apply C p hn g z]

/-- **Stacks 02ST in the case `L = 𝒪_Y`**, which is the displayed equation in the proof of that
tag. For a proper dominant morphism `p : X ⟶ Y` of integral schemes locally of finite type over
the base with `dim_δ(X) = dim_δ(Y) = n`, and a nonzero rational function `g` on `Y`, the proper
pushforward of the principal divisor of `g` read on `X` is `[R(X) : R(Y)]` times the principal
divisor of `g`.

This is Stacks 02RT, `Stacks.Chow.properPushforward_principalDivisorCycle`, applied to the image
of `g` under the extension `R(Y) ⊆ R(X)` of function fields, whose norm is `g^{[R(X) : R(Y)]}`.

No Stacks attribute is attached; see the module documentation. -/
@[ega "IV 21.10.19" "special case"]
theorem properPushforward_principalDivisorCycle_algebraMap (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] [IsIntegral X] [IsIntegral Y] {n : ℤ}
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hnY : schemeDeltaDimension C sY = (n : EInt))
    (p : X ⟶ Y) [IsProper p] [IsDominant p] (hp : p ≫ sY = sX)
    (g : Y.functionField) (hg : g ≠ 0) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap p).toAlgebra
    properPushforward C sX sY p hp (n - 1)
        (principalDivisorCycle C sX hnX (algebraMap Y.functionField X.functionField g)) =
      (Module.finrank Y.functionField X.functionField : ℤ) • principalDivisorCycle C sY hnY g := by
  let _ : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap p).toAlgebra
  have hga : algebraMap Y.functionField X.functionField g ≠ 0 :=
    fun h ↦ hg ((map_eq_zero_iff _ (algebraMap Y.functionField X.functionField).injective).1 h)
  change properPushforward C sX sY p hp (n - 1)
      (principalDivisorCycle C sX hnX (algebraMap Y.functionField X.functionField g)) =
    (Module.finrank Y.functionField X.functionField : ℤ) • principalDivisorCycle C sY hnY g
  rw [properPushforward_principalDivisorCycle C sX sY hnX hnY p hp _ hga,
    Algebra.norm_algebraMap, principalDivisorCycle_pow C sY hnY hg]

end Stacks.Chow

end
