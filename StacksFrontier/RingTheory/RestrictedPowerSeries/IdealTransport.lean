module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.RestrictedPowerSeries

/-!
# Restricted power series for two presentations of the same coefficient ideal

The restricted power series ring `RestrictedPowerSeries I σ` is an inverse limit of polynomial
rings over the quotients `A ⧸ I ^ n`, so it depends on the *ideal* `I` and not merely on the
topology it defines: two equal ideals written differently give two types which are not
definitionally the same, and no statement about one is a statement about the other.

This module gives the canonical isomorphism between the rings for two equal ideals. It is built
levelwise, rewriting the coefficient quotient at each level, so `coefficientProjection` of a
transported series is the level rewrite of its `coefficientProjection`, and the transport of a
constant is the constant.

The ideal that needs rewriting in practice is an extension along a two-step tower: the fourth
paragraph of the proof of Stacks 0GGR needs `B_{\{f\}}{σ}` for the ideal extended from
`A_{\{f\}}`, whereas the identification `B{σ}_{\{f\}} = B_{\{f\}}{σ}` of Stacks 0GGG delivers
it for the ideal extended from `B` through `Localization.Away (φ f)`.

## Main definitions

* `RestrictedPowerSeries.congrLevelEquiv`: the level `n` rewrite
  `(A ⧸ I ^ n)[σ] ≃+* (A ⧸ J ^ n)[σ]` for `I = J`.
* `RestrictedPowerSeries.congrEquiv`: the ring isomorphism `A{σ} ≃+* A{σ}` comparing the two
  presentations of the coefficient ideal.

## Main results

* `RestrictedPowerSeries.coefficientProjection_congrEquiv`: the isomorphism is computed at
  every level by the level rewrite.
* `RestrictedPowerSeries.congrEquiv_coefficientRingHom` and
  `RestrictedPowerSeries.congrEquiv_polynomialRingHom`: it is the identity on constants and on
  polynomials.

## References

* [Stacks Project, Tag 0AJM](https://stacks.math.columbia.edu/tag/0AJM)
* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
-/

@[expose] public section

namespace RestrictedPowerSeries

section

universe u v

variable {A : Type u} [CommRing A]

/-- **The level `n` comparison of two presentations of one coefficient ideal.** Equal ideals
have equal powers, so their quotients are canonically isomorphic, and the isomorphism is applied
to the coefficients. -/
public noncomputable def congrLevelEquiv {I J : Ideal A} (h : I = J) (σ : Type v) (n : ℕ) :
    MvPolynomial σ (A ⧸ I ^ n) ≃+* MvPolynomial σ (A ⧸ J ^ n) :=
  MvPolynomial.mapEquiv σ (Ideal.quotEquivOfEq (congrArg (· ^ n) h))

/-- The rewrite of coefficient quotients is the canonical reduction on representatives. -/
private theorem quotEquivOfEq_comp_mk {I J : Ideal A} (h : I = J) (n : ℕ) :
    ((Ideal.quotEquivOfEq (congrArg (· ^ n) h) : A ⧸ I ^ n ≃+* A ⧸ J ^ n) :
          A ⧸ I ^ n →+* A ⧸ J ^ n).comp (Ideal.Quotient.mk (I ^ n)) =
      Ideal.Quotient.mk (J ^ n) :=
  RingHom.ext fun a => Ideal.quotEquivOfEq_mk (congrArg (· ^ n) h) a

/-- The level comparison rewrites a constant coefficientwise. -/
@[simp]
public theorem congrLevelEquiv_C {I J : Ideal A} (h : I = J) (σ : Type v) (n : ℕ) (a : A) :
    congrLevelEquiv h σ n (MvPolynomial.C (Ideal.Quotient.mk (I ^ n) a)) =
      MvPolynomial.C (Ideal.Quotient.mk (J ^ n) a) := by
  rw [congrLevelEquiv, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C]
  exact congrArg MvPolynomial.C (Ideal.quotEquivOfEq_mk _ a)

/-- The level comparison fixes the variables. -/
@[simp]
public theorem congrLevelEquiv_X {I J : Ideal A} (h : I = J) (σ : Type v) (n : ℕ) (i : σ) :
    congrLevelEquiv h σ n (MvPolynomial.X i) = MvPolynomial.X i := by
  rw [congrLevelEquiv, MvPolynomial.mapEquiv_apply, MvPolynomial.map_X]

/-- The level comparison is compatible with the transition maps of the two inverse limits. -/
public theorem congrLevelEquiv_transition {I J : Ideal A} (h : I = J) (σ : Type v)
    {m n : ℕ} (hmn : m ≤ n) (p : MvPolynomial σ (A ⧸ I ^ n)) :
    coefficientTransition J σ hmn (congrLevelEquiv h σ n p) =
      congrLevelEquiv h σ m (coefficientTransition I σ hmn p) := by
  have hcomp : (Ideal.Quotient.factorPow J hmn).comp
        (Ideal.quotEquivOfEq (congrArg (· ^ n) h)).toRingHom =
      (Ideal.quotEquivOfEq (congrArg (· ^ m) h)).toRingHom.comp
        (Ideal.Quotient.factorPow I hmn) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by
      show Ideal.Quotient.factorPow J hmn ((Ideal.quotEquivOfEq (congrArg (· ^ n) h))
          (Ideal.Quotient.mk (I ^ n) a)) =
        (Ideal.quotEquivOfEq (congrArg (· ^ m) h))
          (Ideal.Quotient.factorPow I hmn (Ideal.Quotient.mk (I ^ n) a))
      rw [Ideal.quotEquivOfEq_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
        Ideal.quotEquivOfEq_mk])
  show MvPolynomial.map (Ideal.Quotient.factorPow J hmn)
      (MvPolynomial.map (Ideal.quotEquivOfEq (congrArg (· ^ n) h)).toRingHom p) =
    MvPolynomial.map (Ideal.quotEquivOfEq (congrArg (· ^ m) h)).toRingHom
      (MvPolynomial.map (Ideal.Quotient.factorPow I hmn) p)
  rw [MvPolynomial.map_map, MvPolynomial.map_map, hcomp]

/-- The inverses of the level comparisons are compatible with the transition maps. -/
private theorem congrLevelEquiv_symm_transition {I J : Ideal A} (h : I = J) (σ : Type v)
    {m n : ℕ} (hmn : m ≤ n) (q : MvPolynomial σ (A ⧸ J ^ n)) :
    coefficientTransition I σ hmn ((congrLevelEquiv h σ n).symm q) =
      (congrLevelEquiv h σ m).symm (coefficientTransition J σ hmn q) := by
  refine ((congrLevelEquiv h σ m).eq_symm_apply).mpr ?_
  rw [← congrLevelEquiv_transition h σ hmn, RingEquiv.apply_symm_apply]

/-- **Restricted power series only depend on the coefficient ideal, not on how it is
written.** Two equal ideals of `A` give canonically isomorphic restricted power series rings:
at every level the coefficient quotients are rewritten, and the rewrites commute with the
transition maps of the two inverse limits. -/
public noncomputable def congrEquiv {I J : Ideal A} (h : I = J) (σ : Type v) :
    RestrictedPowerSeries I σ ≃+* RestrictedPowerSeries J σ where
  toFun x :=
    ⟨fun n => congrLevelEquiv h σ n (coefficientProjection I σ n x), by
      intro m n hmn
      change coefficientTransition J σ hmn
        (congrLevelEquiv h σ n (coefficientProjection I σ n x)) = _
      rw [congrLevelEquiv_transition h σ hmn]
      exact congrArg (congrLevelEquiv h σ m) (x.property hmn)⟩
  invFun y :=
    ⟨fun n => (congrLevelEquiv h σ n).symm (coefficientProjection J σ n y), by
      intro m n hmn
      change coefficientTransition I σ hmn
        ((congrLevelEquiv h σ n).symm (coefficientProjection J σ n y)) = _
      rw [congrLevelEquiv_symm_transition h σ hmn]
      exact congrArg (congrLevelEquiv h σ m).symm (y.property hmn)⟩
  left_inv x := Subtype.ext (funext fun n =>
    (congrLevelEquiv h σ n).symm_apply_apply (coefficientProjection I σ n x))
  right_inv y := Subtype.ext (funext fun n =>
    (congrLevelEquiv h σ n).apply_symm_apply (coefficientProjection J σ n y))
  map_mul' x y := Subtype.ext (funext fun n =>
    ((congrLevelEquiv h σ n).toRingHom.comp (coefficientProjection I σ n)).map_mul x y)
  map_add' x y := Subtype.ext (funext fun n =>
    ((congrLevelEquiv h σ n).toRingHom.comp (coefficientProjection I σ n)).map_add x y)

/-- The comparison isomorphism is computed at every level by the level rewrite. -/
@[simp]
public theorem coefficientProjection_congrEquiv {I J : Ideal A} (h : I = J) (σ : Type v)
    (n : ℕ) (x : RestrictedPowerSeries I σ) :
    coefficientProjection J σ n (congrEquiv h σ x) =
      congrLevelEquiv h σ n (coefficientProjection I σ n x) := rfl

/-- The comparison isomorphism is the canonical map on constants. -/
@[simp]
public theorem congrEquiv_coefficientRingHom {I J : Ideal A} (h : I = J) (σ : Type v) (a : A) :
    congrEquiv h σ (coefficientRingHom I σ a) = coefficientRingHom J σ a := by
  refine Subtype.ext (funext fun n => ?_)
  show congrLevelEquiv h σ n
      (coefficientProjection I σ n (algebraMap A (RestrictedPowerSeries I σ) a)) =
    coefficientProjection J σ n (algebraMap A (RestrictedPowerSeries J σ) a)
  rw [coefficientProjection_algebraMap, coefficientProjection_algebraMap, congrLevelEquiv_C]

/-- The comparison isomorphism is the canonical map on polynomials. -/
@[simp]
public theorem congrEquiv_polynomialRingHom {I J : Ideal A} (h : I = J) (σ : Type v)
    (p : MvPolynomial σ A) :
    congrEquiv h σ (polynomialRingHom I σ p) = polynomialRingHom J σ p := by
  refine Subtype.ext (funext fun n => ?_)
  show congrLevelEquiv h σ n (coefficientProjection I σ n (polynomialRingHom I σ p)) =
    coefficientProjection J σ n (polynomialRingHom J σ p)
  rw [coefficientProjection_polynomialRingHom, coefficientProjection_polynomialRingHom,
    congrLevelEquiv, MvPolynomial.mapEquiv_apply, MvPolynomial.map_map,
    quotEquivOfEq_comp_mk h n]

end

end RestrictedPowerSeries

end
