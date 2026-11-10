module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.RestrictedPowerSeries.CoefficientIdeal

/-!
# Iterating the restricted power series construction

Let `I` be a finitely generated ideal of a commutative ring `A`.  The restricted power series
ring `A{τ ⊕ σ}` in two groups of variables is the restricted power series ring in the variables
`τ` over `A{σ}`, taken for the extended coefficient ideal `I · A{σ}`; in the notation of the
source, `A{x₁, …, x_n} = A{x₁, …, x_{n-1}}{x_n}`.  Both sides are inverse limits of polynomial
rings over coefficient quotients, and at level `n` the comparison is the rearrangement
`(A ⧸ Iⁿ)[τ ⊕ σ] ≅ ((A ⧸ Iⁿ)[σ])[τ]` followed by the identification of `(A ⧸ Iⁿ)[σ]` with
`A{σ} ⧸ (I · A{σ})ⁿ`.

## Main definitions

* `RestrictedPowerSeries.iteratedLevelEquiv`: the level `n` comparison
  `(A ⧸ Iⁿ)[τ ⊕ σ] ≃+* (A{σ} ⧸ (I · A{σ})ⁿ)[τ]`.
* `RestrictedPowerSeries.iteratedEquiv`: the ring isomorphism `A{τ ⊕ σ} ≃+* A{σ}{τ}`.

## Main results

* `RestrictedPowerSeries.coefficientProjection_iteratedEquiv`: the isomorphism is computed at
  every level by the level comparison.
* `RestrictedPowerSeries.iteratedEquiv_coefficientRingHom`,
  `RestrictedPowerSeries.iteratedEquiv_polynomialRingHom_X_inl` and
  `RestrictedPowerSeries.iteratedEquiv_polynomialRingHom_X_inr`: the isomorphism is the
  canonical map on constants and sends each variable to the corresponding variable, which pins
  it down on the image of the polynomial ring.

## Implementation notes

The identification `A{σ} ⧸ (I · A{σ})ⁿ ≅ (A ⧸ Iⁿ)[σ]` of
`RestrictedPowerSeries.quotientCoefficientIdealPowEquiv` needs `I` to be finitely generated, so
that hypothesis is carried throughout.  The isomorphism is assembled levelwise rather than
transported through the comparison of `A{σ}` with the adic completion of a polynomial ring,
which keeps the coefficient ring of the outer construction equal to `A{σ}` on the nose.

## References

* [Stacks Project, Tag 0AJM](https://stacks.math.columbia.edu/tag/0AJM)
* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
-/

@[expose] public section

namespace RestrictedPowerSeries

section

universe u v w

/-- The transition maps between coefficient-quotient polynomial rings reduce a constant
coefficientwise. -/
private theorem coefficientTransition_C {R : Type w} [CommRing R] (I : Ideal R) (σ : Type v)
    {m n : ℕ} (hmn : m ≤ n) (a : R ⧸ I ^ n) :
    coefficientTransition I σ hmn (MvPolynomial.C a) =
      MvPolynomial.C (Ideal.Quotient.factorPow I hmn a) :=
  MvPolynomial.map_C (Ideal.Quotient.factorPow I hmn) a

/-- The transition maps between coefficient-quotient polynomial rings fix the variables. -/
private theorem coefficientTransition_X {R : Type w} [CommRing R] (I : Ideal R) (σ : Type v)
    {m n : ℕ} (hmn : m ≤ n) (i : σ) :
    coefficientTransition I σ hmn (MvPolynomial.X i) = MvPolynomial.X i :=
  MvPolynomial.map_X (Ideal.Quotient.factorPow I hmn) i

variable {A : Type u} [CommRing A]

/-- The identifications of the finite quotients of `A{σ}` with polynomial rings over the
coefficient quotients of `A` are compatible with the transition maps. -/
public theorem coefficientTransition_quotientCoefficientIdealPowEquiv (I : Ideal A) (hI : I.FG)
    (σ : Type v) {m n : ℕ} (hmn : m ≤ n)
    (x : RestrictedPowerSeries I σ ⧸ (coefficientIdeal I σ) ^ n) :
    coefficientTransition I σ hmn (quotientCoefficientIdealPowEquiv I hI σ n x) =
      quotientCoefficientIdealPowEquiv I hI σ m
        (Ideal.Quotient.factorPow (coefficientIdeal I σ) hmn x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  change coefficientTransition I σ hmn (coefficientProjection I σ n f) = _
  exact f.property hmn

/-- The inverses of the identifications of the finite quotients of `A{σ}` are compatible with
the transition maps. -/
private theorem factorPow_quotientCoefficientIdealPowEquiv_symm (I : Ideal A) (hI : I.FG)
    (σ : Type v) {m n : ℕ} (hmn : m ≤ n) (p : MvPolynomial σ (A ⧸ I ^ n)) :
    Ideal.Quotient.factorPow (coefficientIdeal I σ) hmn
        ((quotientCoefficientIdealPowEquiv I hI σ n).symm p) =
      (quotientCoefficientIdealPowEquiv I hI σ m).symm
        (coefficientTransition I σ hmn p) := by
  refine ((quotientCoefficientIdealPowEquiv I hI σ m).eq_symm_apply).mpr ?_
  rw [← coefficientTransition_quotientCoefficientIdealPowEquiv I hI σ hmn,
    RingEquiv.apply_symm_apply]

/-- The level `n` comparison `(A ⧸ Iⁿ)[τ ⊕ σ] ≃+* (A{σ} ⧸ (I · A{σ})ⁿ)[τ]`: rearrange the two
groups of variables, then read the inner polynomial ring as a finite quotient of `A{σ}`. -/
@[ega "0 7.5.2" "partial"]
public noncomputable def iteratedLevelEquiv (I : Ideal A) (hI : I.FG) (σ τ : Type v) (n : ℕ) :
    MvPolynomial (τ ⊕ σ) (A ⧸ I ^ n) ≃+*
      MvPolynomial τ (RestrictedPowerSeries I σ ⧸ (coefficientIdeal I σ) ^ n) :=
  (MvPolynomial.sumRingEquiv (A ⧸ I ^ n) τ σ).trans
    (MvPolynomial.mapEquiv τ (quotientCoefficientIdealPowEquiv I hI σ n).symm)

/-- On a constant the level comparison is the identification of the finite quotients. -/
@[simp]
public theorem iteratedLevelEquiv_C (I : Ideal A) (hI : I.FG) (σ τ : Type v) (n : ℕ)
    (a : A ⧸ I ^ n) :
    iteratedLevelEquiv I hI σ τ n (MvPolynomial.C a) =
      MvPolynomial.C ((quotientCoefficientIdealPowEquiv I hI σ n).symm (MvPolynomial.C a)) := by
  simp only [iteratedLevelEquiv, RingEquiv.trans_apply, MvPolynomial.mapEquiv_apply,
    MvPolynomial.sumRingEquiv_C, MvPolynomial.map_C]
  rfl

/-- The level comparison sends an outer variable to the corresponding variable. -/
@[simp]
public theorem iteratedLevelEquiv_X_inl (I : Ideal A) (hI : I.FG) (σ τ : Type v) (n : ℕ)
    (j : τ) :
    iteratedLevelEquiv I hI σ τ n (MvPolynomial.X (Sum.inl j)) = MvPolynomial.X j := by
  simp only [iteratedLevelEquiv, RingEquiv.trans_apply, MvPolynomial.mapEquiv_apply,
    MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.map_X]

/-- The level comparison sends an inner variable to the corresponding constant. -/
@[simp]
public theorem iteratedLevelEquiv_X_inr (I : Ideal A) (hI : I.FG) (σ τ : Type v) (n : ℕ)
    (i : σ) :
    iteratedLevelEquiv I hI σ τ n (MvPolynomial.X (Sum.inr i)) =
      MvPolynomial.C ((quotientCoefficientIdealPowEquiv I hI σ n).symm (MvPolynomial.X i)) := by
  simp only [iteratedLevelEquiv, RingEquiv.trans_apply, MvPolynomial.mapEquiv_apply,
    MvPolynomial.sumRingEquiv_X_inr, MvPolynomial.map_C]
  rfl

/-- The level comparisons are compatible with the transition maps of the two inverse limits. -/
public theorem iteratedLevelEquiv_transition (I : Ideal A) (hI : I.FG) (σ τ : Type v)
    {m n : ℕ} (hmn : m ≤ n) (p : MvPolynomial (τ ⊕ σ) (A ⧸ I ^ n)) :
    coefficientTransition (coefficientIdeal I σ) τ hmn (iteratedLevelEquiv I hI σ τ n p) =
      iteratedLevelEquiv I hI σ τ m (coefficientTransition I (τ ⊕ σ) hmn p) := by
  have h : (coefficientTransition (coefficientIdeal I σ) τ hmn).comp
        (iteratedLevelEquiv I hI σ τ n).toRingHom =
      (iteratedLevelEquiv I hI σ τ m).toRingHom.comp
        (coefficientTransition I (τ ⊕ σ) hmn) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, iteratedLevelEquiv_C, coefficientTransition_C,
        factorPow_quotientCoefficientIdealPowEquiv_symm]
    · obtain j | i := i
      · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, iteratedLevelEquiv_X_inl, coefficientTransition_X]
      · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, iteratedLevelEquiv_X_inr, coefficientTransition_C,
          coefficientTransition_X, factorPow_quotientCoefficientIdealPowEquiv_symm]
  exact DFunLike.congr_fun h p

/-- The inverses of the level comparisons are compatible with the transition maps. -/
private theorem iteratedLevelEquiv_symm_transition (I : Ideal A) (hI : I.FG) (σ τ : Type v)
    {m n : ℕ} (hmn : m ≤ n)
    (q : MvPolynomial τ (RestrictedPowerSeries I σ ⧸ (coefficientIdeal I σ) ^ n)) :
    coefficientTransition I (τ ⊕ σ) hmn ((iteratedLevelEquiv I hI σ τ n).symm q) =
      (iteratedLevelEquiv I hI σ τ m).symm
        (coefficientTransition (coefficientIdeal I σ) τ hmn q) := by
  refine ((iteratedLevelEquiv I hI σ τ m).eq_symm_apply).mpr ?_
  rw [← iteratedLevelEquiv_transition I hI σ τ hmn, RingEquiv.apply_symm_apply]

/-- **`A{x₁, …, x_n} = A{x₁, …, x_{n-1}}{x_n}`.**  For a finitely generated ideal `I` of `A`, the
restricted power series ring over `A` in two groups of variables is the restricted power series
ring in the outer group over the restricted power series ring in the inner group, taken for the
extended coefficient ideal. -/
@[ega "0 7.5.2" "special case"]
public noncomputable def iteratedEquiv (I : Ideal A) (hI : I.FG) (σ τ : Type v) :
    RestrictedPowerSeries I (τ ⊕ σ) ≃+* RestrictedPowerSeries (coefficientIdeal I σ) τ where
  toFun x :=
    ⟨fun n => iteratedLevelEquiv I hI σ τ n (coefficientProjection I (τ ⊕ σ) n x), by
      intro m n hmn
      change coefficientTransition (coefficientIdeal I σ) τ hmn
        (iteratedLevelEquiv I hI σ τ n (coefficientProjection I (τ ⊕ σ) n x)) = _
      rw [iteratedLevelEquiv_transition I hI σ τ hmn]
      exact congrArg (iteratedLevelEquiv I hI σ τ m) (x.property hmn)⟩
  invFun y :=
    ⟨fun n => (iteratedLevelEquiv I hI σ τ n).symm
        (coefficientProjection (coefficientIdeal I σ) τ n y), by
      intro m n hmn
      change coefficientTransition I (τ ⊕ σ) hmn ((iteratedLevelEquiv I hI σ τ n).symm
        (coefficientProjection (coefficientIdeal I σ) τ n y)) = _
      rw [iteratedLevelEquiv_symm_transition I hI σ τ hmn]
      exact congrArg (iteratedLevelEquiv I hI σ τ m).symm (y.property hmn)⟩
  left_inv x := by
    refine Subtype.ext (funext fun n => ?_)
    change (iteratedLevelEquiv I hI σ τ n).symm
      (iteratedLevelEquiv I hI σ τ n (coefficientProjection I (τ ⊕ σ) n x)) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  right_inv y := by
    refine Subtype.ext (funext fun n => ?_)
    change iteratedLevelEquiv I hI σ τ n ((iteratedLevelEquiv I hI σ τ n).symm
      (coefficientProjection (coefficientIdeal I σ) τ n y)) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  map_mul' x y := by
    refine Subtype.ext (funext fun n => ?_)
    exact ((iteratedLevelEquiv I hI σ τ n).toRingHom.comp
      (coefficientProjection I (τ ⊕ σ) n)).map_mul x y
  map_add' x y := by
    refine Subtype.ext (funext fun n => ?_)
    exact ((iteratedLevelEquiv I hI σ τ n).toRingHom.comp
      (coefficientProjection I (τ ⊕ σ) n)).map_add x y

/-- The isomorphism `A{τ ⊕ σ} ≃+* A{σ}{τ}` is computed at every level by the level
comparison. -/
@[simp, ega "0 7.5.2" "partial"]
public theorem coefficientProjection_iteratedEquiv (I : Ideal A) (hI : I.FG) (σ τ : Type v)
    (n : ℕ) (x : RestrictedPowerSeries I (τ ⊕ σ)) :
    coefficientProjection (coefficientIdeal I σ) τ n (iteratedEquiv I hI σ τ x) =
      iteratedLevelEquiv I hI σ τ n (coefficientProjection I (τ ⊕ σ) n x) := rfl

/-- Two elements of `A{σ}{τ}` agree if they do after the level comparison at every level. -/
private theorem iteratedEquiv_eq_of_levels (I : Ideal A) (hI : I.FG) (σ τ : Type v)
    {x : RestrictedPowerSeries I (τ ⊕ σ)} {y : RestrictedPowerSeries (coefficientIdeal I σ) τ}
    (h : ∀ n, iteratedLevelEquiv I hI σ τ n (coefficientProjection I (τ ⊕ σ) n x) =
      coefficientProjection (coefficientIdeal I σ) τ n y) : iteratedEquiv I hI σ τ x = y :=
  Subtype.ext (funext h)

/-- The isomorphism `A{τ ⊕ σ} ≃+* A{σ}{τ}` is the canonical map on constants. -/
@[simp]
public theorem iteratedEquiv_coefficientRingHom (I : Ideal A) (hI : I.FG) (σ τ : Type v)
    (a : A) :
    iteratedEquiv I hI σ τ (coefficientRingHom I (τ ⊕ σ) a) =
      coefficientRingHom (coefficientIdeal I σ) τ (coefficientRingHom I σ a) := by
  refine iteratedEquiv_eq_of_levels I hI σ τ fun n => ?_
  change iteratedLevelEquiv I hI σ τ n
      (coefficientProjection I (τ ⊕ σ) n
        (algebraMap A (RestrictedPowerSeries I (τ ⊕ σ)) a)) =
    coefficientProjection (coefficientIdeal I σ) τ n
      (algebraMap (RestrictedPowerSeries I σ)
        (RestrictedPowerSeries (coefficientIdeal I σ) τ) (coefficientRingHom I σ a))
  rw [coefficientProjection_algebraMap, coefficientProjection_algebraMap, iteratedLevelEquiv_C]
  congr 1
  refine ((quotientCoefficientIdealPowEquiv I hI σ n).symm_apply_eq).mpr ?_
  rw [quotientCoefficientIdealPowEquiv_mk]
  exact (coefficientProjection_algebraMap I σ n a).symm

/-- The isomorphism `A{τ ⊕ σ} ≃+* A{σ}{τ}` sends each outer variable to the corresponding
variable of `A{σ}{τ}`. -/
@[simp]
public theorem iteratedEquiv_polynomialRingHom_X_inl (I : Ideal A) (hI : I.FG) (σ τ : Type v)
    (j : τ) :
    iteratedEquiv I hI σ τ (polynomialRingHom I (τ ⊕ σ) (MvPolynomial.X (Sum.inl j))) =
      polynomialRingHom (coefficientIdeal I σ) τ (MvPolynomial.X j) := by
  refine iteratedEquiv_eq_of_levels I hI σ τ fun n => ?_
  rw [coefficientProjection_polynomialRingHom, coefficientProjection_polynomialRingHom,
    MvPolynomial.map_X, MvPolynomial.map_X, iteratedLevelEquiv_X_inl]

/-- The isomorphism `A{τ ⊕ σ} ≃+* A{σ}{τ}` sends each inner variable to the corresponding
variable of the coefficient ring `A{σ}`. -/
@[simp]
public theorem iteratedEquiv_polynomialRingHom_X_inr (I : Ideal A) (hI : I.FG) (σ τ : Type v)
    (i : σ) :
    iteratedEquiv I hI σ τ (polynomialRingHom I (τ ⊕ σ) (MvPolynomial.X (Sum.inr i))) =
      coefficientRingHom (coefficientIdeal I σ) τ (polynomialRingHom I σ (MvPolynomial.X i)) := by
  refine iteratedEquiv_eq_of_levels I hI σ τ fun n => ?_
  change iteratedLevelEquiv I hI σ τ n
      (coefficientProjection I (τ ⊕ σ) n
        (polynomialRingHom I (τ ⊕ σ) (MvPolynomial.X (Sum.inr i)))) =
    coefficientProjection (coefficientIdeal I σ) τ n
      (algebraMap (RestrictedPowerSeries I σ)
        (RestrictedPowerSeries (coefficientIdeal I σ) τ)
        (polynomialRingHom I σ (MvPolynomial.X i)))
  rw [coefficientProjection_polynomialRingHom, MvPolynomial.map_X,
    coefficientProjection_algebraMap, iteratedLevelEquiv_X_inr]
  congr 1
  refine ((quotientCoefficientIdealPowEquiv I hI σ n).symm_apply_eq).mpr ?_
  rw [quotientCoefficientIdealPowEquiv_mk, coefficientProjection_polynomialRingHom,
    MvPolynomial.map_X]

end

end RestrictedPowerSeries

end
