module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantCurveH1Trace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSheafCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicLFunction
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.RiemannHypothesis
public import StacksFrontier.AlgebraicGeometry.Picard.BaseChangeCurveTorsionFinite

/-!
# Tag 03V8: the L-function of the constant sheaf on a smooth projective curve

Let `X` be a smooth, projective, geometrically irreducible curve of genus `g` over a finite field
`k` with `q` elements, `k̄` an algebraic closure of `k` and `ℓ ≠ p` a prime. Write
`V = H¹(X_k̄, ℚ_ℓ)` (`LAdicSheaf.rationalGeometricCompactlySupportedCohomology` of the constant
sheaf in degree `1`; `X` is proper, so this is `H¹`) and `π_X^*` for the geometric Frobenius on it
(`LAdicSheaf.rationalGeometricCompactlySupportedFrobenius`). Then `dim V = 2g` and, for the
eigenvalues `α_1, …, α_{2g}` of `π_X^*` on `V`:

1. the L-function `L(X, ℚ_ℓ) = ∏_{x ∈ |X|} (1 - T^{deg x})⁻¹` is a rational function
   (`Stacks.EtaleCohomology.LAdicSheaf.isRational_constantLFunction_of_smoothProjectiveCurve`);
2. the `α_i` are algebraic integers, independent of `ℓ`: `det(1 - π_X^* T | V)` is the image of
   the integral numerator of the zeta function of `X`, in which `ℓ` does not occur
   (`Stacks.EtaleCohomology.LAdicSheaf.exists_integral_curveNumerator_of_smoothProjectiveCurve`,
   `Stacks.EtaleCohomology.LAdicSheaf.isIntegral_curveEigenvalue_of_smoothProjectiveCurve`);
3. `#X(k_n) = 1 - ∑ α_i^n + q^n` for the extension `k_n` of degree `n` of `k`
   (`LAdicSheaf.natCard_fieldValuedPoints_eq_one_sub_sum_add_of_smoothProjectiveCurve`);
4. `|α_i| < q`
   (`Stacks.EtaleCohomology.LAdicSheaf.norm_curveEigenvalue_lt_of_smoothProjectiveCurve`).

These discharge the hypothesis `hpoint` of the statements of `Trace/ConstantSheafCurve.lean`:
the trace identity `#X(k_m) = 1 - Tr((π_X^*)^m | V) + q^m` is
`Stacks.EtaleCohomology.LAdicSheaf.natCast_natCard_fieldValuedPoints_eq_one_sub_trace_add`,
proved from Weil's formula on `Pic(X_k̄)[ℓⁿ]` and the identification of the levels of
`H¹(X_k̄, ℤ_ℓ)` with `Pic(X_k̄)[ℓⁿ⁺¹]`. The source proves part (3) by Theorem 03V2 for the constant
sheaf on `X ⊗ k_n`; for the constant sheaf on a curve, Theorem 03V2 is equivalent to that trace
identity together with the computation of `H⁰` and `H²`. Part (4) is obtained from the Riemann
hypothesis `|α_i| = √q`
(`Stacks.EtaleCohomology.LAdicSheaf.norm_curveEigenvalue_eq_sqrt_of_smoothProjectiveCurve`, from
Bombieri–Stepanov and the cup product pairing), which the source states after the lemma.

## The statement

The prime `ℓ` is different from the characteristic `p` of `k`, the standing convention of the
chapter for `ℓ`-adic sheaves. The eigenvalues are read, as in `Trace/ConstantSheafCurve.lean`,
through a basis `bV` of `V` indexed by `Fin (2g)` — part (2) includes `dim V = 2g`, so such bases
exist — as a family `α` in a ring `Ω` receiving `ℚ_ℓ` with
`det(1 - A T) = ∏ (1 - α_i T)`, `A` the matrix of `π_X^*` in `bV`. The data `p`, `r` and
`hcard : #k = p ^ r` only name the characteristic and the cardinality of `k`.

## References

* [Stacks Project, Tag 03V8](https://stacks.math.columbia.edu/tag/03V8), Lemma 64.23.1.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
-- the structure projections of `Stacks.Models.RegularModelSituation` are global instances whose
-- conclusions match every goal and send instance search astray; they are irrelevant here
attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

section BaseChange

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [IsProper f] [GeometricallyIrreducible f] (kbar : Type u) [Field kbar] [Algebra k kbar]
  (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime] [CharP k p]

/-- For a smooth proper geometrically irreducible curve `X` over `k` and a prime `ℓ ≠ p`, the
base change `X_k̄` is a smooth proper curve over `k̄` and `ℓ` is invertible in `k̄`. -/
theorem isCurve_smooth_isProper_pullback_snd_and_isUnit (hℓp : ℓ ≠ p) :
    IsCurve kbar (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) ∧
      Smooth (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) ∧
      IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) ∧ IsUnit (ℓ : kbar) := by
  haveI : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  haveI : IsCurve k (Over.mk f).hom := ‹IsCurve k f›
  haveI : Smooth (Over.mk f).hom := ‹Smooth f›
  haveI : IsProper (Over.mk f).hom := ‹IsProper f›
  haveI : GeometricallyIrreducible (Over.mk f).hom := ‹GeometricallyIrreducible f›
  refine ⟨Stacks.Picard.isCurve_baseChange_of_geometricallyIrreducible (Over.mk f) kbar,
    inferInstance, inferInstance, Ne.isUnit fun h => hℓp ?_⟩
  exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1
    ((CharP.cast_eq_zero_iff kbar p ℓ).1 h)).symm

end BaseChange

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProjectiveVariety k f] [GeometricallyIrreducible f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (p r : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ r)

/-- The underlying space of a Noetherian scheme `X` is quasi-separated. -/
local instance : QuasiSeparatedSpace X.obj :=
  @AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace X.1
    (inferInstance : AlgebraicGeometry.IsNoetherian X.1).toIsLocallyNoetherian

include hcard in
/-- **`dim H¹(X_k̄, ℚ_ℓ) = 2g`**, `g` the genus of `X`. -/
theorem LAdicSheaf.finrank_rationalCohomology_one_of_smoothProjectiveCurve (hℓp : ℓ ≠ p) :
    Module.finrank ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)) =
      2 * genus f := by
  obtain ⟨h1, h2, h3, hℓ⟩ := isCurve_smooth_isProper_pullback_snd_and_isUnit f kbar ℓ p hℓp
  rw [← genus_baseChange k kbar (pullback.fst _ _) _ f (IsPullback.of_hasPullback _ _)]
  exact LAdicSheaf.finrank_rationalGeometricCompactlySupportedCohomology_constant_one B X ℓ f kbar
    p r hcard hℓ

include hcard in
/-- `H¹(X_k̄, ℚ_ℓ)` is finite dimensional. -/
theorem LAdicSheaf.finite_rationalCohomology_one_of_smoothProjectiveCurve (hℓp : ℓ ≠ p) :
    Module.Finite ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)) := by
  obtain ⟨h1, h2, h3, hℓ⟩ := isCurve_smooth_isProper_pullback_snd_and_isUnit f kbar ℓ p hℓp
  obtain ⟨-, hfin⟩ := LAdicSheaf.free_finite_constant_one B X ℓ f kbar p r hcard hℓ
  change Module.Finite ℚ_[ℓ] (TensorProduct ℤ_[ℓ] ℚ_[ℓ] _)
  infer_instance

/-- **The trace identity for the constant sheaf on a curve**: for `m ≥ 1` and an extension `K` of
`k` of degree `m`, `#X(K) = 1 - Tr((π_X^*)^m | H¹(X_k̄, ℚ_ℓ)) + q^m`. -/
theorem LAdicSheaf.natCast_natCard_fieldValuedPoints_eq_one_sub_trace_add (hℓp : ℓ ≠ p) {m : ℕ}
    (hm : m ≠ 0) (K : Type u) [Field K] [Algebra k K] [Finite K] (hK : Module.finrank k K = m) :
    (Nat.card (fieldValuedPoints f K) : ℚ_[ℓ]) =
      1 - LinearMap.trace ℚ_[ℓ] _
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p r hcard (LAdicSheaf.constantSystem B X ℓ)
              ((1 : ℕ) : ℤ)).hom ^ m) +
        (Fintype.card k : ℚ_[ℓ]) ^ m := by
  obtain ⟨h1, h2, h3, hℓ⟩ := isCurve_smooth_isProper_pullback_snd_and_isUnit f kbar ℓ p hℓp
  haveI : NeZero m := ⟨hm⟩
  obtain ⟨K', hK'fin, hK'⟩ := exists_intermediateField_finrank_eq k kbar p m
  haveI : Finite K' := Module.finite_of_finite k
  letI : Fintype K' := Fintype.ofFinite K'
  have hcardK' : Fintype.card K' = p ^ (r * m) := by
    rw [Module.card_eq_pow_finrank (K := k), hK', hcard, ← pow_mul]
  have hKK' : Nat.card (fieldValuedPoints f K) = Nat.card (fieldValuedPoints f K') := by
    rw [natCard_fieldValuedPoints, natCard_fieldValuedPoints, hK, hK']
  have hfix : Nat.card (fieldValuedPoints f K') =
      Nat.card (fixedSections (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))
        (geometricFrobeniusBaseChangePow (Over.mk f) kbar p r hcard m)) :=
    (natCard_fixedSections_geometricFrobeniusBaseChangePow (Over.mk f) kbar p r hcard m K'
      hcardK').symm
  rw [hKK', hfix, LAdicSheaf.trace_rationalFrobenius_pow_constant_one B X ℓ f kbar p r hcard hℓ m,
    ← map_natCast (algebraMap ℤ_[ℓ] ℚ_[ℓ]),
    LAdicSheaf.natCast_natCard_fixedSections_eq_one_sub_trace_pow_add B X ℓ f kbar p r hcard hℓ m
      hm]
  simp

/-- The point counts `N m = ∑_{deg x ∣ m} deg x = #X(k_m)` satisfy the hypothesis `hpoint` of
`Trace/ConstantSheafCurve.lean` for the matrix of `π_X^*` in any basis of `H¹(X_k̄, ℚ_ℓ)`. -/
theorem LAdicSheaf.hpoint_of_smoothProjectiveCurve (hℓp : ℓ ≠ p) {g : ℕ}
    (bV : Module.Basis (Fin (2 * g)) ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)))
    (n : ℕ) (hn : n ≠ 0) :
    ((∑ x ∈ (closedPointsDegreeLE f n).filter fun x => residueDegree f x.1 ∣ n,
        residueDegree f x.1 : ℕ) : ℚ_[ℓ]) =
      ∑ a : Fin 3, (if Even (curveDeg a) then (1 : ℚ_[ℓ]) else -1) *
        ((curveFrobenius (Fintype.card k) (LinearMap.toMatrix bV bV
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p r hcard (LAdicSheaf.constantSystem B X ℓ)
              ((1 : ℕ) : ℤ)).hom) a) ^ n).trace := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨K', hK'fin, hK'⟩ := exists_intermediateField_finrank_eq k kbar p n
  haveI : Finite K' := Module.finite_of_finite k
  rw [alternatingTrace_curveFrobenius, LinearMap.toMatrix_pow, ← LinearMap.trace_eq_matrix_trace,
    ← LAdicSheaf.natCast_natCard_fieldValuedPoints_eq_one_sub_trace_add B X ℓ f kbar p r hcard hℓp
      hn K' hK', natCard_fieldValuedPoints, hK']

/-! ### The four parts of Tag 03V8 -/

/-- **Tag 03V8, part (1).** The L-function `L(X, ℚ_ℓ) = ∏_{x ∈ |X|} (1 - T^{deg x})⁻¹` of a smooth,
projective, geometrically irreducible curve over a finite field is a rational function: its
product with a polynomial whose value at `0` is nonzero is a polynomial. (The polynomials are
`(1 - T)(1 - qT)` and `det(1 - π_X^* T | H¹(X_k̄, ℚ_ℓ))`.) -/
@[stacks 03V8 "part (1): L(X, Q_ell) is a rational function, for X a smooth projective \
geometrically irreducible curve over a finite field and ell a prime different from the \
characteristic; its product with (1 - T)(1 - qT) is det(1 - pi_X^* T | H^1(X_kbar, Q_ell))"]
theorem LAdicSheaf.isRational_constantLFunction_of_smoothProjectiveCurve (hℓp : ℓ ≠ p) :
    ∃ P Q : Polynomial ℚ_[ℓ], Q.eval 0 ≠ 0 ∧
      constantLFunction f ℚ_[ℓ] * (Q : PowerSeries ℚ_[ℓ]) = (P : PowerSeries ℚ_[ℓ]) := by
  obtain ⟨r, -, hcard⟩ := FiniteField.card k p
  haveI := LAdicSheaf.finite_rationalCohomology_one_of_smoothProjectiveCurve B X ℓ f
    (AlgebraicClosure k) p r hcard hℓp
  let bV := Module.finBasisOfFinrankEq ℚ_[ℓ] _
    (LAdicSheaf.finrank_rationalCohomology_one_of_smoothProjectiveCurve B X ℓ f (AlgebraicClosure k)
      p r hcard hℓp)
  exact isRational_constantLFunction (Fintype.card k) _ _ (fun n hn => rfl)
    (LAdicSheaf.hpoint_of_smoothProjectiveCurve B X ℓ f (AlgebraicClosure k) p r hcard hℓp bV)

/-- **Tag 03V8, part (2), independence of `ℓ`.** `dim H¹(X_k̄, ℚ_ℓ) = 2g`, and for every basis of
`H¹(X_k̄, ℚ_ℓ)` the polynomial `det(1 - π_X^* T | H¹)` is the image of one integral polynomial of
degree at most `2g` with constant coefficient `1`: the numerator `L(X, ℤ)·(1 - T)(1 - qT)` of the
zeta function of `X`, in which `ℓ` does not occur. -/
@[stacks 03V8 "part (2), independence of ell: dim H^1(X_kbar, Q_ell) = 2g and the characteristic \
polynomial det(1 - pi_X^* T | H^1) is the image of the integral numerator of the zeta function of \
X, a polynomial over Z determined by the Euler product of X, in which ell does not occur"]
theorem LAdicSheaf.exists_integral_curveNumerator_of_smoothProjectiveCurve (hℓp : ℓ ≠ p) :
    Module.finrank ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)) =
      2 * genus f ∧
    ∀ bV : Module.Basis (Fin (2 * genus f)) ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)),
      ∃ P : Polynomial ℤ, P.natDegree ≤ 2 * genus f ∧ P.coeff 0 = 1 ∧
        (P : PowerSeries ℤ) = integralCurveNumerator f (Fintype.card k) ∧
        P.map (Int.castRingHom ℚ_[ℓ]) = localCharPolynomial (LinearMap.toMatrix bV bV
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p r hcard (LAdicSheaf.constantSystem B X ℓ)
              ((1 : ℕ) : ℤ)).hom) 1 :=
  ⟨LAdicSheaf.finrank_rationalCohomology_one_of_smoothProjectiveCurve B X ℓ f kbar p r hcard hℓp,
    fun bV => exists_integral_curveNumerator (Fintype.card k) _ _ (fun n hn => rfl)
      (LAdicSheaf.hpoint_of_smoothProjectiveCurve B X ℓ f kbar p r hcard hℓp bV)⟩

/-- **Tag 03V8, part (2), integrality.** The eigenvalues `α_1, …, α_{2g}` of `π_X^*` on
`H¹(X_k̄, ℚ_ℓ)` are algebraic integers. -/
@[stacks 03V8 "part (2): the eigenvalues alpha_1, ..., alpha_{2g} of pi_X^* on H^1(X_kbar, Q_ell) \
are algebraic integers, being the reciprocal roots of the integral numerator of the zeta \
function, of constant coefficient 1"]
theorem LAdicSheaf.isIntegral_curveEigenvalue_of_smoothProjectiveCurve (hℓp : ℓ ≠ p)
    (bV : Module.Basis (Fin (2 * genus f)) ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)))
    {Ω : Type*} [CommRing Ω] (φ : ℚ_[ℓ] →+* Ω) (α : Fin (2 * genus f) → Ω)
    (hα : (localCharPolynomial (LinearMap.toMatrix bV bV
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
          (CompactificationOf.ofProper f) kbar p r hcard (LAdicSheaf.constantSystem B X ℓ)
            ((1 : ℕ) : ℤ)).hom) 1).map φ =
      ∏ i, (1 - Polynomial.C (α i) * Polynomial.X))
    (i : Fin (2 * genus f)) : IsIntegral ℤ (α i) :=
  isIntegral_curveEigenvalue (Fintype.card k) _ _ (fun n hn => rfl)
    (LAdicSheaf.hpoint_of_smoothProjectiveCurve B X ℓ f kbar p r hcard hℓp bV) φ α hα i

/-- **Tag 03V8, part (3).** The number of points of `X` with values in an extension `k_n` of `k` of
degree `n ≥ 1` is `#X(k_n) = 1 - ∑_{i=1}^{2g} α_i^n + q^n`, `α_i` the eigenvalues of `π_X^*` on
`H¹(X_k̄, ℚ_ℓ)`. -/
@[stacks 03V8 "part (3): #X(k_n) = 1 - sum_{i=1}^{2g} alpha_i^n + q^n for every extension k_n of k \
of degree n >= 1, alpha_i the eigenvalues of pi_X^* on H^1(X_kbar, Q_ell)"]
theorem LAdicSheaf.natCard_fieldValuedPoints_eq_one_sub_sum_add_of_smoothProjectiveCurve
    (hℓp : ℓ ≠ p)
    (bV : Module.Basis (Fin (2 * genus f)) ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)))
    {Ω : Type*} [CommRing Ω] (φ : ℚ_[ℓ] →+* Ω) (α : Fin (2 * genus f) → Ω)
    (hα : (localCharPolynomial (LinearMap.toMatrix bV bV
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
          (CompactificationOf.ofProper f) kbar p r hcard (LAdicSheaf.constantSystem B X ℓ)
            ((1 : ℕ) : ℤ)).hom) 1).map φ =
      ∏ i, (1 - Polynomial.C (α i) * Polynomial.X))
    {n : ℕ} (hn : n ≠ 0) (K : Type u) [Field K] [Algebra k K] [Finite K]
    (hK : Module.finrank k K = n) :
    (Nat.card (fieldValuedPoints f K) : Ω) = 1 - ∑ i, α i ^ n + (Fintype.card k : Ω) ^ n := by
  rw [natCard_fieldValuedPoints, hK]
  exact card_rationalPoints_eq_one_sub_sum_add (Fintype.card k) _ _
    (LAdicSheaf.hpoint_of_smoothProjectiveCurve B X ℓ f kbar p r hcard hℓp bV) φ α hα hn

/-- **The Riemann hypothesis for the eigenvalues of `π_X^*` on `H¹(X_k̄, ℚ_ℓ)`**, which the source
states after Tag 03V8: read in `ℂ`, every `α_i` has `|α_i| = √q`. -/
theorem LAdicSheaf.norm_curveEigenvalue_eq_sqrt_of_smoothProjectiveCurve (hℓp : ℓ ≠ p)
    (bV : Module.Basis (Fin (2 * genus f)) ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)))
    (φ : ℚ_[ℓ] →+* ℂ) (α : Fin (2 * genus f) → ℂ)
    (hα : (localCharPolynomial (LinearMap.toMatrix bV bV
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
          (CompactificationOf.ofProper f) kbar p r hcard (LAdicSheaf.constantSystem B X ℓ)
            ((1 : ℕ) : ℤ)).hom) 1).map φ =
      ∏ i, (1 - Polynomial.C (α i) * Polynomial.X))
    (i : Fin (2 * genus f)) : ‖α i‖ = Real.sqrt (Fintype.card k) := by
  obtain ⟨h1, h2, h3, hℓ⟩ := isCurve_smooth_isProper_pullback_snd_and_isUnit f kbar ℓ p hℓp
  haveI : GeometricallyReduced f := geometricallyReduced_of_smooth f
  haveI : GeometricallyIntegral f :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  obtain ⟨J, hJ, hAJ⟩ := LAdicSheaf.exists_isUnit_det_transpose_mul_mul_eq_card_smul B X ℓ f kbar p
    r hcard hℓ bV
  let N : ℕ → ℕ := fun m => ∑ x ∈ (closedPointsDegreeLE f m).filter
    (fun x => residueDegree f x.1 ∣ m), residueDegree f x.1
  have hN : ∀ m : ℕ, m ≠ 0 → ∀ (K : Type u) [Field K] [Algebra k K] [Finite K],
      Module.finrank k K = m → Nat.card (fieldValuedPoints f K) = N m := by
    intro m _ K _ _ _ hK
    rw [natCard_fieldValuedPoints, hK]
  exact Stacks.BombieriStepanov.norm_curveEigenvalue_eq_sqrt (k := k) p f N hN
    (LinearMap.toMatrix bV bV
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
        (CompactificationOf.ofProper f) kbar p r hcard (LAdicSheaf.constantSystem B X ℓ)
          ((1 : ℕ) : ℤ)).hom) J
    (LAdicSheaf.hpoint_of_smoothProjectiveCurve B X ℓ f kbar p r hcard hℓp bV) hJ hAJ φ α hα i

/-- **Tag 03V8, part (4).** Every eigenvalue `α_i` of `π_X^*` on `H¹(X_k̄, ℚ_ℓ)`, read in `ℂ` along
a ring map `ℚ_ℓ → ℂ`, has `|α_i| < q`. -/
@[stacks 03V8 "part (4): |alpha_i| < q for every eigenvalue alpha_i of pi_X^* on H^1(X_kbar, Q_ell) \
read in C; it follows from the Riemann hypothesis |alpha_i| = sqrt q, which the source states \
right after the lemma"]
theorem LAdicSheaf.norm_curveEigenvalue_lt_of_smoothProjectiveCurve (hℓp : ℓ ≠ p)
    (bV : Module.Basis (Fin (2 * genus f)) ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)))
    (φ : ℚ_[ℓ] →+* ℂ) (α : Fin (2 * genus f) → ℂ)
    (hα : (localCharPolynomial (LinearMap.toMatrix bV bV
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
          (CompactificationOf.ofProper f) kbar p r hcard (LAdicSheaf.constantSystem B X ℓ)
            ((1 : ℕ) : ℤ)).hom) 1).map φ =
      ∏ i, (1 - Polynomial.C (α i) * Polynomial.X))
    (i : Fin (2 * genus f)) : ‖α i‖ < (Fintype.card k : ℝ) := by
  rw [LAdicSheaf.norm_curveEigenvalue_eq_sqrt_of_smoothProjectiveCurve B X ℓ f kbar p r hcard hℓp
    bV φ α hα i, Real.sqrt_lt_self_iff]
  exact_mod_cast Fintype.one_lt_card

end Stacks.EtaleCohomology

end
