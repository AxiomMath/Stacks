module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NodalResolution
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# The nodal chart ring `R[x, y]/(xy - πⁿ)` is normal

Let `R` be a discrete valuation ring with uniformizer `π` and `n ≥ 0`. The ring
`A = R[x, y]/(xy - πⁿ)` of the standard nodal model is an integrally closed domain. This is the
normality of the local model of [Stacks, Tag 0CDC], used to show that the blowup of the model in
its singular point does not change the structure sheaf.

## Implementation notes

`A` is the intersection of its two localizations `A_x` and `A_y` inside its fraction field: if
`a / xᵖ = b / y^q` then `a y^q = b xᵖ`, and `y` is a nonzerodivisor modulo every power of `x`,
because `A/(x) = (R/(πⁿ))[y]`. Each of `A_x`, `A_y` is normal, since its local rings are local
rings of `A` at primes not containing both coordinates, which are regular
(`Stacks.SemistableReduction.isRegularLocalRing_localization_nodalChartRing_of_not_and`).

## Main results

* `Stacks.mem_span_nodalGen_zero_of_mul`: `y c ∈ (x)` implies `c ∈ (x)`.
* `Stacks.isIntegrallyClosed_nodalChartRing`: `R[x, y]/(xy - h)` is integrally closed, for `R`
  a regular unique factorization domain and `h ≠ 0`.

## References

* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
-/

@[expose] public noncomputable section

universe u

namespace Stacks

variable {R : Type u} [CommRing R]

/-- The `R`-algebra map `R[x, y]/(xy - h) → (R/(h))[T]` killing `x` and sending `y` to `T`. -/
def nodalReduce (h : R) : nodalChartRing R h →ₐ[R] Polynomial (R ⧸ Ideal.span {h}) :=
  nodalLift ![0, Polynomial.X] (by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul]
    rw [Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self h), map_zero])

/-- `nodalReduce h` sends `x` to `0`. -/
theorem nodalReduce_nodalGen_zero (h : R) : nodalReduce h (nodalGen R h 0) = 0 :=
  nodalLift_nodalGen _ _ 0

/-- `nodalReduce h` sends `y` to `T`. -/
theorem nodalReduce_nodalGen_one (h : R) : nodalReduce h (nodalGen R h 1) = Polynomial.X :=
  nodalLift_nodalGen _ _ 1

/-- **`y` is a nonzerodivisor modulo `x`**: in `R[x, y]/(xy - h)`, `y c ∈ (x)` implies
`c ∈ (x)`. -/
theorem mem_span_nodalGen_zero_of_mul {h : R} {c : nodalChartRing R h}
    (hc : nodalGen R h 1 * c ∈ Ideal.span {nodalGen R h 0}) :
    c ∈ Ideal.span {nodalGen R h 0} := by
  set J := Ideal.span {nodalGen R h 0}
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective c
  let ev : MvPolynomial (Fin 2) R →ₐ[R] Polynomial R := MvPolynomial.aeval ![0, Polynomial.X]
  let σ : Polynomial R →ₐ[R] nodalChartRing R h := Polynomial.aeval (nodalGen R h 1)
  have h1 : (Ideal.Quotient.mkₐ R J).comp (Ideal.Quotient.mkₐ R _) =
      (Ideal.Quotient.mkₐ R J).comp (σ.comp ev) := by
    refine MvPolynomial.algHom_ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ev, σ, MvPolynomial.aeval_X,
        Matrix.cons_val_zero, map_zero]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    · simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ev, σ, MvPolynomial.aeval_X,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Polynomial.aeval_X]
      rfl
  have h1' : Ideal.Quotient.mk J (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk J (σ (ev P)) :=
    congrArg (fun φ => φ P) h1
  -- the reduction of the class of `P` is the reduction of that polynomial
  have h2 : (nodalReduce h).comp (Ideal.Quotient.mkₐ R _) =
      (Polynomial.mapAlgHom (Ideal.Quotient.mkₐ R (Ideal.span {h}))).comp ev := by
    refine MvPolynomial.algHom_ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ev, MvPolynomial.aeval_X,
        Matrix.cons_val_zero, map_zero]
      exact nodalReduce_nodalGen_zero h
    · simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ev, MvPolynomial.aeval_X,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [Polynomial.coe_mapAlgHom, Polynomial.map_X]
      exact nodalReduce_nodalGen_one h
  have h2' : nodalReduce h (Ideal.Quotient.mk _ P) =
      Polynomial.map (Ideal.Quotient.mk (Ideal.span {h})) (ev P) :=
    congrArg (fun φ => φ P) h2
  -- the reduction kills `(x)`
  have hJ : ∀ z ∈ J, nodalReduce h z = 0 := by
    intro z hz
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    rw [map_mul, nodalReduce_nodalGen_zero, mul_zero]
  have h3 : Polynomial.X * nodalReduce h (Ideal.Quotient.mk _ P) = Polynomial.X * 0 := by
    rw [← nodalReduce_nodalGen_one h, ← map_mul, mul_zero]
    exact hJ _ hc
  have h4 : Polynomial.map (Ideal.Quotient.mk (Ideal.span {h})) (ev P) = 0 := by
    rw [← h2']
    exact Polynomial.isRegular_X.left h3
  have h5 : ev P ∈ Ideal.map Polynomial.C (Ideal.span {h}) := by
    rw [Ideal.mem_map_C_iff]
    intro n
    have := congrArg (fun p => Polynomial.coeff p n) h4
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  have h6 : σ (ev P) ∈ J := by
    have hle : Ideal.map (σ : Polynomial R →+* nodalChartRing R h)
        (Ideal.map Polynomial.C (Ideal.span {h})) ≤ J := by
      rw [Ideal.map_map, Ideal.map_span, Ideal.span_le, Set.image_singleton,
        Set.singleton_subset_iff]
      change σ (Polynomial.C h) ∈ J
      rw [Polynomial.aeval_C, ← nodalGen_zero_mul_nodalGen_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    exact hle (Ideal.mem_map_of_mem _ h5)
  exact Ideal.Quotient.eq_zero_iff_mem.1 (h1'.trans (Ideal.Quotient.eq_zero_iff_mem.2 h6))

/-- `y` is a nonzerodivisor modulo every power of `x`, in a domain. -/
theorem mem_span_nodalGen_zero_pow_of_mul_pow {h : R} [IsDomain (nodalChartRing R h)]
    (hx : nodalGen R h 0 ≠ 0) :
    ∀ (p q : ℕ) (c : nodalChartRing R h),
      nodalGen R h 1 ^ q * c ∈ Ideal.span {nodalGen R h 0 ^ p} →
        c ∈ Ideal.span {nodalGen R h 0 ^ p} := by
  intro p
  induction p with
  | zero => simp
  | succ p ih =>
    intro q
    induction q with
    | zero => exact fun c hc => by simpa using hc
    | succ q ihq =>
      intro c hc
      have hx1 : nodalGen R h 1 ^ q * c ∈ Ideal.span {nodalGen R h 0} := by
        refine mem_span_nodalGen_zero_of_mul
          (Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ (Nat.succ_ne_zero p)) ?_)
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hc
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hx1
      have hd' : nodalGen R h 1 * d ∈ Ideal.span {nodalGen R h 0 ^ p} := by
        obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hc
        refine Ideal.mem_span_singleton'.2 ⟨e, ?_⟩
        apply mul_left_cancel₀ hx
        linear_combination he - nodalGen R h 1 * hd
      have hdp : d ∈ Ideal.span {nodalGen R h 0 ^ p} := ih 1 d (by simpa using hd')
      refine ihq c ?_
      obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hdp
      refine Ideal.mem_span_singleton'.2 ⟨e, ?_⟩
      rw [← hd, ← he]
      ring

section Normal

variable [IsDomain R] [IsRegularRing R] [UniqueFactorizationMonoid R] {h : R}

omit [IsRegularRing R] [UniqueFactorizationMonoid R] in
/-- For `h ≠ 0`, both coordinates `x` and `y` of `R[x, y]/(xy - h)` are nonzero. -/
theorem nodalGen_ne_zero (hh : h ≠ 0) (i : Fin 2) : nodalGen R h i ≠ 0 := by
  fin_cases i
  · exact nodalGen_zero_ne_zero h
  · exact nodalGen_one_ne_zero hh

/-- **The localizations of `R[x, y]/(xy - h)` away from either coordinate are integrally
closed**, for `R` a regular unique factorization domain and `h ≠ 0`. -/
theorem isIntegrallyClosed_localization_away_nodalGen (hh : h ≠ 0) (i : Fin 2) :
    IsIntegrallyClosed (Localization.Away (nodalGen R h i)) := by
  have := isDomain_nodalChartRing hh
  have : IsDomain (Localization.Away (nodalGen R h i)) :=
    IsLocalization.isDomain_localization
      (powers_le_nonZeroDivisors_of_noZeroDivisors (nodalGen_ne_zero hh i))
  refine IsIntegrallyClosed.of_localization_maximal fun P _ _ => ?_
  let q := P.comap (algebraMap (nodalChartRing R h) (Localization.Away (nodalGen R h i)))
  have hq : ¬ (nodalGen R h 0 ∈ q ∧ nodalGen R h 1 ∈ q) := by
    rintro ⟨h0, h1⟩
    have hi : nodalGen R h i ∈ q := by
      fin_cases i <;> assumption
    exact (inferInstance : P.IsPrime).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hi (IsLocalization.Away.algebraMap_isUnit _))
  have := SemistableReduction.isRegularLocalRing_localization_nodalChartRing_of_not_and h q hq
  have := isIntegrallyClosed_of_isRegularLocalRing (Localization.AtPrime q)
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Submonoid.powers (nodalGen R h i)) P).toRingEquiv

/-- **`R[x, y]/(xy - h)` is integrally closed**, for `R` a regular unique factorization domain
and `h ≠ 0`. -/
theorem isIntegrallyClosed_nodalChartRing (hh : h ≠ 0) :
    IsIntegrallyClosed (nodalChartRing R h) := by
  have := isDomain_nodalChartRing hh
  let S : Fin 2 → Submonoid (nodalChartRing R h) := fun i => Submonoid.powers (nodalGen R h i)
  have hS : ∀ i, S i ≤ nonZeroDivisors _ := fun i =>
    powers_le_nonZeroDivisors_of_noZeroDivisors (nodalGen_ne_zero hh i)
  refine IsIntegrallyClosed.of_localization_submonoid S hS
    (isIntegrallyClosed_localization_away_nodalGen hh) ?_
  refine le_antisymm (fun z hz => ?_) bot_le
  have hz' := Algebra.mem_iInf.1 hz
  obtain ⟨a, s, hs, rfl⟩ := hz' 0
  obtain ⟨b, t, ht, hbt⟩ := hz' 1
  obtain ⟨p, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hs
  obtain ⟨q, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 ht
  have hcross : nodalGen R h 1 ^ q * a = nodalGen R h 0 ^ p * b := by
    rw [IsLocalization.mk'_eq_iff_eq] at hbt
    exact IsFractionRing.injective _ (FractionRing (nodalChartRing R h)) hbt
  have ha : a ∈ Ideal.span {nodalGen R h 0 ^ p} :=
    mem_span_nodalGen_zero_pow_of_mul_pow (nodalGen_ne_zero hh 0) p q a
      (hcross ▸ Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  exact Algebra.mem_bot.2 ⟨c, (IsLocalization.mk'_mul_cancel_right _ _).symm⟩

end Normal

end Stacks

end
