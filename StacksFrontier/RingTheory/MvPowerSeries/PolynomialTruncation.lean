module

public import StacksFrontier.RingTheory.MvPowerSeries.LowDegree
public import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# Truncating a power series ring to a polynomial ring

Let `R` be a commutative ring and let `J = (X₀, …, X_{n-1})` be the ideal of variables, either of
`MvPowerSeries (Fin n) R` or of `MvPolynomial (Fin n) R`. This file proves that `Jᵗ` is *exactly*
the set of series whose coefficients in total degree below `t` vanish — the inclusion
`Stacks.MvPowerSeries.RegularParameters.coeff_eq_zero_of_mem_pow_span_range_X` is the easy half —
and deduces that the inclusion of polynomials into power series induces a ring isomorphism

`MvPolynomial (Fin n) R ⧸ Jᵗ ≃+* MvPowerSeries (Fin n) R ⧸ Jᵗ`.

So a power series ring modulo a power of its ideal of variables is a *polynomial* truncation: no
power series survives the quotient. This is what makes a truncated chart isomorphism of a power
series ring provable where its untruncated form can fail, the point being that a polynomial
truncation commutes with localization while a power series ring does not.

## Main results

* `Stacks.MvPowerSeries.RegularParameters.lowDegreeVanishing_le_pow_span_range_X` — the half with
  content: a power series whose coefficients in total degree below `t` all vanish lies in `Jᵗ`.
  The series is split along the *least* variable occurring in each monomial, which divides the
  corresponding piece, and induction on `t` applies to the quotients.
* `Stacks.MvPowerSeries.RegularParameters.mem_pow_span_range_X_iff` — the resulting
  characterization of `Jᵗ` by coefficients.
* `Stacks.MvPowerSeries.RegularParameters.mem_pow_span_range_MvPolynomial_X_iff` — the polynomial
  analogue, where the content is instead the finiteness of the support.
* `Stacks.MvPowerSeries.RegularParameters.ker_mk_comp_coeToMvPowerSeries` — the kernel of
  `MvPolynomial (Fin n) R → MvPowerSeries (Fin n) R ⧸ Jᵗ` is the polynomial `Jᵗ`.
* `Stacks.MvPowerSeries.RegularParameters.polynomialTruncationEquiv` — the induced isomorphism
  `MvPolynomial (Fin n) R ⧸ Jᵗ ≃+* MvPowerSeries (Fin n) R ⧸ Jᵗ`.

## Implementation notes

Total degree is spelled `∑ i, d i`, as in `StacksFrontier/RingTheory/MvPowerSeries/LowDegree.lean`,
rather than through `Finsupp.degree`.

Surjectivity of `MvPolynomial (Fin n) R → MvPowerSeries (Fin n) R ⧸ Jᵗ` is witnessed by
`MvPowerSeries.trunc'` at the *box* with every exponent `t` rather than at the simplex of total
degree below `t`: the box is a `Finsupp` already to hand, and all that is needed of it is that it
contains the simplex, since a monomial outside the box has some exponent exceeding `t` and so
total degree above `t`.
-/

@[expose] public section

namespace Stacks.MvPowerSeries.RegularParameters

variable {R : Type*} [CommRing R] {n : ℕ}

/-! ### An auxiliary fact -/

private theorem sum_single_add (i : Fin n) (e : Fin n →₀ ℕ) :
    ∑ j, ((Finsupp.single i 1 + e : Fin n →₀ ℕ)) j = 1 + ∑ j, e j := by
  rw [← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum, map_add, Finsupp.degree_single]

/-! ### The ideal of variables of a power series ring, by coefficients -/

/-- The part of `f` carried by the monomials whose least occurring variable is `X i`. It is
divisible by `X i`, and summing over `i` recovers `f` as soon as `f` has no constant term. -/
private def leastVarPart (f : MvPowerSeries (Fin n) R) (i : Fin n) : MvPowerSeries (Fin n) R :=
  fun d => if (∀ j, j < i → d j = 0) ∧ d i ≠ 0 then MvPowerSeries.coeff d f else 0

private theorem coeff_leastVarPart (f : MvPowerSeries (Fin n) R) (i : Fin n) (d : Fin n →₀ ℕ) :
    MvPowerSeries.coeff d (leastVarPart f i) =
      if (∀ j, j < i → d j = 0) ∧ d i ≠ 0 then MvPowerSeries.coeff d f else 0 :=
  rfl

private theorem X_dvd_leastVarPart (f : MvPowerSeries (Fin n) R) (i : Fin n) :
    (MvPowerSeries.X i : MvPowerSeries (Fin n) R) ∣ leastVarPart f i := by
  rw [MvPowerSeries.X_dvd_iff]
  intro m hm
  rw [coeff_leastVarPart]
  simp [hm]

private theorem sum_leastVarPart (f : MvPowerSeries (Fin n) R)
    (h0 : MvPowerSeries.coeff 0 f = 0) : ∑ i, leastVarPart f i = f := by
  refine MvPowerSeries.ext fun d => ?_
  rw [map_sum]
  by_cases hd : d = 0
  · subst hd
    simp [coeff_leastVarPart, h0]
  · have hne : d.support.Nonempty := Finsupp.support_nonempty_iff.mpr hd
    set i₀ := d.support.min' hne
    have hi₀ne : d i₀ ≠ 0 := Finsupp.mem_support_iff.mp (d.support.min'_mem hne)
    have hlt : ∀ j, j < i₀ → d j = 0 := fun j hj => by
      by_contra hj0
      exact absurd (d.support.min'_le j (Finsupp.mem_support_iff.mpr hj0)) (not_le.mpr hj)
    refine (Finset.sum_eq_single i₀ (fun i _ hi => ?_)
      (fun h => absurd (Finset.mem_univ i₀) h)).trans ?_
    · rw [coeff_leastVarPart, if_neg]
      rintro ⟨hall, hne'⟩
      rcases lt_or_gt_of_ne hi with h | h
      · exact hne' (hlt i h)
      · exact hi₀ne (hall i₀ h)
    · rw [coeff_leastVarPart, if_pos ⟨hlt, hi₀ne⟩]

private theorem coeff_single_add_X_mul (i : Fin n) (g : MvPowerSeries (Fin n) R)
    (e : Fin n →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.single i 1 + e)
        ((MvPowerSeries.X i : MvPowerSeries (Fin n) R) * g) = MvPowerSeries.coeff e g := by
  rw [MvPowerSeries.X, MvPowerSeries.coeff_add_monomial_mul, one_mul]

/-- **A power series with no coefficient in total degree below `t` lies in the `t`-th power of the
ideal of variables.** The converse of
`Stacks.MvPowerSeries.RegularParameters.coeff_eq_zero_of_mem_pow_span_range_X`, and the half that
has content: the series is cut into the parts whose monomials have a given least variable, each
part is divisible by that variable, and the quotients again have no coefficient in total degree
below `t - 1`. -/
theorem lowDegreeVanishing_le_pow_span_range_X (t : ℕ) :
    lowDegreeVanishing R n t ≤
      Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    intro f hf
    have h0 : MvPowerSeries.coeff 0 f = 0 := hf 0 (by simp)
    rw [← sum_leastVarPart f h0]
    refine Ideal.sum_mem _ fun i _ => ?_
    obtain ⟨g, hg⟩ := X_dvd_leastVarPart f i
    have hgmem : g ∈ lowDegreeVanishing R n t := by
      intro e he
      have hcoeff : MvPowerSeries.coeff e g =
          MvPowerSeries.coeff (Finsupp.single i 1 + e) (leastVarPart f i) := by
        rw [hg, coeff_single_add_X_mul]
      rw [hcoeff, coeff_leastVarPart]
      split_ifs with h
      · exact hf _ (by rw [sum_single_add]; omega)
      · rfl
    rw [hg, pow_succ, mul_comm (MvPowerSeries.X i : MvPowerSeries (Fin n) R) g]
    exact Ideal.mul_mem_mul (ih hgmem) (Ideal.subset_span (Set.mem_range_self i))

/-- **The `t`-th power of the ideal of variables of a power series ring, by coefficients.** -/
theorem mem_pow_span_range_X_iff {t : ℕ} {f : MvPowerSeries (Fin n) R} :
    f ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) ^ t ↔
      ∀ d : Fin n →₀ ℕ, (∑ i, d i) < t → MvPowerSeries.coeff d f = 0 :=
  ⟨coeff_eq_zero_of_mem_pow_span_range_X,
    fun hf => lowDegreeVanishing_le_pow_span_range_X t hf⟩

/-! ### The ideal of variables of a polynomial ring, by coefficients -/

/-- **The `t`-th power of the ideal of variables of a polynomial ring, by coefficients.** For
polynomials the content is in the other half: the support is finite, so the polynomial is the sum
of its monomials, and a monomial of total degree at least `t` is a product of at least `t`
variables. -/
theorem mem_pow_span_range_MvPolynomial_X_iff {t : ℕ} {p : MvPolynomial (Fin n) R} :
    p ∈ Ideal.span (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) R)) ^ t ↔
      ∀ d : Fin n →₀ ℕ, (∑ i, d i) < t → p.coeff d = 0 := by
  constructor
  · intro hp d hd
    have hmapgen :
        Ideal.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := R))
            (Ideal.span (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) R))) ≤
          Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
      exact Ideal.subset_span ⟨i, by simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply]⟩
    have hmem : (p : MvPowerSeries (Fin n) R) ∈
        Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) ^ t := by
      have := Ideal.pow_right_mono hmapgen t (by
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hp)
      simpa [MvPolynomial.coeToMvPowerSeries.ringHom_apply] using this
    simpa using coeff_eq_zero_of_mem_pow_span_range_X hmem d hd
  · intro hp
    rw [MvPolynomial.as_sum p]
    refine Ideal.sum_mem _ fun d hd => ?_
    have hdeg : t ≤ ∑ i, d i := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.mp hd) (hp d (by omega))
    rw [MvPolynomial.monomial_eq]
    refine Ideal.mul_mem_left _ _ ?_
    have hprod : (d.prod fun i e => (MvPolynomial.X i : MvPolynomial (Fin n) R) ^ e) ∈
        ∏ i ∈ d.support,
          Ideal.span (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) R)) ^ d i :=
      Ideal.prod_mem_prod fun i _ =>
        Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _
    rw [Finset.prod_pow_eq_pow_sum] at hprod
    refine Ideal.pow_le_pow_right ?_ hprod
    refine hdeg.trans (le_of_eq ?_)
    refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
    simpa using Finsupp.notMem_support_iff.mp hi

/-! ### The induced isomorphism of quotients -/

/-- **Every power series is a polynomial modulo a power of the ideal of variables.** The witness is
the truncation at the box with every exponent `t`. -/
theorem exists_polynomial_sub_mem_pow_span_range_X (t : ℕ) (f : MvPowerSeries (Fin n) R) :
    ∃ p : MvPolynomial (Fin n) R, f - (p : MvPowerSeries (Fin n) R) ∈
      Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) ^ t := by
  refine ⟨MvPowerSeries.trunc' R (Finsupp.equivFunOnFinite.symm fun _ => t) f, ?_⟩
  rw [mem_pow_span_range_X_iff]
  intro d hd
  have hle : d ≤ (Finsupp.equivFunOnFinite.symm fun _ : Fin n => t) := by
    intro i
    have := Finset.single_le_sum (f := fun j : Fin n => d j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    omega
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos hle, sub_self]

/-- **The kernel of `MvPolynomial (Fin n) R → MvPowerSeries (Fin n) R ⧸ Jᵗ`** is the `t`-th power
of the ideal of variables of the polynomial ring. -/
theorem ker_mk_comp_coeToMvPowerSeries (t : ℕ) :
    RingHom.ker ((Ideal.Quotient.mk
          (Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) ^ t)).comp
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := R))) =
      Ideal.span (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) R)) ^ t := by
  ext p
  rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_pow_span_range_X_iff, mem_pow_span_range_MvPolynomial_X_iff]
  simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply]

/-- **A power series ring modulo a power of its ideal of variables is a polynomial ring modulo the
same.** The inclusion of polynomials into power series induces an isomorphism of the two quotients:
it is surjective by
`Stacks.MvPowerSeries.RegularParameters.exists_polynomial_sub_mem_pow_span_range_X`, and its kernel
is computed by `Stacks.MvPowerSeries.RegularParameters.ker_mk_comp_coeToMvPowerSeries`. -/
noncomputable def polynomialTruncationEquiv (t : ℕ) :
    MvPolynomial (Fin n) R ⧸
        Ideal.span (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) R)) ^ t ≃+*
      MvPowerSeries (Fin n) R ⧸
        Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) ^ t :=
  (Ideal.quotEquivOfEq (ker_mk_comp_coeToMvPowerSeries t).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := (Ideal.Quotient.mk
          (Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) ^ t)).comp
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := R)))
      (fun z => by
        obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
        obtain ⟨p, hp⟩ := exists_polynomial_sub_mem_pow_span_range_X t f
        refine ⟨p, ?_⟩
        rw [RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
          Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← neg_sub]
        exact neg_mem hp))

/-- `polynomialTruncationEquiv t` sends the class of a polynomial `p` to the class of `p` viewed as
a power series. -/
@[simp]
theorem polynomialTruncationEquiv_mk (t : ℕ) (p : MvPolynomial (Fin n) R) :
    polynomialTruncationEquiv t (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (p : MvPowerSeries (Fin n) R) := by
  rfl

/-- **The isomorphism carries the class of a polynomial ideal to the class of its image.** Stated
for a principal ideal, which is the case the chart computations need: the relation of a
hypersurface. -/
theorem map_mk_span_singleton_eq (t : ℕ) (p : MvPolynomial (Fin n) R) :
    Ideal.map (Ideal.Quotient.mk
          (Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) ^ t))
        (Ideal.span {(p : MvPowerSeries (Fin n) R)}) =
      Ideal.map (polynomialTruncationEquiv (R := R) (n := n) t).toRingHom
        (Ideal.map (Ideal.Quotient.mk
            (Ideal.span (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) R)) ^ t))
          (Ideal.span {p})) := by
  rw [Ideal.map_map, Ideal.map_span, Ideal.map_span]
  congr 1
  simp

end Stacks.MvPowerSeries.RegularParameters

end
