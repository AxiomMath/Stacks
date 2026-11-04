module

public import StacksFrontier.RingTheory.HilbertSamuel.Defs
public import StacksFrontier.RingTheory.HilbertFunction.Numerical
import StacksFrontier.RingTheory.HilbertSamuel.Function
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Additivity to leading order of the Hilbert–Samuel function

Proof of `Ideal.max_degree_eq_degree_of_exact` (Stacks 00KC): for a short exact sequence
`0 → M' → M → M'' → 0` of finite modules over a Noetherian local ring `(R, m)` and an ideal of
definition `I`, the error `χ_{I,M} - χ_{I,M''} - χ_{I,M'}` has degree `<` the degree of
`χ_{I,M'}` unless `M'` has finite length, and the degree of `χ_{I,M}` is the maximum of the
degrees of `χ_{I,M'}` and `χ_{I,M''}`.

## Main results

* `Stacks.HilbertSamuel.ShortExactDegree.solution`: the statement of the lemma.

## Implementation notes

The equality of degrees rests on three comparisons of Hilbert–Samuel functions, valid for every
`n` (resp. every `n ≥ c`) and with no hypothesis on `M'`:

* `length_le_add`: `χ_{I,M}(n) ≤ χ_{I,M'}(n) + χ_{I,M''}(n)`,
* `length_le_of_exact`: `χ_{I,M''}(n) ≤ χ_{I,M}(n)`, and
* `exists_length_shift_le`: `χ_{I,M'}(n - c) ≤ χ_{I,M}(n)` for `n ≥ c` (Artin–Rees, Lemma 00IN).

The first two are read off the short exact sequence
`0 → M'/(M' ∩ I^{n+1}M) → M/I^{n+1}M → M''/I^{n+1}M'' → 0` of `StacksHelpers.length_quotient_ses`,
the third off `StacksHelpers.comap_pow_smul_eq`. Since the leading coefficients of `χ_{I,M'}` and
`χ_{I,M''}` are nonnegative, the degree of `χ_{I,M'} + χ_{I,M''}` is the maximum of the two
degrees, and a backward shift does not change a degree, so the three comparisons squeeze
`deg χ_{I,M}` between `max {deg χ_{I,M'}, deg χ_{I,M''}}` and itself. The source instead deduces
part (2) from part (1) when `M'` has infinite length and by an Artin–Rees argument when `M'` has
finite length; the three comparisons subsume both cases, and part (3) of the source is the case
`I = maximalIdeal R` of the last conjunct, so it needs no separate argument.

The degree bound of part (1) is the source's argument. Lemma 00K6
(`additivity_of_characteristic_and_hilbert_functions`) produces a submodule `N ⊆ M'` of finite
colength `l` and a shift `c` with `χ_{I,M}(n) = χ_{I,M''}(n) + χ_{I,N}(n - c) + l` for `n ≥ c`,
which `eq_add_comp_add_C_of_charFn_eq` turns into the identity `P = P'' + Q(X - c) + l` of the
computing polynomials, `Q` being the one for `N`. So the error is
`(Q(X - c) - Q) + (Q - P') + l`, and its three summands have degree `< deg χ_{I,M'}`: the first
by `degree_comp_X_sub_C_sub_lt`, the elementary calculus fact that a backward shift changes a
polynomial by one of strictly smaller degree; the second by Lemma 00KB
(`HilbertSamuel.degree_sub_lt`), which also forces `deg Q = deg χ_{I,M'}` through
`degree_eq_of_degree_sub_lt`; the third because `deg χ_{I,M'} > 0` when `M'` has infinite length.

`Computes I N P` is the hypothesis shape of the lemma — `P` computes
`n ↦ length_R (N / I^{n+1} N)` at all large `n` — spelled with the lengths rather than with
`HilbertSamuel.hilbertSamuelFunction` because it is verbatim the condition on which Definition
00KA branches, which is what `hilbertSamuelDegree_eq_degree` needs; that lemma turns Definition
00KA, which reads the degree off a polynomial chosen by `Classical.choose`, into the degree of
*any* computing polynomial, and uniqueness of a computing polynomial
(`eq_of_eventually_eval_natCast_eq`) is all that is needed for this, so Lemma 00K9 is not used.
A computing polynomial exists by Proposition 00K8, whose binomial-basis presentation is converted
by `Stacks.HilbertFunction.PolynomialQuotient.binomialPoly`. A `Computes` hypothesis carries both
  halves of what the
comparisons above need: the lengths it computes are finite (`Computes.eventually_length_eq`) and
the polynomial's values are their casts (`Computes.isHilbertSamuelPoly`, and
`Computes.eventually_eval_comp` for the backward shift).

## References

* [Stacks Project, Tag 00KC](https://stacks.math.columbia.edu/tag/00KC)
-/

@[expose] public section

namespace Stacks.HilbertSamuel.ShortExactDegree

open Filter _root_.HilbertSamuel IsLocalRing Polynomial
open _root_.Stacks.HilbertFunction.NumericalPoly

/-! ### Elementary facts about rational polynomials -/

/-- A backward shift does not change the degree of a polynomial. -/
private lemma degree_comp_X_sub_C (p : ℚ[X]) (c : ℚ) : (p.comp (X - C c)).degree = p.degree := by
  rw [show (X - C c : ℚ[X]) = X + C (-c) by rw [map_neg, sub_eq_add_neg], ← taylor_apply]
  exact degree_taylor p (-c)

/-- **Elementary calculus.** The backward difference `p(X - c) - p(X)` of a nonzero polynomial
has degree strictly smaller than that of `p`: the shift preserves the degree and the leading
coefficient. -/
private lemma degree_comp_X_sub_C_sub_lt {p : ℚ[X]} (hp : p ≠ 0) (c : ℚ) :
    (p.comp (X - C c) - p).degree < p.degree := by
  have hd := degree_comp_X_sub_C p c
  have h := Polynomial.degree_sub_lt_left hd (by rwa [Ne, ← degree_eq_bot, hd, degree_eq_bot])
    (by rw [leadingCoeff_comp (by simp)]; simp)
  rwa [hd] at h

/-- The degree of a sum of two polynomials with nonnegative leading coefficients is the maximum
of their degrees: no cancellation can occur in the leading term. -/
private lemma degree_add_eq_max_of_leadingCoeff_nonneg {p q : ℚ[X]} (hp : 0 ≤ p.leadingCoeff)
    (hq : 0 ≤ q.leadingCoeff) : (p + q).degree = max p.degree q.degree := by
  rcases lt_trichotomy p.degree q.degree with h | h | h
  · rw [degree_add_eq_right_of_degree_lt h, max_eq_right h.le]
  · rcases eq_or_ne p 0 with rfl | hp0
    · simp
    · have h1 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
      have h2 : q.leadingCoeff ≠ 0 :=
        leadingCoeff_ne_zero.mpr fun h0 => hp0 (by simpa [h0] using h)
      rw [degree_add_eq_of_leadingCoeff_add_ne_zero (by positivity), h, max_self]
  · rw [degree_add_eq_left_of_degree_lt h, max_eq_left h.le]

/-- Two polynomials whose difference has degree smaller than each of them have equal degree: a
strict drop in the difference rules out either degree dominating. -/
private lemma degree_eq_of_degree_sub_lt {p q : ℚ[X]} (hp : (p - q).degree < p.degree)
    (hq : (p - q).degree < q.degree) : p.degree = q.degree := by
  rcases lt_trichotomy p.degree q.degree with h | h | h
  · exact absurd (degree_sub_eq_right_of_degree_lt h ▸ hq) (lt_irrefl _)
  · exact h
  · exact absurd (degree_sub_eq_left_of_degree_lt h ▸ hp) (lt_irrefl _)

/-- If `p` is eventually nonnegative on `ℕ` and eventually bounded above by `q` there, then
`p.degree ≤ q.degree`. This is `HilbertSamuel.poly_cmp` at `c = 0`, whose hypothesis `q ≠ 0` is
supplied by the degenerate case: if `q = 0` the two bounds force `p = 0` as well. -/
private lemma degree_le_of_eventually_eval_le {p q : ℚ[X]}
    (hp : ∀ᶠ n : ℕ in atTop, 0 ≤ p.eval (n : ℚ))
    (h : ∀ᶠ n : ℕ in atTop, p.eval (n : ℚ) ≤ q.eval (n : ℚ)) : p.degree ≤ q.degree := by
  rcases eq_or_ne q 0 with rfl | hq
  · refine le_of_eq (congrArg Polynomial.degree (eq_of_eventually_eval_natCast_eq ?_))
    filter_upwards [hp, h] with n h1 h2
    simp only [eval_zero] at h2 ⊢
    linarith
  · refine poly_cmp p q 0 ?_ hq (nonneg_leadingCoeff_of_eventually_nonneg p hp)
    filter_upwards [h] with n hn
    linarith

/-! ### Computing polynomials for the Hilbert–Samuel function -/

variable {R : Type*} [CommRing R]

/-- `Computes I N P` says that the rational polynomial `P` computes the Hilbert–Samuel function
`n ↦ length_R (N / I^{n+1} N)` at all large `n`. This is the hypothesis shape of Tags 00K8,
00K9 and 00KA. -/
@[ega "0 16.2.1"]
private def Computes (I : Ideal R) (N : Type*) [AddCommGroup N] [Module R N] (P : ℚ[X]) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
    Module.length R (N ⧸ (I ^ (n + 1) • (⊤ : Submodule R N))) = p ∧ P.eval (n : ℚ) = (p : ℚ)

variable {I : Ideal R} {N : Type*} [AddCommGroup N] [Module R N] {P Q : ℚ[X]}

/-- A computing polynomial takes the value `χ_{I,N}(n)` at all large `n`. -/
private lemma Computes.isHilbertSamuelPoly (h : Computes I N P) :
    IsHilbertSamuelPoly I N P := by
  filter_upwards [h] with n hn
  obtain ⟨p, hp1, hp2⟩ := hn
  rw [hp2, hilbertSamuelFunction, hp1]
  simp

/-- The backward shift `P(X - c)` of a computing polynomial computes the shifted Hilbert–Samuel
function `n ↦ length_R (N / I^{n-c+1} N)` at all large `n`. -/
private lemma Computes.eventually_shift (h : Computes I N P) (c : ℕ) :
    ∀ᶠ n : ℕ in atTop, c ≤ n ∧ ∃ p : ℕ,
      Module.length R (N ⧸ (I ^ (n - c + 1) • (⊤ : Submodule R N))) = p ∧
        (P.comp (X - C (c : ℚ))).eval (n : ℚ) = p := by
  filter_upwards [(tendsto_sub_atTop_nat c).eventually h, eventually_ge_atTop c]
    with n ⟨p, hp, he⟩ hge
  refine ⟨hge, p, hp, ?_⟩
  rw [eval_comp, eval_sub, eval_X, eval_C, ← Nat.cast_sub hge]
  exact he

private lemma Computes.eventually_nonneg (h : Computes I N P) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ) := by
  filter_upwards [h] with n ⟨p, _, hp⟩
  rw [hp]; positivity

private lemma Computes.eventually_eval_comp_nonneg (h : Computes I N P) (c : ℕ) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ (P.comp (X - C (c : ℚ))).eval (n : ℚ) := by
  filter_upwards [h.eventually_shift c] with n ⟨_, p, _, hp⟩
  rw [hp]; positivity

private lemma Computes.leadingCoeff_nonneg (h : Computes I N P) : 0 ≤ P.leadingCoeff :=
  nonneg_leadingCoeff_of_eventually_nonneg P h.eventually_nonneg

/-- A computing polynomial is unique: two polynomials agreeing at all large naturals agree. -/
private lemma Computes.unique (hP : Computes I N P) (hQ : Computes I N Q) : P = Q := by
  refine eq_of_eventually_eval_natCast_eq ?_
  filter_upwards [hP.isHilbertSamuelPoly, hQ.isHilbertSamuelPoly] with n h1 h2
  rw [h1, h2]

/-- Definition 00KA reads `Ideal.hilbertSamuelDegree I N` off a computing polynomial chosen by
`Classical.choose`; by uniqueness it is the degree of *any* computing polynomial. -/
private lemma hilbertSamuelDegree_eq_degree (h : Computes I N P) :
    I.hilbertSamuelDegree N = P.degree := by
  have hex : ∃ Q : ℚ[X], ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
      Module.length R (N ⧸ (I ^ (n + 1) • (⊤ : Submodule R N))) = p ∧
        Q.eval (n : ℚ) = (p : ℚ) := ⟨P, h⟩
  rw [Ideal.hilbertSamuelDegree, dite_eq_left hex]
  exact congrArg Polynomial.degree (Computes.unique hex.choose_spec h)

/-- **Proposition 00K8.** The Hilbert–Samuel function of a finite module over a Noetherian local
ring is computed by a rational polynomial: the binomial-basis presentation of Tag 00K8 becomes a
polynomial through the binomial polynomials `X choose i`. -/
@[ega "0 16.2.1" "special case"]
private lemma exists_computes [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I.radical = maximalIdeal R) (N : Type*) [AddCommGroup N] [Module R N]
    [Module.Finite R N] : ∃ P : ℚ[X], Computes I N P := by
  obtain ⟨r, _a, b, hab⟩ :=
    Ideal.exists_eventually_length_quotient_smul_pow_eq_sum_choose_mul I hI N
  refine ⟨∑ i ∈ Finset.range (r + 1), C (b i : ℚ) *
    Stacks.HilbertFunction.PolynomialQuotient.binomialPoly i,
    hab.mono fun n hn => ?_⟩
  obtain ⟨q, hq1, hq2⟩ := hn.2
  refine ⟨q, hq1, ?_⟩
  simp only [eval_finsetSum, eval_mul, eval_C,
    Stacks.HilbertFunction.PolynomialQuotient.binomialPoly_eval,
    Ring.choose_natCast]
  rw [show ((q : ℚ)) = ((q : ℤ) : ℚ) by push_cast; ring, hq2]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Comparison of the three Hilbert–Samuel functions -/

section Exact

variable {M' M M'' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup M] [Module R M]
  [AddCommGroup M''] [Module R M''] {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}

/-- The short exact sequence `0 → M'/(M' ∩ I^{n+1}M) → M/I^{n+1}M → M''/I^{n+1}M'' → 0`
induced by `0 → M' → M → M'' → 0`. -/
private lemma length_quotient_eq_add (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (I : Ideal R) (n : ℕ) :
    Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))
      = Module.length R (M' ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)).comap f)
        + Module.length R (M'' ⧸ (I ^ (n + 1) • (⊤ : Submodule R M''))) := by
  have h := StacksHelpers.length_quotient_ses f g hg hfg (I ^ (n + 1) • (⊤ : Submodule R M))
  rwa [StacksHelpers.map_pow_smul_top I g hg] at h

/-- `χ_{I,M}(n) ≤ χ_{I,M'}(n) + χ_{I,M''}(n)`: the submodule `M'/(M' ∩ I^{n+1}M)` of
`M/I^{n+1}M` is a quotient of `M'/I^{n+1}M'`. -/
private lemma length_le_add (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (I : Ideal R) (n : ℕ) :
    Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))
      ≤ Module.length R (M' ⧸ (I ^ (n + 1) • (⊤ : Submodule R M')))
        + Module.length R (M'' ⧸ (I ^ (n + 1) • (⊤ : Submodule R M''))) := by
  rw [length_quotient_eq_add hg hfg I n]
  refine add_le_add (length_quotient_antitone ?_) le_rfl
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact smul_mono_right _ le_top

/-- `χ_{I,M''}(n) ≤ χ_{I,M}(n)`: `M''/I^{n+1}M''` is a quotient of `M/I^{n+1}M`. -/
private lemma length_le_of_exact (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (I : Ideal R) (n : ℕ) :
    Module.length R (M'' ⧸ (I ^ (n + 1) • (⊤ : Submodule R M'')))
      ≤ Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) := by
  rw [length_quotient_eq_add hg hfg I n]
  exact le_add_self

/-- **Artin–Rees (Lemma 00IN).** There is a shift `c` with `χ_{I,M'}(n - c) ≤ χ_{I,M}(n)` for
all `n ≥ c`: the filtration induced on `M'` by the powers of `I` on `M` is squeezed between
`I^{n+1}M'` and `I^{n+1-c}M'`. -/
private lemma exists_length_shift_le [IsNoetherianRing R] [Module.Finite R M]
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (I : Ideal R) :
    ∃ c : ℕ, ∀ n ≥ c,
      Module.length R (M' ⧸ (I ^ ((n - c) + 1) • (⊤ : Submodule R M')))
        ≤ Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) := by
  obtain ⟨c, hc⟩ := StacksHelpers.comap_pow_smul_eq I f hf
  refine ⟨c, fun n hn => ?_⟩
  rw [length_quotient_eq_add hg hfg I n]
  refine le_trans (length_quotient_antitone ?_) le_self_add
  rw [hc (n + 1) (by omega), show n + 1 - c = (n - c) + 1 from by omega]
  exact smul_mono_right _ le_top

/-! ### The comparisons at the level of the computing polynomials -/

variable {P' P P'' : ℚ[X]}

/-- `χ_{I,M} ≤ χ_{I,M'} + χ_{I,M''}` for the computing polynomials. -/
private lemma eventually_eval_le_add (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hP' : Computes I M' P') (hP : Computes I M P) (hP'' : Computes I M'' P'') :
    ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ (P' + P'').eval (n : ℚ) := by
  filter_upwards [hP, hP', hP''] with n ⟨p, hp, he⟩ ⟨p', hp', he'⟩ ⟨p'', hp'', he''⟩
  rw [eval_add, he, he', he'']
  have h := length_le_add hg hfg I n
  rw [hp, hp', hp''] at h
  exact_mod_cast h

/-- `χ_{I,M''} ≤ χ_{I,M}` for the computing polynomials. -/
private lemma eventually_eval_le (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hP : Computes I M P) (hP'' : Computes I M'' P'') :
    ∀ᶠ n : ℕ in atTop, P''.eval (n : ℚ) ≤ P.eval (n : ℚ) := by
  filter_upwards [hP, hP''] with n ⟨p, hp, he⟩ ⟨p'', hp'', he''⟩
  rw [he, he'']
  have h := length_le_of_exact hg hfg I n
  rw [hp, hp''] at h
  exact_mod_cast h

/-- **Artin–Rees** for the computing polynomials: `χ_{I,M'}(X - c) ≤ χ_{I,M}` eventually. -/
private lemma exists_eventually_eval_comp_le [IsNoetherianRing R] [Module.Finite R M]
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hP' : Computes I M' P') (hP : Computes I M P) :
    ∃ c : ℕ, ∀ᶠ n : ℕ in atTop, (P'.comp (X - C (c : ℚ))).eval (n : ℚ) ≤ P.eval (n : ℚ) := by
  obtain ⟨c, hc⟩ := exists_length_shift_le hf hg hfg I
  refine ⟨c, ?_⟩
  filter_upwards [hP'.eventually_shift c, hP] with n ⟨hge, p', hp', he'⟩ ⟨p, hp, he⟩
  rw [he', he]
  have h := hc n hge
  rw [hp, hp'] at h
  exact_mod_cast h

/-- **Lemma 00K6 at the level of the computing polynomials.** A submodule `N ⊆ M'` of colength
`l` and a shift `c` with `χ_{I,M}(n) = χ_{I,M''}(n) + χ_{I,N}(n - c) + l` for all `n ≥ c` give
the identity `χ_{I,M} = χ_{I,M''} + χ_{I,N}(X - c) + l` of polynomials. -/
private lemma eq_add_comp_add_C_of_charFn_eq (c l : ℕ)
    (hchi : ∀ n ≥ c, charFn R I M n = charFn R I M'' n + charFn R I N (n - c) + (l : ℕ∞))
    (hP : Computes I M P) (hP'' : Computes I M'' P'') (hQ : Computes I N Q) :
    P = P'' + Q.comp (X - C (c : ℚ)) + C (l : ℚ) := by
  refine eq_of_eventually_eval_natCast_eq ?_
  filter_upwards [hP, hP'', hQ.eventually_shift c]
    with n ⟨p, hp, he⟩ ⟨p'', hp'', he''⟩ ⟨hge, q, hq, heq⟩
  rw [eval_add, eval_add, eval_C, he, he'', heq]
  have h := hchi n hge
  simp only [charFn] at h
  rw [hp, hp'', hq] at h
  exact_mod_cast h

/-! ### The two parts of the lemma -/

/-- **Part (2).** The degree of `χ_{I,M}` is the maximum of the degrees of `χ_{I,M'}` and
`χ_{I,M''}`. The three comparisons of Hilbert–Samuel functions bound `deg χ_{I,M}` above by
`deg (χ_{I,M'} + χ_{I,M''})` and below by each of `deg χ_{I,M'}` and `deg χ_{I,M''}`, and the
leading coefficients of `χ_{I,M'}` and `χ_{I,M''}` are nonnegative, so the upper bound is the
maximum of the two degrees. -/
private lemma degree_max_eq [IsNoetherianRing R] [Module.Finite R M] (I : Ideal R)
    (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hP' : Computes I M' P') (hP : Computes I M P) (hP'' : Computes I M'' P'') :
    max P'.degree P''.degree = P.degree := by
  refine le_antisymm (max_le ?_ ?_) ?_
  · obtain ⟨c, hc⟩ := exists_eventually_eval_comp_le hf hg hfg hP' hP
    rw [← degree_comp_X_sub_C P' (c : ℚ)]
    exact degree_le_of_eventually_eval_le (hP'.eventually_eval_comp_nonneg c) hc
  · exact degree_le_of_eventually_eval_le hP''.eventually_nonneg
      (eventually_eval_le hg hfg hP hP'')
  · calc P.degree ≤ (P' + P'').degree :=
          degree_le_of_eventually_eval_le hP.eventually_nonneg
            (eventually_eval_le_add hg hfg hP' hP hP'')
      _ = max P'.degree P''.degree :=
          degree_add_eq_max_of_leadingCoeff_nonneg hP'.leadingCoeff_nonneg
            hP''.leadingCoeff_nonneg

/-- **Part (1).** If `M'` does not have finite length, the error `χ_{I,M} - χ_{I,M''} - χ_{I,M'}`
has degree strictly smaller than the degree of `χ_{I,M'}`. Writing `Q = χ_{I,N}` for the
submodule `N ⊆ M'` of Lemma 00K6, the error is `(Q(X - c) - Q) + ((Q - χ_{I,M'}) + l)`; the
first summand drops the degree by elementary calculus, the second by Lemma 00KB, and the third
is constant while `deg χ_{I,M'} > 0`. -/
private lemma degree_error_lt [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M']
    [Module.Finite R M] [Module.Finite R M''] (I : Ideal R) (hI : I.radical = maximalIdeal R)
    (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hM' : ¬ IsFiniteLength R M')
    (hP' : Computes I M' P') (hP : Computes I M P) (hP'' : Computes I M'' P'') :
    (P - P'' - P').degree < P'.degree := by
  have hM'len : ¬ HasFiniteLength R M' := fun hfin =>
    hM' (Module.length_ne_top_iff.mp (lt_top_iff_ne_top.mp hfin))
  have hpos : 0 < P'.degree := hsPoly_degree_pos I hI M' hM'len P' hP'.isHilbertSamuelPoly
  obtain ⟨N, c, l, hl, hchi, -⟩ :=
    additivity_of_characteristic_and_hilbert_functions R I hI M' M M'' f g hf hg hfg
  obtain ⟨Q, hQ⟩ := exists_computes I hI (N : Type _)
  obtain ⟨hlt1, hlt2⟩ := degree_sub_lt I hI M' hM'len N
    (show Module.length R (M' ⧸ N) < ⊤ from by rw [hl]; exact ENat.natCast_lt_top l)
    P' Q hP'.isHilbertSamuelPoly hQ.isHilbertSamuelPoly
  have hdeg : Q.degree = P'.degree := (degree_eq_of_degree_sub_lt hlt1 hlt2).symm
  have hQ0 : Q ≠ 0 := by rw [Ne, ← degree_eq_bot, hdeg]; exact ne_bot_of_gt hpos
  have hsplit : P - P'' - P' = Q.comp (X - C (c : ℚ)) - Q + ((Q - P') + C (l : ℚ)) := by
    rw [eq_add_comp_add_C_of_charFn_eq c l hchi hP hP'' hQ]; ring
  rw [hsplit]
  refine (degree_add_le _ _).trans_lt (max_lt ?_ ((degree_add_le _ _).trans_lt (max_lt ?_ ?_)))
  · rw [← hdeg]; exact degree_comp_X_sub_C_sub_lt hQ0 _
  · rw [show Q - P' = -(P' - Q) from by ring, degree_neg]; exact hlt1
  · exact degree_C_le.trans_lt hpos

end Exact

/-! ### The lemma -/

/-- For a short exact sequence `0 → M' → M → M'' → 0` of finite modules over a Noetherian local
ring and an ideal of definition `I`, polynomials computing the three Hilbert–Samuel functions
satisfy the degree bound and the degree equality, and the Hilbert–Samuel degrees satisfy
`max (d(M'), d(M'')) = d(M)`. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = maximalIdeal R)
    {M' M M'' : Type*} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    {f : M' →ₗ[R] M} {g : M →ₗ[R] M''} (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    (∀ P' P P'' : ℚ[X],
      (∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
          Module.length R (M' ⧸ (I ^ (n + 1) • (⊤ : Submodule R M'))) = p ∧
            P'.eval (n : ℚ) = (p : ℚ)) →
        (∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
          Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = p ∧
            P.eval (n : ℚ) = (p : ℚ)) →
        (∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
          Module.length R (M'' ⧸ (I ^ (n + 1) • (⊤ : Submodule R M''))) = p ∧
            P''.eval (n : ℚ) = (p : ℚ)) →
        (¬ IsFiniteLength R M' → (P - P'' - P').degree < P'.degree) ∧
          max P'.degree P''.degree = P.degree) ∧
      max (I.hilbertSamuelDegree M') (I.hilbertSamuelDegree M'') =
        I.hilbertSamuelDegree M := by
  refine ⟨fun P' P P'' hP' hP hP'' =>
    ⟨fun hM' => degree_error_lt I hI hfg hf hg hM' hP' hP hP'',
      degree_max_eq I hfg hf hg hP' hP hP''⟩, ?_⟩
  obtain ⟨P', hP'⟩ := exists_computes I hI M'
  obtain ⟨P, hP⟩ := exists_computes I hI M
  obtain ⟨P'', hP''⟩ := exists_computes I hI M''
  rw [hilbertSamuelDegree_eq_degree hP', hilbertSamuelDegree_eq_degree hP'',
    hilbertSamuelDegree_eq_degree hP]
  exact degree_max_eq I hfg hf hg hP' hP hP''

end Stacks.HilbertSamuel.ShortExactDegree

end

/-!
# The Hilbert–Samuel degree in a short exact sequence of finite modules

Let `(R, m)` be a Noetherian local ring, let `I ⊆ R` be an ideal of definition, that is an
ideal with `√I = m`, and let `0 → M' → M → M'' → 0` be a short exact sequence of finite
`R`-modules. Every finite `R`-module annihilated by a power of `I` has finite length, so

`χ_{I,N}(n) = length_R (N / I ^ (n + 1) N)`

is a well-defined function `ℕ → ℕ` for each of `N = M'`, `M`, `M''`, and it is a numerical
polynomial (Proposition 00K8). These three functions are not additive: `χ_{I,M}` is not
`χ_{I,M'} + χ_{I,M''}`, because the filtration induced on `M'` by the powers of `I` on `M` is
in general coarser than the filtration of `M'` by the powers of `I`. They are additive to
leading order, however: unless `M'` has finite length, the error
`χ_{I,M} - χ_{I,M''} - χ_{I,M'}` has degree strictly smaller than the degree of `χ_{I,M'}`.
Since the leading coefficients of `χ_{I,M'}` and `χ_{I,M''}` are nonnegative, the degree of
`χ_{I,M}` is therefore the maximum of the degrees of `χ_{I,M'}` and `χ_{I,M''}`; for `I = m`
this is the same statement for the invariant `d(-)` of Definition 00KA.

## Main results

* `Ideal.max_degree_eq_degree_of_exact`: the three assertions of Lemma 00KC — the degree bound
  on the error `χ_{I,M} - χ_{I,M''} - χ_{I,M'}`, and the equality
  `max {deg χ_{I,M'}, deg χ_{I,M''}} = deg χ_{I,M}`, both for the polynomials computing the
  three Hilbert–Samuel functions and for the invariant `Ideal.hilbertSamuelDegree`, whose case
  `I = m` is the equality `max {d(M'), d(M'')} = d(M)`.

## Implementation notes

The short exact sequence is spelled as in the companion statements Stacks 00LX
(`Module.min_depth_le_depth_of_exact`) and 0B51 (`Module.supportDim_of_exact`): an exact pair
of `R`-linear maps `f : M' →ₗ[R] M`, `g : M →ₗ[R] M''` with `f` injective and `g` surjective,
rather than a `CategoryTheory.ShortComplex (ModuleCat R)`. All three modules are assumed
finite, as in the source, although over the Noetherian ring `R` finiteness of `M'` and of `M''`
already follows from that of `M`.

Neither Mathlib nor this project has a type of numerical polynomials, so the numerical
polynomials `χ_{I,M'}`, `χ_{I,M}`, `χ_{I,M''}` of parts (1) and (2) are presented, as in
`Ideal.exists_degree_eq_of_eventually_eval_eq_length_quotient_smul_pow` (Tag 00K9), by rational
polynomials `P'`, `P`, `P''` computing them at all large `n`. Such polynomials exist by
Proposition 00K8 and are unique, since two polynomials agreeing at all large naturals agree at
infinitely many rationals (`Polynomial.eq_of_infinite_eval_eq`), so `P'.degree`, `P.degree` and
`P''.degree` are the degrees of the three numerical polynomials. The error term of part (1) is
then the polynomial `P - P'' - P'`; that it is again a numerical polynomial is inherited from
the hypotheses, since it computes `χ_{I,M} - χ_{I,M''} - χ_{I,M'}` at all large `n` and that
function takes integer values there, so the content of part (1) is the degree bound. Degrees
are compared in `WithBot ℕ`, where `⊥ = -∞` is the degree of the zero polynomial, so `max` and
`<` are those of the source's `{-∞, 0, 1, 2, …}` and part (2) includes the degenerate cases in
which one of the three modules vanishes.

The three polynomials are quantified *inside* the conjunct that mentions them, not by the
theorem: the last conjunct is an equality of Hilbert–Samuel degrees, mentioning no polynomial,
and a user of it should not have to produce three polynomials computing `χ_{I,M'}`, `χ_{I,M}`
and `χ_{I,M''}` — that is Proposition 00K8 rather than boilerplate — before applying it. That
last conjunct is part (2) again, for the invariant `Ideal.hilbertSamuelDegree` of Definition
00KA in place of a chosen computing polynomial; passing from one form to the other is the
characterisation of that invariant, which is not available as a lemma, so both forms are
asserted. Part (3) of the source is its case `I = m`: `Module.hilbertSamuelDegree R N`, the
`d(N)` of Definition 00KA, is by definition `(maximalIdeal R).hilbertSamuelDegree N`, and the
hypothesis `hI` is then `Ideal.IsPrime.radical inferInstance`, so part (3) needs no separate
statement — the last conjunct at `I = maximalIdeal R` *is* `max {d(M'), d(M'')} = d(M)`, up to
unfolding a reducible abbreviation.

Being an ideal of definition (Tag 07DU) is spelled `I.radical = IsLocalRing.maximalIdeal R`,
and `I ^ n N` as `I ^ n • (⊤ : Submodule R N)`; finiteness of the lengths is carried inside the
hypotheses on the polynomials, in the shape
`∃ p : ℕ, Module.length R … = p ∧ P.eval (n : ℚ) = p`, rather than behind `ENat.toNat`. Both
are the spellings of `Ideal.exists_eventually_length_quotient_smul_pow_eq_sum_choose_mul`
(Tag 00K8). "Does not have finite length" is `¬ IsFiniteLength R M'`. The equality of degrees is
oriented as the source writes it, with the maximum on the left; `Module.supportDim_of_exact`
puts the middle module on the left instead.

Faithfulness. (1) Every hypothesis is used by the conclusion: `I` and `hI` by both conjuncts
(the last one through `Ideal.hilbertSamuelDegree I`), and `hfg`, `hf`, `hg` by both. Without
`hI` the lengths are infinite, so the hypotheses on `P'`, `P`, `P''` are unsatisfiable rather
than vacuous — over `R = k[[x, y]]` with `I = (x)` and `M = R` one has
`length_R (M / I ^ (n + 1) M) = ⊤` — and `IsNoetherianRing R` together with the finiteness
hypotheses is what makes them satisfiable, finiteness also entering part (2) through
Artin–Rees. Each of `hfg`, `hf`, `hg` is needed for part (2), already over `R = k[[x]]` with
`I = m`: dropping `hfg`, take `M' = M'' = 0` and `M = R` with `f = 0`, `g = 0`, where `f` is
injective and `g` is surjective but `max {-∞, -∞} = -∞ ≠ 1`; dropping `hf`, take `M' = R` and
`M = M'' = 0`, where the pair is exact and `g` is surjective but `max {1, -∞} = 1 ≠ -∞`;
dropping `hg`, take `M'' = R` and `M' = M = 0`, where the pair is exact and `f` is injective
but `max {-∞, 1} = 1 ≠ -∞`. The hypothesis `¬ IsFiniteLength R M'` of part (1) is load-bearing
at `M' = 0`, where `P' = 0` and the error term is `0`, so that the conclusion would read
`-∞ < -∞`. (2) The scalars and base are the source's: all lengths are lengths of `R`-modules,
not of modules over `R / I` or over the associated graded ring `⨁_d I ^ d / I ^ (d + 1)`; `f`
and `g` are `R`-linear; and the comparison polynomials have rational coefficients evaluated at
the rational cast of `n`, as in the source's `ℚ[t]`. (3) The source names the three numerical
polynomials and the invariant `d(-)`, and all four are pinned: the polynomials by the
hypotheses that they compute the three functions at all large `n`, which determines them, and
`d(-)` by Definition 00KA; the sequence too is pinned, by the maps `f` and `g` carrying the
hypotheses, rather than asserted to exist. (4) The instantiation is not degenerate: for
`R = k[[x, y]]`, `I = m` and the sequence `0 → R →(·x) R → R/xR → 0` one has
`χ_{I,M'}(n) = χ_{I,M}(n) = binom(n + 2, 2)` and `χ_{I,M''}(n) = n + 1`, so `M'` does not have
finite length, the error term `P - P'' - P' = -(t + 1)` of part (1) has degree `1 < 2`, part (2)
reads `max {2, 1} = 2` and part (3) reads `max {2, 1} = 2`.

## References

* [Stacks Project, Tag 00KC](https://stacks.math.columbia.edu/tag/00KC)

## Tags

Hilbert–Samuel function, numerical polynomial, degree, short exact sequence, ideal of definition
-/

open Filter IsLocalRing Polynomial in
/-- **Stacks 00KC.** Let `R` be a Noetherian local ring, let `I ⊆ R` be an ideal of definition
(`I.radical` is the maximal ideal of `R`) and let `0 → M' → M → M'' → 0` be a short exact
sequence of finite `R`-modules, given by `f : M' →ₗ[R] M` injective, `g : M →ₗ[R] M''`
surjective and `Function.Exact f g`. Then

1. if `M'` does not have finite length, then `χ_{I,M} - χ_{I,M''} - χ_{I,M'}` is a numerical
   polynomial of degree `<` the degree of `χ_{I,M'}`,
2. `max {deg χ_{I,M'}, deg χ_{I,M''}} = deg χ_{I,M}`, and
3. `max {d(M'), d(M'')} = d(M)`, for the invariant `d(-)` of Definition 00KA — the case
   `I = m` of the last conjunct, since `d(N) = (maximalIdeal R).hilbertSamuelDegree N`.

Here `P'`, `P`, `P''` are the numerical polynomials `χ_{I,M'}`, `χ_{I,M}`, `χ_{I,M''}`, that is,
the polynomials with `P'(n) = length_R (M' / I ^ (n + 1) M')` for all `n ≫ 0` and likewise for
`M` and `M''`, and `Ideal.hilbertSamuelDegree I N` is the degree of `χ_{I,N}`. -/
@[stacks 00KC "The first conjunct is parts (1) and (2) of the tag, for polynomials computing the
three Hilbert–Samuel functions as in Tags 00K8 and 00K9, so `χ_{I,M} - χ_{I,M''} - χ_{I,M'}` is
`P - P'' - P'`; that this is again a numerical polynomial is inherited from the hypotheses on
the three polynomials, and the degree bound is the content. The second conjunct is part (2) for
the invariant of Definition 00KA, and part (3) of the tag is its case `I = maximalIdeal R`. See
the module docstring.", ega "0 16.2.2.2" "(1) deg bound, (2)"]
public theorem Ideal.max_degree_eq_degree_of_exact
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = maximalIdeal R)
    {M' M M'' : Type*} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    {f : M' →ₗ[R] M} {g : M →ₗ[R] M''} (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    (∀ P' P P'' : ℚ[X],
      (∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
          Module.length R (M' ⧸ (I ^ (n + 1) • (⊤ : Submodule R M'))) = p ∧
            P'.eval (n : ℚ) = (p : ℚ)) →
        (∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
          Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = p ∧
            P.eval (n : ℚ) = (p : ℚ)) →
        (∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
          Module.length R (M'' ⧸ (I ^ (n + 1) • (⊤ : Submodule R M''))) = p ∧
            P''.eval (n : ℚ) = (p : ℚ)) →
        (¬ IsFiniteLength R M' → (P - P'' - P').degree < P'.degree) ∧
          max P'.degree P''.degree = P.degree) ∧
      max (I.hilbertSamuelDegree M') (I.hilbertSamuelDegree M'') =
        I.hilbertSamuelDegree M :=
          by exact Stacks.HilbertSamuel.ShortExactDegree.solution (g := g) (f := f) I hI hfg hf hg
