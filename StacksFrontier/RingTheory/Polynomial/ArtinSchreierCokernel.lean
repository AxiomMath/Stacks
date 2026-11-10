module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Perfect

/-!
# The cokernel of `f ↦ f ^ p - f` on a polynomial ring

Let `k` be a field of characteristic `p > 0`. The map `f ↦ f ^ p - f` on `k[x]` is additive, and
its cokernel is described by a set of representatives:

* if `k` is algebraically closed, the polynomials `∑_{p ∤ n} λₙ xⁿ` (no coefficient in a degree
  divisible by `p`, the degree `0` included) form a set of representatives;
* if `k` is only perfect, one has to allow constants as well: every class is represented by a
  polynomial `∑_{p ∤ n} λₙ xⁿ + c`, and two of these represent the same class exactly when their
  non-constant coefficients agree and their constant terms differ by an element `a ^ p - a` of `k`.

## Main definitions

* `Stacks.ArtinSchreier.ringArtinSchreier R p`: the additive map `f ↦ f ^ p - f` of a commutative
  ring `R` of characteristic `p`.

## Main results

* `Polynomial.existsUnique_sub_mem_range_ringArtinSchreier`: the representatives over an
  algebraically closed field.
* `Polynomial.exists_sub_mem_range_ringArtinSchreier_of_perfectRing` and the criterion beside it:
  the representatives over a perfect field.
* `Polynomial.not_exists_sub_mem_range_ringArtinSchreier_of_not_pth_power`: over an imperfect
  field the second description fails, so perfectness is what the parenthetical case needs.

## References

* [Stacks Project, Tag 0A47](https://stacks.math.columbia.edu/tag/0A47)
-/

@[expose] public section

open Polynomial

namespace Stacks.ArtinSchreier

variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- **The Artin–Schreier map** `f ↦ f ^ p - f` of a commutative ring of characteristic `p`, as an
additive map: the Frobenius minus the identity. -/
noncomputable def ringArtinSchreier : R →+ R :=
  (frobenius R p : R →+* R).toAddMonoidHom - AddMonoidHom.id R

@[simp]
theorem ringArtinSchreier_apply (f : R) : ringArtinSchreier R p f = f ^ p - f :=
  rfl

end Stacks.ArtinSchreier

namespace Polynomial

open Stacks.ArtinSchreier

variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]

/-- The coefficient of `X ^ (p * m)` in `u ^ p` is the `p`-th power of the coefficient of
`X ^ m` in `u`. -/
theorem coeff_pow_char_mul (u : k[X]) (m : ℕ) : (u ^ p).coeff (p * m) = u.coeff m ^ p := by
  rw [← map_frobenius_expand, coeff_map, coeff_expand hp.out.pos, ite_eq_left (dvd_mul_right p m),
    Nat.mul_div_cancel_left m hp.out.pos]
  rfl

/-- The coefficient of `u ^ p - u` in degree `p * deg u` is nonzero when `u` is not constant. -/
private theorem coeff_pow_char_sub_natDegree_ne_zero (u : k[X]) (hd : 0 < u.natDegree) :
    (u ^ p - u).coeff (p * u.natDegree) ≠ 0 := by
  have hlt : u.natDegree < p * u.natDegree := lt_mul_left hd hp.out.one_lt
  rw [coeff_sub, coeff_pow_char_mul, coeff_eq_zero_of_natDegree_lt hlt, sub_zero]
  have hu : u ≠ 0 := fun h0 => by simp [h0] at hd
  exact pow_ne_zero _ (leadingCoeff_ne_zero.mpr hu)

/-- **The values of `f ↦ f ^ p - f` that have no coefficient in a positive degree divisible by
`p` are constants.** If `u ^ p - u` has vanishing coefficients in every positive degree divisible
by `p`, then `u` is a constant: otherwise the leading coefficient of `u ^ p - u` sits in degree
`p * deg u`. -/
theorem eq_C_of_ringArtinSchreier_coeff_eq_zero (u : k[X])
    (h : ∀ n, 0 < n → p ∣ n → (u ^ p - u).coeff n = 0) : u = C (u.coeff 0) := by
  by_contra hne
  have hd : 0 < u.natDegree := by
    by_contra h0
    exact hne (eq_C_of_natDegree_eq_zero (by omega))
  exact coeff_pow_char_sub_natDegree_ne_zero u hd
    (h _ (Nat.mul_pos hp.out.pos hd) (dvd_mul_right p _))

/-- The polynomials with no coefficient in a degree divisible by `p`, as an additive subgroup. -/
def noCoeffDvdSubgroup (k : Type*) [Field k] (p : ℕ) : AddSubgroup k[X] where
  carrier := {f | ∀ n, p ∣ n → f.coeff n = 0}
  add_mem' {a b} ha hb n hn := by rw [coeff_add, ha n hn, hb n hn, add_zero]
  zero_mem' n _ := coeff_zero n
  neg_mem' {a} ha n hn := by rw [coeff_neg, ha n hn, neg_zero]

/-- The polynomials with no coefficient in a positive degree divisible by `p`, as an additive
subgroup. -/
def noCoeffPosDvdSubgroup (k : Type*) [Field k] (p : ℕ) : AddSubgroup k[X] where
  carrier := {f | ∀ n, 0 < n → p ∣ n → f.coeff n = 0}
  add_mem' {a b} ha hb n h0 hn := by rw [coeff_add, ha n h0 hn, hb n h0 hn, add_zero]
  zero_mem' n _ _ := coeff_zero n
  neg_mem' {a} ha n h0 hn := by rw [coeff_neg, ha n h0 hn, neg_zero]

/-- **Reduction of a monomial.** Over a perfect field of characteristic `p`, every polynomial is
congruent modulo the values of `f ↦ f ^ p - f` to one with no coefficient in a positive degree
divisible by `p`: the monomial `c X ^ (p * m)` is congruent to `c ^ (1 / p) X ^ m`. -/
theorem mem_sup_range_ringArtinSchreier_of_perfectRing [PerfectRing k p] (g : k[X]) :
    g ∈ noCoeffPosDvdSubgroup k p ⊔ (ringArtinSchreier k[X] p).range := by
  induction g using Polynomial.induction_on' with
  | add f g hf hg => exact add_mem hf hg
  | monomial n c =>
    induction n using Nat.strong_induction_on generalizing c with
    | _ n ih =>
    by_cases hn : 0 < n ∧ p ∣ n
    · obtain ⟨m, rfl⟩ := hn.2
      have hm : 0 < m := Nat.pos_of_mul_pos_left hn.1
      have hlt : m < p * m := lt_mul_left hm hp.out.one_lt
      let d : k := (frobeniusEquiv k p).symm c
      have hsub : monomial (p * m) c - monomial m d ∈ (ringArtinSchreier k[X] p).range :=
        ⟨monomial m d, by
          rw [ringArtinSchreier_apply, monomial_pow, mul_comm m p]
          congr 2
          exact frobeniusEquiv_symm_pow_p k p c⟩
      have := add_mem (ih m hlt d) (AddSubgroup.mem_sup_right hsub)
      rwa [add_sub_cancel] at this
    · refine AddSubgroup.mem_sup_left fun i hi hpi => ?_
      rw [coeff_monomial, ite_eq_right]
      rintro rfl
      exact hn ⟨hi, hpi⟩

/-- **Uniqueness over a perfect field.** Two polynomials without coefficients in positive degrees
divisible by `p` are congruent modulo the values of `f ↦ f ^ p - f` exactly when their
non-constant coefficients agree and their constant terms differ by a value `a ^ p - a`. -/
theorem sub_mem_range_ringArtinSchreier_iff {f f' : k[X]} (hf : f ∈ noCoeffPosDvdSubgroup k p)
    (hf' : f' ∈ noCoeffPosDvdSubgroup k p) :
    f - f' ∈ (ringArtinSchreier k[X] p).range ↔
      (∀ n, n ≠ 0 → f.coeff n = f'.coeff n) ∧
        f.coeff 0 - f'.coeff 0 ∈ (ringArtinSchreier k p).range := by
  constructor
  · rintro ⟨u, hu⟩
    rw [ringArtinSchreier_apply] at hu
    have hgood : ∀ n, 0 < n → p ∣ n → (u ^ p - u).coeff n = 0 := fun n h0 hn => by
      rw [hu, coeff_sub, hf n h0 hn, hf' n h0 hn, sub_zero]
    have hC := eq_C_of_ringArtinSchreier_coeff_eq_zero u hgood
    rw [hC, ← C_pow, ← C_sub] at hu
    refine ⟨fun n hn => ?_, ⟨u.coeff 0, ?_⟩⟩
    · have := congrArg (coeff · n) hu
      simp only [coeff_C, ite_eq_right hn, coeff_sub] at this
      exact (sub_eq_zero.mp this.symm)
    · have := congrArg (coeff · 0) hu
      simpa only [coeff_C_zero, coeff_sub, ringArtinSchreier_apply] using this
  · rintro ⟨hn, a, ha⟩
    refine ⟨C a, ?_⟩
    ext n
    rw [ringArtinSchreier_apply, ← C_pow, ← C_sub, coeff_sub]
    rcases eq_or_ne n 0 with rfl | h0
    · rw [coeff_C_zero]
      exact ha
    · rw [coeff_C, ite_eq_right h0, hn n h0, sub_self]

/-- **[Stacks, Tag 0A47], the representatives of the cokernel.** Let `k` be an algebraically
closed field of characteristic `p > 0`. Every polynomial `g ∈ k[x]` is congruent modulo the image
of `f ↦ f ^ p - f` to exactly one polynomial `∑_{p ∤ n} λₙ xⁿ`, that is, to exactly one
polynomial with no coefficient in a degree divisible by `p` (the degree `0` included). In other
words these polynomials form a set of representatives for the cokernel of
`k[x] → k[x], f ↦ f ^ p - f`. -/
@[stacks 0A47 "the polynomials sum over p ∤ n of λ_n x^n represent the cokernel of f ↦ f^p - f"]
theorem existsUnique_sub_mem_range_ringArtinSchreier [IsAlgClosed k] (g : k[X]) :
    ∃! f : k[X], (∀ n, p ∣ n → f.coeff n = 0) ∧
      g - f ∈ (ringArtinSchreier k[X] p).range := by
  obtain ⟨f₀, hf₀, z, hz, hsum⟩ :=
    AddSubgroup.mem_sup.mp (mem_sup_range_ringArtinSchreier_of_perfectRing (p := p) g)
  -- remove the constant term of `f₀`, which is a value `a ^ p - a`
  have hdeg : (X ^ p - X - C (f₀.coeff 0) : k[X]).natDegree = p := by
    rw [sub_sub, natDegree_sub_eq_left_of_natDegree_lt] <;>
      rw [natDegree_X_pow]
    rw [natDegree_X_add_C]
    exact hp.out.one_lt
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (X ^ p - X - C (f₀.coeff 0)) fun h => by
    have := natDegree_eq_zero_iff_degree_le_zero.mpr h.le
    exact hp.out.ne_zero (hdeg.symm.trans this)
  have ha' : a ^ p - a = f₀.coeff 0 := by
    simpa [sub_eq_zero] using ha
  have hmem : g - (f₀ - C (f₀.coeff 0)) ∈ (ringArtinSchreier k[X] p).range := by
    rw [← hsum]
    have : f₀ + z - (f₀ - C (f₀.coeff 0)) = z + (C a ^ p - C a) := by
      rw [← C_pow, ← C_sub, ha']
      ring
    rw [this]
    exact add_mem hz ⟨C a, rfl⟩
  refine ⟨f₀ - C (f₀.coeff 0), ⟨fun n hn => ?_, hmem⟩, ?_⟩
  · rcases eq_or_ne n 0 with rfl | h0
    · rw [coeff_sub, coeff_C_zero, sub_self]
    · rw [coeff_sub, coeff_C, ite_eq_right h0, sub_zero]
      exact hf₀ n (Nat.pos_of_ne_zero h0) hn
  · rintro f ⟨hf, hg⟩
    have hf0 : f ∈ noCoeffPosDvdSubgroup k p := fun n _ hn => hf n hn
    have hf₁ : f₀ - C (f₀.coeff 0) ∈ noCoeffPosDvdSubgroup k p := fun n h0 hn => by
      rw [coeff_sub, coeff_C, ite_eq_right h0.ne', sub_zero]
      exact hf₀ n h0 hn
    have hdiff : f - (f₀ - C (f₀.coeff 0)) ∈ (ringArtinSchreier k[X] p).range := by
      have := sub_mem hmem hg
      rwa [sub_sub_sub_cancel_left] at this
    obtain ⟨hcoeff, -⟩ := (sub_mem_range_ringArtinSchreier_iff hf0 hf₁).mp hdiff
    ext n
    rcases eq_or_ne n 0 with rfl | h0
    · rw [hf 0 (dvd_zero p)]
      simp
    · exact hcoeff n h0

/-- **[Stacks, Tag 0A47], the parenthetical case of a field that is not algebraically closed.**
Let `k` be a perfect field of characteristic `p > 0`. Then the representatives of the cokernel of
`f ↦ f ^ p - f` on `k[x]` need constants added: every `g ∈ k[x]` is congruent to a polynomial
`∑_{p ∤ n} λₙ xⁿ + c`, and two such polynomials are congruent exactly when their coefficients
`λₙ` agree and their constant terms differ by a value `a ^ p - a` of `k`. So the constants needed
are a set of representatives of `k / {a ^ p - a}`, which is zero for algebraically closed `k`.

The source says "if `k` is not algebraically closed"; perfectness is needed and is assumed here:
over an imperfect field the description fails, by
`Polynomial.not_exists_sub_mem_range_ringArtinSchreier_of_not_pth_power`. -/
@[stacks 0A47 "if k is not algebraically closed, constants have to be added (k perfect)"]
theorem exists_sub_mem_range_ringArtinSchreier_of_perfectRing [PerfectRing k p] :
    (∀ g : k[X], ∃ f : k[X], (∀ n, 0 < n → p ∣ n → f.coeff n = 0) ∧
      g - f ∈ (ringArtinSchreier k[X] p).range) ∧
    ∀ f f' : k[X], (∀ n, 0 < n → p ∣ n → f.coeff n = 0) →
      (∀ n, 0 < n → p ∣ n → f'.coeff n = 0) →
      (f - f' ∈ (ringArtinSchreier k[X] p).range ↔
        (∀ n, n ≠ 0 → f.coeff n = f'.coeff n) ∧
          f.coeff 0 - f'.coeff 0 ∈ (ringArtinSchreier k p).range) := by
  refine ⟨fun g => ?_, fun f f' hf hf' => sub_mem_range_ringArtinSchreier_iff hf hf'⟩
  obtain ⟨f, hf, z, hz, hsum⟩ :=
    AddSubgroup.mem_sup.mp (mem_sup_range_ringArtinSchreier_of_perfectRing (p := p) g)
  refine ⟨f, hf, ?_⟩
  rw [← hsum, add_sub_cancel_left]
  exact hz

/-- **Perfectness cannot be dropped from the parenthetical case.** If `t ∈ k` is not a `p`-th
power, then `t xᵖ` is not congruent modulo the values of `f ↦ f ^ p - f` to any polynomial without
coefficients in positive degrees divisible by `p`. -/
theorem not_exists_sub_mem_range_ringArtinSchreier_of_not_pth_power {t : k}
    (ht : ∀ s : k, s ^ p ≠ t) :
    ¬ ∃ f : k[X], (∀ n, 0 < n → p ∣ n → f.coeff n = 0) ∧
      C t * X ^ p - f ∈ (ringArtinSchreier k[X] p).range := by
  rintro ⟨f, hf, u, hu⟩
  rw [ringArtinSchreier_apply] at hu
  have hp1 := hp.out.one_lt
  -- the coefficient of `u ^ p - u` in degree `p * m`
  have hc : ∀ m, u.coeff m ^ p - u.coeff (p * m) = (C t * X ^ p - f).coeff (p * m) := fun m => by
    rw [← hu, coeff_sub, coeff_pow_char_mul]
  -- in the degrees `p ^ (j + 1)`, `j ≥ 1`, the coefficients of `u` are `p`-th powers
  have hrec : ∀ j, 1 ≤ j → u.coeff (p ^ (j + 1)) = u.coeff (p ^ j) ^ p := fun j hj => by
    have h := hc (p ^ j)
    have hne : p * p ^ j ≠ p :=
      (lt_mul_right hp.out.pos (Nat.one_lt_pow (by omega) hp1)).ne'
    rw [coeff_sub, coeff_C_mul_X_pow, ite_eq_right hne, hf _ (by positivity) (dvd_mul_right _ _),
      sub_zero, sub_eq_zero] at h
    rw [pow_succ', h]
  have hvan : ∀ j, 1 ≤ j → u.coeff (p ^ j) = 0 := by
    intro j hj
    by_contra h0
    have hall : ∀ i, u.coeff (p ^ (j + i)) ≠ 0 := by
      intro i
      induction i with
      | zero => simpa using h0
      | succ i ih =>
        rw [← add_assoc, hrec _ (by omega)]
        exact pow_ne_zero p ih
    apply hall u.natDegree
    apply coeff_eq_zero_of_natDegree_lt
    calc u.natDegree < p ^ u.natDegree := Nat.lt_pow_self hp1
      _ ≤ p ^ (j + u.natDegree) := Nat.pow_le_pow_right hp.out.pos (by omega)
  have h1 := hc 1
  rw [mul_one, coeff_sub, coeff_C_mul_X_pow, ite_eq_left rfl, hf p hp.out.pos dvd_rfl, sub_zero,
    show u.coeff p = u.coeff (p ^ 1) by rw [pow_one], hvan 1 le_rfl, sub_zero] at h1
  exact ht _ h1

/-- **A rescaled Artin–Schreier value `c (xᵖ - x)` is a value only for `c ∈ 𝐅_p`.** If
`w ^ p - w = c (xᵖ - x)` in `k[x]`, then `c ^ p = c`: comparing leading terms forces `w` to have
degree at most one, and then the coefficients of `x` and of `xᵖ` give `w₁ = c` and `w₁ ^ p = c`. -/
theorem pow_eq_self_of_ringArtinSchreier_eq_C_mul (w : k[X]) (c : k)
    (h : w ^ p - w = C c * (X ^ p - X)) : c ^ p = c := by
  have hp1 := hp.out.one_lt
  have hR : ∀ n, n ≠ p → n ≠ 1 → (C c * (X ^ p - X)).coeff n = 0 := fun n h₁ h₂ => by
    rw [coeff_C_mul, coeff_sub, coeff_X_pow, coeff_X, ite_eq_right h₁, ite_eq_right (Ne.symm h₂),
      sub_zero, mul_zero]
  -- `w` has degree at most one
  have hdeg : w.natDegree ≤ 1 := by
    by_contra hd
    push Not at hd
    have h₁ : p * w.natDegree ≠ p := (lt_mul_right hp.out.pos hd).ne'
    have h₂ : p * w.natDegree ≠ 1 := by nlinarith
    exact coeff_pow_char_sub_natDegree_ne_zero w (by omega) (by rw [h]; exact hR _ h₁ h₂)
  -- the coefficient of `x`
  have hcoeff1 : w.coeff 1 = c := by
    have hc := congrArg (coeff · 1) h
    have hpow : (w ^ p).coeff 1 = 0 := by
      rw [← map_frobenius_expand, coeff_map, coeff_expand hp.out.pos, ite_eq_right, map_zero]
      exact fun hd => hp1.ne' (Nat.dvd_one.mp hd)
    rw [coeff_sub, hpow, zero_sub, coeff_C_mul, coeff_sub, coeff_X_pow, ite_eq_right hp1.ne,
      coeff_X_one, zero_sub, mul_neg, mul_one, neg_inj] at hc
    exact hc
  -- the coefficient of `xᵖ`
  have hc := congrArg (coeff · (p * 1)) h
  rw [coeff_sub, coeff_pow_char_mul, hcoeff1, mul_one,
    coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hp1), sub_zero, coeff_C_mul, coeff_sub,
    coeff_X_pow, ite_eq_left rfl, coeff_X, ite_eq_right hp1.ne, sub_zero, mul_one] at hc
  exact hc

end Polynomial

end
