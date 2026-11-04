module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksFrontier.RingTheory.DeRham.Cartier.Coordinates

/-!
# The Cartier isomorphism for a polynomial algebra over a perfect ring

Let `A` be a perfect ring of characteristic `p` and `P = A[X₁, …, Xₙ]`. The variables are
Frobenius coordinates of `P` over `A`: the differentials `dXⱼ` are a basis of `Ω[P⁄A]`, and the
monomials `X^α`, `0 ≤ αⱼ < p`, are a basis of `P` over itself acting through the Frobenius,
since every monomial `a X^β` is `(a^{1/p} X^γ)^p X^α` for `β = pγ + α`. Hence the inverse Cartier
map `Ω^i_{P/A} ⟶ H^i(F_*Ω^•_{P/A})` is bijective.

## Main results

* `KaehlerDifferential.Cartier.isFrobeniusCoordinates_mvPolynomial`: the variables are
  Frobenius coordinates.
* `KaehlerDifferential.Cartier.inverseCartier_bijective_mvPolynomial`: **the Cartier
  isomorphism for a polynomial algebra over a perfect ring**.
-/

@[expose] public noncomputable section

open KaehlerDifferential MvPolynomial

universe u

namespace KaehlerDifferential.Cartier

variable (p : ℕ) [hp : Fact p.Prime] (A : Type u) [CommRing A] [CharP A p] [PerfectRing A p]
  {n : ℕ}

/-- The monomial `X^α` is `monomial α 1`. -/
theorem monomial_X (α : Fin n → ℕ) :
    monomial (X (R := A)) α = MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) 1 := by
  rw [Cartier.monomial, MvPolynomial.monomial_eq, C_1, one_mul, Finsupp.prod_fintype] <;> simp

/-- The map `(c_α) ↦ ∑_α c_α^p X^α`, as an additive map. -/
def frobeniusCoordinateMap :
    ((Fin n → Fin p) → MvPolynomial (Fin n) A) →+ MvPolynomial (Fin n) A where
  toFun c := ∑ α, c α ^ p * monomial X (fun j ↦ (α j : ℕ))
  map_zero' := by simp [zero_pow hp.out.ne_zero]
  map_add' c c' := by
    simp only [Pi.add_apply, add_pow_char, add_mul, Finset.sum_add_distrib]

omit [PerfectRing A p] in
/-- `frobeniusCoordinateMap` sends the family that is `f` at `α` and `0` elsewhere to
`f^p X^α`. -/
theorem frobeniusCoordinateMap_single (α : Fin n → Fin p) (f : MvPolynomial (Fin n) A) :
    frobeniusCoordinateMap p A
        (Pi.single α f : (Fin n → Fin p) → MvPolynomial (Fin n) A) =
      f ^ p * monomial X (fun j ↦ (α j : ℕ)) := by
  classical
  show ∑ α', (Pi.single α f : (Fin n → Fin p) → MvPolynomial (Fin n) A) α' ^ p * _ = _
  rw [Finset.sum_eq_single α]
  · simp
  · intro α' _ h
    simp [h, zero_pow hp.out.ne_zero]
  · simp

/-- Every monomial `a X^β` is `(a^{1/p} X^γ)^p X^α` with `β = pγ + α`. -/
theorem monomial_mem_range (β : Fin n →₀ ℕ) (a : A) :
    MvPolynomial.monomial β a ∈ (frobeniusCoordinateMap p A (n := n)).range := by
  classical
  let α : Fin n → Fin p := fun j ↦ ⟨β j % p, Nat.mod_lt _ hp.out.pos⟩
  let γ : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j ↦ β j / p
  refine ⟨(Pi.single α (MvPolynomial.monomial γ ((frobeniusEquiv A p).symm a)) :
    (Fin n → Fin p) → MvPolynomial (Fin n) A), ?_⟩
  have hβ : p • γ + Finsupp.equivFunOnFinite.symm (fun j ↦ (α j : ℕ)) = β := by
    ext j
    simp [γ, α, Nat.div_add_mod]
  rw [frobeniusCoordinateMap_single, monomial_X, MvPolynomial.monomial_pow,
    MvPolynomial.monomial_mul_monomial, frobeniusEquiv_symm_pow_p, mul_one, hβ]

omit [PerfectRing A p] in
/-- The coefficient of `X^{pγ + α}` in `∑_α c_α^p X^α` is `(coeff_γ c_α)^p`. -/
theorem coeff_frobeniusCoordinateMap (c : (Fin n → Fin p) → MvPolynomial (Fin n) A)
    (α : Fin n → Fin p) (γ : Fin n →₀ ℕ) :
    coeff (p • γ + Finsupp.equivFunOnFinite.symm (fun j ↦ (α j : ℕ)))
        (frobeniusCoordinateMap p A c) = coeff γ (c α) ^ p := by
  classical
  have hpow : ∀ f : MvPolynomial (Fin n) A,
      f ^ p = ∑ δ ∈ f.support, MvPolynomial.monomial (p • δ) (coeff δ f ^ p) := by
    intro f
    conv_lhs => rw [f.as_sum]
    rw [sum_pow_char]
    exact Finset.sum_congr rfl fun δ _ ↦ by rw [MvPolynomial.monomial_pow]
  show coeff _ (∑ α', c α' ^ p * monomial X (fun j ↦ (α' j : ℕ))) = _
  rw [coeff_sum, Finset.sum_eq_single α]
  · rw [hpow, monomial_X, Finset.sum_mul, coeff_sum]
    simp only [MvPolynomial.monomial_mul_monomial, mul_one, coeff_monomial]
    rw [Finset.sum_eq_single γ]
    · simp
    · intro δ _ hδ
      rw [ite_eq_right]
      intro h
      apply hδ
      ext j
      have := congrArg (· j) h
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
        Finsupp.coe_equivFunOnFinite_symm] at this
      have h1 := (α j).2
      have h2 : p * δ j = p * γ j := by omega
      exact Nat.eq_of_mul_eq_mul_left hp.out.pos h2
    · intro hγ
      rw [ite_eq_left rfl, notMem_support_iff.1 hγ, zero_pow hp.out.ne_zero]
  · intro α' _ hα'
    rw [hpow, monomial_X, Finset.sum_mul, coeff_sum]
    refine Finset.sum_eq_zero fun δ _ ↦ ?_
    rw [MvPolynomial.monomial_mul_monomial, mul_one, coeff_monomial, ite_eq_right]
    intro h
    apply hα'
    funext j
    have := congrArg (· j) h
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.coe_equivFunOnFinite_symm] at this
    have h1 := (α j).2
    have h2 := (α' j).2
    apply Fin.ext
    have e1 : (p * δ j + α' j) % p = (α' j : ℕ) := by
      rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h2
    have e2 : (p * γ j + α j) % p = (α j : ℕ) := by
      rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h1
    rw [← e1, ← e2, this]
  · simp

/-- **The variables of a polynomial algebra over a perfect ring are Frobenius coordinates.** -/
theorem isFrobeniusCoordinates_mvPolynomial :
    IsFrobeniusCoordinates p (MvPolynomial (Fin n) A) (X (R := A)) := by
  show Function.Bijective (frobeniusCoordinateMap p A (n := n))
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    funext α
    ext γ
    have h := coeff_frobeniusCoordinateMap p A c α γ
    rw [hc, coeff_zero] at h
    apply (PerfectRing.bijective_frobenius (R := A) (p := p)).1
    beta_reduce
    rw [Pi.zero_apply, coeff_zero, ← h, zero_pow hp.out.ne_zero]
  · intro f
    show f ∈ (frobeniusCoordinateMap p A (n := n)).range
    induction f using MvPolynomial.induction_on' with
    | monomial β a => exact monomial_mem_range p A β a
    | add f g hf hg => exact add_mem hf hg

/-- The basis `mvPolynomialBasis` of `Ω[P⁄A]` consists of the differentials `dXⱼ`. -/
theorem mvPolynomialBasis_eq_D (j : Fin n) :
    mvPolynomialBasis A (Fin n) j = D A (MvPolynomial (Fin n) A) (X j) :=
  (mvPolynomialBasis A (Fin n)).repr.injective (by
    rw [Module.Basis.repr_self, mvPolynomialBasis_repr_D_X])

/-- **The Cartier isomorphism for a polynomial algebra over a perfect ring**: the inverse Cartier
map `Ω^i_{P/A} ⟶ H^i(F_*Ω^•_{P/A})` is bijective for `P = A[X₁, …, Xₙ]`. -/
theorem inverseCartier_bijective_mvPolynomial (i : ℕ) :
    Function.Bijective (inverseCartier p A (MvPolynomial (Fin n) A) i) :=
  inverseCartier_bijective_of_isFrobeniusCoordinates p (mvPolynomialBasis_eq_D A)
    (isFrobeniusCoordinates_mvPolynomial p A) i

end KaehlerDifferential.Cartier

end
