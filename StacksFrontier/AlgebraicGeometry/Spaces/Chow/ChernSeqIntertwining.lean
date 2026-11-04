module

public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.Group.Hom.End
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SegreInverse

/-!
# Operations intertwining Segre operations intertwine Chern operations

The Chern operations of a projective bundle are the coefficients of the inverse of its Segre
series, `c_n = (-1)^n s_n` with `s₀ = 1` and `s_n = -∑_{j<n} t_{n-j} s_j`
(`AlgebraicGeometry.Space.PrivateChern.chernSeq`). If a homomorphism `φ : M ⟶ M'` intertwines two
families of Segre operations, `φ ∘ t_i = t'_i ∘ φ` for every `i`, then it intertwines the Chern
operations built from them, `φ ∘ c_n = c'_n ∘ φ`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.map_segreInverseSeq_of_intertwines`: intertwining of the
  inverse Segre sequences.
* `AlgebraicGeometry.Space.PrivateChern.map_chernSeq_of_intertwines`: intertwining of the Chern
  sequences.

## References

* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0ESD](https://stacks.math.columbia.edu/tag/0ESD)
-/

@[expose] public section

namespace AlgebraicGeometry.Space.PrivateChern

variable {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] (φ : M →+ M')
  {t : ℕ → AddMonoid.End M} {t' : ℕ → AddMonoid.End M'}

/-- A finite sum of endomorphisms is evaluated pointwise. -/
private theorem end_finset_sum_apply {N ι : Type*} [AddCommGroup N] (s : Finset ι)
    (f : ι → AddMonoid.End N) (y : N) : (∑ j ∈ s, f j) y = ∑ j ∈ s, f j y :=
  AddMonoidHom.finsetSum_apply _ _ _

/-- Powers of `-1` in `AddMonoid.End` are the integer casts of the powers of `-1`. -/
private theorem neg_one_pow_end {N : Type*} [AddCommGroup N] (n : ℕ) :
    ((-1 : AddMonoid.End N) ^ n) = (((-1) ^ n : ℤ) : AddMonoid.End N) := by
  push_cast; rfl

/-- **A homomorphism intertwining two Segre sequences intertwines their inverse sequences.** -/
theorem map_segreInverseSeq_of_intertwines (h : ∀ i x, φ (t i x) = t' i (φ x)) (n : ℕ) (x : M) :
    φ (segreInverseSeq t n x) = segreInverseSeq t' n (φ x) := by
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    cases n with
    | zero => simp [segreInverseSeq_zero]
    | succ n =>
      rw [segreInverseSeq_succ, segreInverseSeq_succ]
      show φ (-((∑ j : Fin (n + 1), t (n + 1 - j) * segreInverseSeq t j : AddMonoid.End M) x)) =
        -((∑ j : Fin (n + 1), t' (n + 1 - j) * segreInverseSeq t' j : AddMonoid.End M') (φ x))
      rw [map_neg, end_finset_sum_apply, end_finset_sum_apply, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [AddMonoid.End.coe_mul, AddMonoid.End.coe_mul, Function.comp_apply, Function.comp_apply,
        h, ih j j.2]

/-- **A homomorphism intertwining two Segre sequences intertwines their Chern sequences.** -/
theorem map_chernSeq_of_intertwines (h : ∀ i x, φ (t i x) = t' i (φ x)) (n : ℕ) (x : M) :
    φ (chernSeq t n x) = chernSeq t' n (φ x) := by
  simp only [chernSeq, AddMonoid.End.coe_mul, Function.comp_apply]
  rw [← map_segreInverseSeq_of_intertwines φ h n x]
  generalize segreInverseSeq t n x = y
  rw [neg_one_pow_end, neg_one_pow_end, AddMonoid.End.intCast_apply,
    AddMonoid.End.intCast_apply, map_zsmul]

end AlgebraicGeometry.Space.PrivateChern

end
