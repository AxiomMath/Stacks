module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# The two-parameter system `F ^ m + I ^ n` and the powers of `F + I`

Let `F` and `I` be ideals of a commutative ring and put `J = F + I`. The ideals `F ^ m + I ^ n`,
indexed by pairs `(m, n)`, and the powers `J ^ k` are **mutually cofinal**: each member of
either system contains a member of the other. Concretely

* `J ^ (m + n) ≤ F ^ m + I ^ n` — Mathlib's `Ideal.sup_pow_add_le_pow_sup_pow`; and
* `F ^ m + I ^ n ≤ J ^ (min m n)` — `Ideal.pow_sup_pow_le_sup_pow_min` below.

So the two systems define the same topology on the ring, hence the same completion. This is the
ring-level content of the step in the Stacks Project's proof of tag 0GVV which recognises the
completion of an adic\* formal spectrum `Spf A` along a closed subset `V(F)` of `|Spec (A / I)|`
as the formal spectrum of the `J`-adic completion of `A`: the completion is presented by the
double system `A / (F ^ m + I ^ n)`, and cofinality replaces it by the single system `A / J ^ k`.

## Main results

* `Ideal.pow_sup_pow_le_sup_pow_min`: `F ^ m + I ^ n ≤ (F + I) ^ (min m n)`.
* `Ideal.exists_sup_pow_le_pow_sup_pow`: every `F ^ m + I ^ n` contains a power of `F + I`.
* `Ideal.exists_pow_sup_pow_le_sup_pow`: every power of `F + I` contains some `F ^ m + I ^ n`.
* `Ideal.sup_pow_two_mul_le_pow_sup_pow_self` and `Ideal.pow_sup_pow_self_le_sup_pow`: the
  sandwich `(F + I) ^ (2 * k) ≤ F ^ k + I ^ k ≤ (F + I) ^ k` for the diagonal system.

The two inequalities of the sandwich are the two cofinality statements specialised to the
diagonal `m = n = k`, which is the form a cofinal-subsystem argument over `ℕ` consumes.
-/

@[expose] public section

namespace Ideal

variable {R : Type*} [CommSemiring R] (F I : Ideal R)

/-- `F ^ m + I ^ n` is contained in `(F + I) ^ (min m n)`: both summands are, since a power of
`F` or of `I` with exponent at least `min m n` lies in the corresponding power of `F + I`. -/
theorem pow_sup_pow_le_sup_pow_min (m n : ℕ) :
    F ^ m ⊔ I ^ n ≤ (F ⊔ I) ^ min m n :=
  sup_le
    ((pow_le_pow_right (min_le_left m n)).trans (pow_le_pow_left' le_sup_left _))
    ((pow_le_pow_right (min_le_right m n)).trans (pow_le_pow_left' le_sup_right _))

/-- **Every member of the two-parameter system contains a power of the sum.** Taking `k = m + n`
works, by `Ideal.sup_pow_add_le_pow_sup_pow`. -/
theorem exists_sup_pow_le_pow_sup_pow (m n : ℕ) : ∃ k, (F ⊔ I) ^ k ≤ F ^ m ⊔ I ^ n :=
  ⟨m + n, sup_pow_add_le_pow_sup_pow⟩

/-- **Every power of the sum contains a member of the two-parameter system.** Taking
`m = n = k` works, by `Ideal.pow_sup_pow_le_sup_pow_min`. -/
theorem exists_pow_sup_pow_le_sup_pow (k : ℕ) : ∃ m n, F ^ m ⊔ I ^ n ≤ (F ⊔ I) ^ k :=
  ⟨k, k, by simpa using pow_sup_pow_le_sup_pow_min F I k k⟩

/-- The diagonal member `F ^ k + I ^ k` contains `(F + I) ^ (2 * k)`. -/
theorem sup_pow_two_mul_le_pow_sup_pow_self (k : ℕ) :
    (F ⊔ I) ^ (2 * k) ≤ F ^ k ⊔ I ^ k := by
  simpa [two_mul] using (sup_pow_add_le_pow_sup_pow : (F ⊔ I) ^ (k + k) ≤ F ^ k ⊔ I ^ k)

/-- The diagonal member `F ^ k + I ^ k` is contained in `(F + I) ^ k`. -/
theorem pow_sup_pow_self_le_sup_pow (k : ℕ) : F ^ k ⊔ I ^ k ≤ (F ⊔ I) ^ k := by
  simpa using pow_sup_pow_le_sup_pow_min F I k k

/-- The two-parameter system is antitone in each index, so it is a directed system under
reverse inclusion: `F ^ m' + I ^ n' ≤ F ^ m + I ^ n` whenever `m ≤ m'` and `n ≤ n'`. -/
theorem pow_sup_pow_le_pow_sup_pow {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    F ^ m' ⊔ I ^ n' ≤ F ^ m ⊔ I ^ n :=
  sup_le_sup (pow_le_pow_right hm) (pow_le_pow_right hn)

end Ideal
