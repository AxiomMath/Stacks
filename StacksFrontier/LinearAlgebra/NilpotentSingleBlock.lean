module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# A nilpotent endomorphism with one-dimensional kernel is a single Jordan block

Let `s` be an endomorphism of a finite-dimensional vector space `V` of dimension `n` over a
field, with `s ^ n = 0` and `dim ker s = 1`. Then `dim ker sᵐ = m` for every `m ≤ n`, and
`ker sᵐ = im s^{n - m}`: the kernels and images of the powers of `s` form a single flag with
one-dimensional steps.

The proof is the dimension count: `sᵐ` maps `ker s^{m+1}` into `ker s` with kernel `ker sᵐ`, so
the dimension of `ker sᵐ` grows by at most one at each step, while it reaches `n` at `m = n`.

This is the linear algebra behind the filtration of the free module on a torsor under `ℤ/ℓ` by
the powers of `s = τ - 1` (`τ` the generator), whose steps are all one-dimensional; it is used
for the cyclic-cover argument in the duality of the first cohomology of a curve.

## Main results

* `Module.End.finrank_ker_pow_add_le`: `dim ker s^{m+k} ≤ dim ker sᵐ + k · dim ker s`.
* `Module.End.finrank_ker_pow_eq_of_finrank_ker_eq_one`: `dim ker sᵐ = m` for `m ≤ n`.
* `Module.End.range_pow_eq_ker_pow_of_finrank_ker_eq_one`: `im s^{n-m} = ker sᵐ` for `m ≤ n`.
-/

@[expose] public section

namespace Module.End

open LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (s : Module.End K V)

omit [FiniteDimensional K V] in
/-- `sᵐ` maps `ker s^{m+1}` into `ker s`. -/
theorem pow_apply_mem_ker_of_mem_ker_pow_succ (m : ℕ) {v : V} (hv : v ∈ ker (s ^ (m + 1))) :
    (s ^ m) v ∈ ker s := by
  rw [mem_ker] at hv ⊢
  rwa [← Module.End.mul_apply, ← pow_succ']

/-- **The dimension of `ker s^{m+1}` exceeds that of `ker sᵐ` by at most `dim ker s`.** -/
theorem finrank_ker_pow_succ_le (m : ℕ) :
    Module.finrank K (ker (s ^ (m + 1))) ≤
      Module.finrank K (ker (s ^ m)) + Module.finrank K (ker s) := by
  let g : ker (s ^ (m + 1)) →ₗ[K] ker s :=
    (s ^ m).restrict fun _ hv => pow_apply_mem_ker_of_mem_ker_pow_succ s m hv
  have hker : Module.finrank K (ker g) ≤ Module.finrank K (ker (s ^ m)) := by
    let h : ker g →ₗ[K] ker (s ^ m) :=
      { toFun := fun w => ⟨w.1.1, mem_ker.mpr (congrArg Subtype.val (mem_ker.mp w.2))⟩
        map_add' := fun a b => rfl
        map_smul' := fun c a => rfl }
    exact LinearMap.finrank_le_finrank_of_injective (f := h)
      fun a b hab => Subtype.ext (Subtype.ext (congrArg Subtype.val hab :))
  have hrange := Submodule.finrank_le (range g)
  have := LinearMap.finrank_range_add_finrank_ker g
  omega

/-- **`dim ker s^{m+k} ≤ dim ker sᵐ + k · dim ker s`.** -/
theorem finrank_ker_pow_add_le (m k : ℕ) :
    Module.finrank K (ker (s ^ (m + k))) ≤
      Module.finrank K (ker (s ^ m)) + k * Module.finrank K (ker s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := finrank_ker_pow_succ_le s (m + k)
    rw [← add_assoc]
    nlinarith

variable {s}

/-- **A nilpotent endomorphism of an `n`-dimensional space with `sⁿ = 0` and one-dimensional
kernel has `dim ker sᵐ = m` for `m ≤ n`.** -/
theorem finrank_ker_pow_eq_of_finrank_ker_eq_one
    (hs : s ^ Module.finrank K V = 0) (h1 : Module.finrank K (ker s) = 1) {m : ℕ}
    (hm : m ≤ Module.finrank K V) : Module.finrank K (ker (s ^ m)) = m := by
  have hle : Module.finrank K (ker (s ^ m)) ≤ m := by
    have := finrank_ker_pow_add_le s 0 m
    rw [zero_add, pow_zero, Module.End.one_eq_id, LinearMap.ker_id, finrank_bot, h1] at this
    omega
  have hn : Module.finrank K (ker (s ^ Module.finrank K V)) = Module.finrank K V := by
    rw [hs, ker_zero, finrank_top]
  have hge := finrank_ker_pow_add_le s m (Module.finrank K V - m)
  rw [Nat.add_sub_cancel' hm, hn, h1, mul_one] at hge
  omega

/-- **`ker sᵐ = im s^{n-m}`** for a nilpotent endomorphism of an `n`-dimensional space with
`sⁿ = 0` and one-dimensional kernel, `m ≤ n`. -/
theorem range_pow_eq_ker_pow_of_finrank_ker_eq_one
    (hs : s ^ Module.finrank K V = 0) (h1 : Module.finrank K (ker s) = 1) {m : ℕ}
    (hm : m ≤ Module.finrank K V) :
    range (s ^ (Module.finrank K V - m)) = ker (s ^ m) := by
  have hle : range (s ^ (Module.finrank K V - m)) ≤ ker (s ^ m) := by
    rintro _ ⟨v, rfl⟩
    rw [mem_ker, ← Module.End.mul_apply, ← pow_add, Nat.add_sub_cancel' hm, hs, zero_apply]
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h₁ := LinearMap.finrank_range_add_finrank_ker (s ^ (Module.finrank K V - m))
  rw [finrank_ker_pow_eq_of_finrank_ker_eq_one hs h1 (Nat.sub_le _ _)] at h₁
  rw [finrank_ker_pow_eq_of_finrank_ker_eq_one hs h1 hm]
  omega

/-- **For `j < n`, every vector killed by `sʲ` is in the image of `s`**, for a nilpotent
endomorphism of an `n`-dimensional space with `sⁿ = 0` and one-dimensional kernel. -/
theorem exists_apply_eq_of_pow_apply_eq_zero_of_finrank_ker_eq_one
    (hs : s ^ Module.finrank K V = 0) (h1 : Module.finrank K (ker s) = 1) {j : ℕ}
    (hj : j < Module.finrank K V) {x : V} (hx : (s ^ j) x = 0) : ∃ y, s y = x := by
  obtain ⟨y, rfl⟩ :=
    (range_pow_eq_ker_pow_of_finrank_ker_eq_one hs h1 hj.le).ge (mem_ker.mpr hx)
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank K V - j = m + 1 := ⟨Module.finrank K V - j - 1, by omega⟩
  refine ⟨(s ^ m) y, ?_⟩
  rw [hm, pow_succ', Module.End.mul_apply]

end Module.End

end
