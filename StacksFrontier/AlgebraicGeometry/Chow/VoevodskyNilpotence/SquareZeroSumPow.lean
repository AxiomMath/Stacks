module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.Support

/-!
# Two counting identities behind the Voevodsky nilpotence argument

Stacks 0FH9 computes the flat pullback along `π : Xⁿ ⟶ Sⁿ(X)` of the zero cycle
`c₁(𝒩)ⁿ ∩ [Sⁿ(X)]` and, separately, the Picard class of `π^*𝒩`. Both computations reduce to a
count, and this file proves the two counts in the generality in which they are counts and nothing
else.

The first is the expansion of an `n`-th power of a sum of `n` square-zero elements of a
commutative ring:

  `(c₁ + ⋯ + cₙ)ⁿ = n! · c₁ ⋯ cₙ`  whenever `cᵢ² = 0` for every `i`.

Expanding the power indexes the terms by the functions `p : Fin n → Fin n`
(`Finset.sum_pow'`). A term whose `p` is not injective repeats an index, so its product has a
factor `cᵢ²` and vanishes; a term whose `p` is injective is a permutation, so its product is
`c₁ ⋯ cₙ` after reindexing. What survives is therefore one copy of `c₁ ⋯ cₙ` for each permutation
of `Fin n`, and there are `n!` of those.

*This is where the source's arithmetic slips.* Stacks 0FH9 writes

  `(∑ᵢ c₁(ℒᵢ))ⁿ ∩ [Xⁿ] = nⁿ c₁(ℒ₁) ∩ … ∩ c₁(ℒₙ) ∩ [Xⁿ]`,

with `nⁿ` where the expansion gives `n!`: the multinomial coefficient of the all-ones multi-index
is `n!/(1! ⋯ 1!) = n!`, not `nⁿ`. The slip is harmless for the lemma, whose conclusion is only
that a *nonzero* integer multiple of `αₙ` is a pullback, but the constant it produces is
`((n-1)!)ⁿ · n!` and not `(n!)ⁿ`.

The second count is the sum, over all permutations `σ` of `Fin n`, of a term depending only on
`σ i₀` for one fixed index `i₀`:

  `∑_{σ ∈ Sₙ} ℓ (σ i₀) = (n-1)! • ∑ᵢ ℓ i`.

Here the fibres of `σ ↦ σ i₀` are permuted among themselves by left multiplication with a
transposition, so they are equinumerous, and since there are `n` of them and `n!` permutations
each has `(n-1)!` elements.

## Main results

* `Stacks.Chow.card_filter_perm_apply_eq` — the fibre count: exactly `(n-1)!` permutations of
  `Fin n` send a given index to a given index.
* `Stacks.Chow.sum_perm_apply_eq_factorial_nsmul_sum` — the second identity, in an arbitrary
  additive commutative monoid.
* `Stacks.Chow.sum_pow_eq_factorial_nsmul_prod` — the first identity, in an arbitrary
  commutative ring.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
-/

@[expose] public section

open Finset Nat

namespace Stacks.Chow

/-! ### The fibres of `σ ↦ σ i₀` -/

section Fibre

variable {n : ℕ}

/-- Left multiplication by the transposition of `i` and `j` is a bijection from the permutations
carrying `i₀` to `i` onto those carrying `i₀` to `j`. -/
private theorem card_filter_perm_apply_eq_congr (i₀ i j : Fin n) :
    #{σ : Equiv.Perm (Fin n) | σ i₀ = i} = #{σ : Equiv.Perm (Fin n) | σ i₀ = j} := by
  classical
  exact Finset.card_nbij' (fun σ ↦ Equiv.swap i j * σ) (fun σ ↦ Equiv.swap i j * σ)
    (fun σ _ ↦ by simp_all) (fun σ _ ↦ by simp_all) (fun σ _ ↦ by simp [← mul_assoc])
    (fun σ _ ↦ by simp [← mul_assoc])

/-- **The fibre count.** For indices `i₀, i` of `Fin n` there are exactly `(n-1)!`
permutations `σ` of `Fin n` with `σ i₀ = i`.

The fibres of `σ ↦ σ i₀` are equinumerous by
`Stacks.Chow.card_filter_perm_apply_eq_congr`, there are `n` of them, and together they
exhaust the `n!` permutations. -/
theorem card_filter_perm_apply_eq (i₀ i : Fin n) :
    #{σ : Equiv.Perm (Fin n) | σ i₀ = i} = (n - 1)! := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos i₀.pos).symm⟩
  have htotal : ∑ j : Fin (m + 1), #{σ : Equiv.Perm (Fin (m + 1)) | σ i₀ = j} =
      (m + 1)! := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin (m + 1)) ↦ σ i₀)
      (fun σ _ ↦ Finset.mem_univ _), Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun j _ ↦ card_filter_perm_apply_eq_congr i₀ j i), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin] at htotal
  simpa [Nat.factorial_succ] using htotal

/-- **The orbit sum.** For a family `ℓ` indexed by `Fin n` and a fixed index `i₀`, the sum over
all permutations `σ` of `Fin n` of `ℓ (σ i₀)` is `(n-1)!` copies of the total `∑ᵢ ℓ i`.

Each value `i` is taken by `σ i₀` for exactly `(n-1)!` permutations
(`Stacks.Chow.card_filter_perm_apply_eq`). -/
theorem sum_perm_apply_eq_factorial_nsmul_sum {M : Type*} [AddCommMonoid M] (ℓ : Fin n → M)
    (i₀ : Fin n) :
    ∑ σ : Equiv.Perm (Fin n), ℓ (σ i₀) = (n - 1)! • ∑ i, ℓ i := by
  classical
  have himg : Finset.image (fun σ : Equiv.Perm (Fin n) ↦ σ i₀) Finset.univ = Finset.univ :=
    Finset.eq_univ_of_forall fun i ↦ Finset.mem_image.2
      ⟨Equiv.swap i₀ i, Finset.mem_univ _, Equiv.swap_apply_left i₀ i⟩
  rw [Finset.sum_comp (f := ℓ) (g := fun σ : Equiv.Perm (Fin n) ↦ σ i₀), himg,
    Finset.sum_congr rfl (fun i _ ↦ by rw [card_filter_perm_apply_eq i₀ i]),
    ← Finset.smul_sum]

end Fibre

/-! ### The `n`-th power of a sum of `n` square-zero elements -/

/-- **The square-zero expansion.** In a commutative ring, if `c : Fin n → R` has `cᵢ² = 0` for
every `i`, then

  `(∑ᵢ cᵢ)ⁿ = n! • ∏ᵢ cᵢ`.

Expanding the power by `Finset.sum_pow'` indexes the terms by functions `p : Fin n → Fin n`; a
non-injective `p` contributes a product with a repeated factor, hence zero, and an injective one
is a permutation, whose product is `∏ᵢ cᵢ` after reindexing. There are `n!` permutations.

This is the step of the proof of Stacks 0FH9 that turns `(∑ᵢ c₁(ℒᵢ))ⁿ ∩ [Xⁿ]` into a multiple of
`c₁(ℒ₁) ∩ ⋯ ∩ c₁(ℒₙ) ∩ [Xⁿ]`. The multiplier is `n!`; the source writes `nⁿ`. -/
theorem sum_pow_eq_factorial_nsmul_prod {R : Type*} [CommRing R] {n : ℕ} (c : Fin n → R)
    (hc : ∀ i, c i * c i = 0) :
    (∑ i, c i) ^ n = n ! • ∏ i, c i := by
  classical
  have hzero : ∀ p : Fin n → Fin n, ¬ Function.Injective p → ∏ i, c (p i) = 0 := by
    intro p hp
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hp
    rw [← Finset.mul_prod_erase Finset.univ (fun k ↦ c (p k)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ (fun k ↦ c (p k))
        (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ j⟩),
      ← mul_assoc, hij, hc, zero_mul]
  have himage : ∀ p ∈ (Finset.univ : Finset (Fin n → Fin n)),
      p ∉ Finset.univ.image (fun σ : Equiv.Perm (Fin n) ↦ (σ : Fin n → Fin n)) →
      ∏ i, c (p i) = 0 := fun p _ hpS ↦ hzero p fun hinj ↦ hpS <| Finset.mem_image.2
      ⟨Equiv.ofBijective p (Finite.injective_iff_bijective.1 hinj), Finset.mem_univ _, rfl⟩
  rw [Finset.sum_pow' Finset.univ c n, Fintype.piFinset_univ,
    ← Finset.sum_subset (Finset.subset_univ _) himage,
    Finset.sum_image (fun σ _ σ' _ h ↦ Equiv.coe_fn_injective h),
    Finset.sum_congr rfl (fun σ _ ↦ Equiv.prod_comp σ c), Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin]

/-- **The square-zero expansion for pairwise commuting elements of a ring.** In a ring, if
`c : Fin n → R` is pairwise commuting and `cᵢ² = 0` for every `i`, then

  `(∑ᵢ cᵢ)ⁿ = n! • c₀ ⋯ c_{n-1}`,

the product being taken in the order of the indices. Only commutativity among the `cᵢ` is used,
so this is the form the identity takes in the ring `AddMonoid.End` of operators on Chow groups,
where the `cᵢ` are the first Chern class cap operations of invertible modules and the commutation
is Stacks 02TJ.

The pairwise commutation makes the subring generated by the `cᵢ` commutative
(`Subring.isMulCommutative_closure`), and the identity there is
`Stacks.Chow.sum_pow_eq_factorial_nsmul_prod`. -/
theorem sum_pow_eq_factorial_nsmul_listProd_of_commute {R : Type*} [Ring R] {n : ℕ}
    (c : Fin n → R) (hcomm : ∀ i j, Commute (c i) (c j)) (hc : ∀ i, c i * c i = 0) :
    (∑ i, c i) ^ n = n ! • (List.ofFn c).prod := by
  classical
  have hpair : ∀ x ∈ Set.range c, ∀ y ∈ Set.range c, x * y = y * x := by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    exact hcomm i j
  let : CommRing (Subring.closure (Set.range c)) :=
    { (inferInstance : Ring (Subring.closure (Set.range c))) with
      mul_comm := (Subring.isMulCommutative_closure fun x hx y hy _ => hpair x hx y hy).is_comm.comm }
  let φ : Subring.closure (Set.range c) →+* R := (Subring.closure (Set.range c)).subtype
  let c' : Fin n → Subring.closure (Set.range c) :=
    fun i ↦ ⟨c i, Subring.subset_closure (Set.mem_range_self i)⟩
  calc (∑ i, c i) ^ n = φ ((∑ i, c' i) ^ n) := by
        rw [map_pow, map_sum]
        rfl
    _ = φ (n ! • ∏ i, c' i) := by
      rw [sum_pow_eq_factorial_nsmul_prod c' fun i ↦ Subtype.ext (by simpa using hc i)]
    _ = n ! • (List.ofFn c).prod := by
      rw [map_nsmul, ← List.prod_ofFn (f := c'), map_list_prod, List.map_ofFn]
      rfl

end Stacks.Chow

end
