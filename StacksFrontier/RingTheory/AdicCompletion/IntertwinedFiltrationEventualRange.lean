module

public import StacksFrontier.RingTheory.AdicCompletion.IntertwinedFiltration

/-!
# The intertwined-filtration limit argument with a per-`n` range condition

`StacksFrontier/RingTheory/AdicCompletion/IntertwinedFiltration.lean` runs the
commutative-algebra core of [Stacks, Tag 02OC]: for a tower `(P n)` of `A`-modules with
compatible maps `π n : M → P n` whose kernels are intertwined with the `I`-adic filtration,
the limit of `(P n)` is the `I`-adic completion `M^∧_I`.  Its range hypothesis is the
*uniform* one of [Stacks, Tag 02OB] clause (3): a single shift `c`, shared with the kernel
bounds, with `im (P k → P n) = im (π n)` for every `k ≥ n + c`.

This file runs the same argument from the weaker *per-`n`* range condition, the shape in which
[Stacks, Tag 08AY] clause (3) states it: for every `n` there is a level `c₂ ≥ n`, depending on
`n` and not tied to the kernel shift `c`, with `im (P k → P n) = im (π n)` for every `k ≥ c₂`.
That is all the argument uses — the hypothesis is reached at exactly one point, where a
compatible family's `n`-th component is exhibited in `im (π n)` by pulling it back from a high
enough level, one `n` at a time.

## Relation to the uniform version, and the duplication

`Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange` below is
`Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimit` with the per-`n` hypothesis in
place of the uniform one, and the per-`n` hypothesis is strictly weaker: the uniform one
implies it with `c₂ = n + c`, and nothing recovers a shift uniform in `n` from a level that may
grow arbitrarily fast.  So the weaker statement cannot be obtained by specializing the
uniform one, and the chain carrying the hypothesis has to be rerun.

Two declarations of the file above are therefore duplicated here:

* `Stacks.IntertwinedFiltration.towerComparison_bijective`, as
  `Stacks.IntertwinedFiltration.towerComparison_bijective_of_eventualRange`.  Its proof is the
  same, with the one range step choosing a level per `n`; every other step calls the lemmas of
  the file above (`towerLimit_ext`, `quotKerEmbed_injective`, `towerComparison_coe`,
  `antitone_ker`, `factor_quotient_mk`, `quotKerEmbed_mk`, `towerLimit_compat`) rather than
  reproving anything.
* `Stacks.IntertwinedFiltration.towerLimitEquivQuotTowerLimit`, as
  `Stacks.IntertwinedFiltration.towerLimitEquivQuotTowerLimitOfEventualRange` — one line
  wrapping the bijectivity in a `LinearEquiv`.

The duplication exists only because the types of those two declarations are frozen: they take
the uniform hypothesis, and they may not be retyped.  The right repair is for the file above to
weaken its own range hypothesis to the per-`n` existential and keep the uniform statement as a
specialization along `c₂ = n + c`; this file then disappears, its three declarations becoming
the ones there.

## Main results

* `Stacks.IntertwinedFiltration.towerComparison_bijective_of_eventualRange` and
  `Stacks.IntertwinedFiltration.towerLimitEquivQuotTowerLimitOfEventualRange` — the limit of
  `(P n)` agrees with the limit of `(M ⧸ ker (π n))`, from the per-`n` range condition.
* `Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange` — the assembled
  statement `M^∧_I ≃ₗ[A] lim_n P n`, from the per-`n` range condition.

## References

* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 08AY](https://stacks.math.columbia.edu/tag/08AY)
-/

@[expose] public section

namespace Stacks.IntertwinedFiltration

variable {A : Type*} [CommRing A]

section TowerOfMaps

variable {M : Type*} [AddCommGroup M] [Module A M]
  (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m) (π : ∀ n, M →ₗ[A] P n)

/-- **Steps 1 and 2 of Stacks 02OC, from the per-`n` range condition.**  If for each `n` the
maps `P k → P n` have image exactly `im (π n)` for all large `k`, then the limit of the tower
`(P n)` is the limit of the tower `(M ⧸ ker (π n))`: a compatible family has all its components
in `im (π n)`, because the `n`-th one is pulled back from a high enough level, and
`im (π n) ≅ M ⧸ ker (π n)`.

The range hypothesis is the per-`n` existential of [Stacks, Tag 08AY] clause (3): the proof
chooses, for each `n` separately, one level `c₂ ≥ n` at which the images agree.  This is
`towerComparison_bijective` with that hypothesis in place of the uniform threshold `n + c` of
[Stacks, Tag 02OB] clause (3), which is strictly stronger; see the module docstring on why the
proof is rerun rather than specialized. -/
public theorem towerComparison_bijective_of_eventualRange
    (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m)
    (hrange : ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
      LinearMap.range (T n k h) = LinearMap.range (π n)) :
    Function.Bijective (towerComparison P T π hπ) := by
  constructor
  · intro y y' hyy'
    refine towerLimit_ext fun n ↦ quotKerEmbed_injective P π n ?_
    rw [← towerComparison_coe P T π hπ y n, ← towerComparison_coe P T π hπ y' n, hyy']
  · intro x
    have hmem : ∀ n : ℕ, ∃ a : M, π n a = (x : ∀ k, P k) n := by
      intro n
      obtain ⟨c₂, hnc₂, hc₂⟩ := hrange n
      rw [← LinearMap.mem_range, ← hc₂ c₂ hnc₂ le_rfl]
      exact ⟨(x : ∀ k, P k) c₂, towerLimit_compat x n c₂ hnc₂⟩
    choose a ha using hmem
    refine ⟨⟨fun n ↦ Submodule.Quotient.mk (a n), ?_⟩, towerLimit_ext fun n ↦ ?_⟩
    · intro m n h
      show Submodule.factor (antitone_ker P T π hπ h) (Submodule.Quotient.mk (a n)) =
        (Submodule.Quotient.mk (a m) : M ⧸ LinearMap.ker (π m))
      rw [factor_quotient_mk, Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]
      have h1 : π m (a n) = T m n h (π n (a n)) := by
        rw [← hπ m n h, LinearMap.comp_apply]
      rw [h1, ha n, towerLimit_compat x m n h, ha m]
    · rw [towerComparison_coe]
      exact (quotKerEmbed_mk P π n (a n)).trans (ha n)

/-- The limit of the tower `(P n)` is the limit of the tower `(M ⧸ ker (π n))`, from the per-`n`
range condition.  This is `towerLimitEquivQuotTowerLimit` with the range hypothesis of
[Stacks, Tag 08AY] clause (3) in place of the uniform one. -/
public noncomputable def towerLimitEquivQuotTowerLimitOfEventualRange
    (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m)
    (hrange : ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
      LinearMap.range (T n k h) = LinearMap.range (π n)) :
    quotTowerLimit (fun n ↦ LinearMap.ker (π n)) (antitone_ker P T π hπ) ≃ₗ[A] towerLimit P T :=
  LinearEquiv.ofBijective _ (towerComparison_bijective_of_eventualRange P T π hπ hrange)

/-- **The commutative-algebra core of Stacks 02OC, from the per-`n` range condition.**  Let
`(P n)` be a tower of `A`-modules with compatible maps `π n : M → P n`.  Assume there is a `c`
with

* `I ^ n M ≤ ker (π n)` for all `n`;
* `ker (π n) ≤ I ^ (n - c) M` for all `n ≥ c`;

and that for every `n` there is a level `c₂ ≥ n` with `im (P k → P n) = im (π n)` for all
`k ≥ c₂`.

Then the `I`-adic completion of `M` is the limit of the tower `(P n)`.

The last hypothesis is exactly clause (3) of [Stacks, Tag 08AY]: the level `c₂` depends on `n`
and is not tied to the shift `c` of the kernel bounds.  That is all the argument uses,
`towerComparison_bijective_of_eventualRange` choosing one such level per `n`.  With the uniform
threshold `n + c` of [Stacks, Tag 02OB] clause (3) instead, the statement is
`adicCompletionEquivTowerLimit`; that hypothesis is strictly stronger, which is why this is a
separate statement rather than a specialization of it. -/
public noncomputable def adicCompletionEquivTowerLimitOfEventualRange (I : Ideal A) (c : ℕ)
    (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m)
    (hker : ∀ n, I ^ n • (⊤ : Submodule A M) ≤ LinearMap.ker (π n))
    (hker' : ∀ n, c ≤ n → LinearMap.ker (π n) ≤ I ^ (n - c) • (⊤ : Submodule A M))
    (hrange : ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
      LinearMap.range (T n k h) = LinearMap.range (π n)) :
    AdicCompletion I M ≃ₗ[A] towerLimit P T :=
  (adicCompletionEquiv I (fun n ↦ LinearMap.ker (π n)) c (antitone_ker P T π hπ) hker
      hker').symm.trans
    (towerLimitEquivQuotTowerLimitOfEventualRange P T π hπ hrange)

end TowerOfMaps

end Stacks.IntertwinedFiltration

end
