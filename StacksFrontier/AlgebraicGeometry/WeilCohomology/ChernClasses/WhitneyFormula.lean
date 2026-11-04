module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TotalChernClassLocallyFree

/-!
# The Whitney sum formula for an invertible submodule

In the standing situation of Stacks Section 45.12, the existence half of Tag 0FI5 turns on one
computation: for a short exact sequence `0 ⟶ ℒ ⟶ ℰ ⟶ 𝓕 ⟶ 0` of finite locally free modules with
`ℒ` invertible, `c^A(ℰ) = c^A(ℒ) c^A(𝓕)`,
that is `c^A_{n+1}(ℰ) = c^A_{n+1}(𝓕) + c₁^A(ℒ) ∪ c^A_n(𝓕)`. This file proves it.

## Main results

* `Stacks.WeilCohomology.ChernSetup.chernClass_add_one_of_invertibleSub`: **the Whitney sum
  formula for an invertible submodule**, the computation at the heart of Tag 0FI5's existence
  half.

## The argument

Write `p : P ⟶ X` for the projective bundle of `ℰ`, `x = c₁^A(𝒪_P(1))`, `Λ = p^*c₁^A(ℒ)`, and
`a = ∑_{k=0}^{r+1} (-1)^k x^k ∪ p^*c^A_{r+1-k}(𝓕)`.

The surjection `ℰ ⟶ 𝓕` gives a closed immersion `i : P' = 𝐏(𝓕) ⟶ 𝐏(ℰ) = P` over `X` under
which `𝒪_P(1)` restricts to `𝒪_{P'}(1)`, so `i^*a` is equation 45.12.1.1 for `𝓕` on `P'` and
therefore vanishes. Condition (5) of the situation then gives `a ∪ c₁^A(𝒪_P(P')) = 0`, and
`𝒪_P(P') ≅ ℒ^{⊗ -1} ⊗ 𝒪_P(1)` identifies `c₁^A(𝒪_P(P'))` with `x - Λ`. So `a ∪ (x - Λ) = 0`.

Expanding, the family `d_0 = 1`, `d_{j+1} = c^A_{j+1}(𝓕) + c₁^A(ℒ) ∪ c^A_j(𝓕)` satisfies
`∑_{k=0}^{r+2} (-1)^k x^k ∪ p^*d_{r+2-k} = -(x - Λ) ∪ a = 0`,
which is equation 45.12.1.1 for `ℰ`; by
`Stacks.WeilCohomology.ChernSetup.chernClass_eq_of_relation` the family `d` is therefore the
family of Chern classes of `ℰ`. That expansion is pure ring theory and is isolated as
`Stacks.WeilCohomology.sum_eq_zero_of_divisorRelation`.

## What is a hypothesis, and why

`Stacks.WeilCohomology.ChernSetup` carries the projective bundle of a module as a field with no
functoriality, so none of the geometry the source's proof uses can be produced from it. The
three inputs are therefore hypotheses, exactly as the comparison of projective bundles is a
hypothesis in `Stacks.WeilCohomology.ChernSetup.chernClass_eq_of_bundleIso`:

* the closed immersion `i : 𝐏(𝓕) ⟶ 𝐏(ℰ)` over `X` — clause (3)(c) of the source's standing
  situation — together with `i^*c₁^A(𝒪_P(1)) = c₁^A(𝒪_{P'}(1))`;
* the class `𝒪_P(P') ∈ Pic(P)` with the conclusion of **condition (5)**: a class killed by
  `i^*` is killed by `c₁^A(𝒪_P(P'))`. Condition (5) is not a field of
  `Stacks.WeilCohomology.ChernSetup`;
* the identification `c₁^A(𝒪_P(P')) = c₁^A(𝒪_P(1)) - p^*c₁^A(ℒ)`, which the source takes from
  the description of `𝐏(𝓕) ⊂ 𝐏(ℰ)` as the zero scheme of a regular section of
  `ℒ^{⊗ -1} ⊗ 𝒪_P(1)`.

Because these are hypotheses and not consequences of the situation, the result is weaker than
Tag 0FI5's and carries no tag.

The last hypothesis is also what makes `p^*c₁^A(ℒ)` central: it is the difference of the two
central classes `c₁^A(𝒪_P(1))` and `c₁^A(𝒪_P(P'))`. Condition (3) of the source,
`f^*c₁^A(ℒ) = c₁^A(f^*ℒ)`, is therefore not needed here and is not assumed.

Constant ranks are hypotheses: the source reduces to that case by condition (2), the splitting
`A(U ⨿ V) = A(U) × A(V)`, and that reduction is
`Stacks.WeilCohomology.SourceChernSetup.exists_clopenRankPieces`, which is not applied here. The
sequence `0 ⟶ ℒ ⟶ ℰ ⟶ 𝓕 ⟶ 0` itself does not appear in the statement — only the
data the source's proof extracts from it: the ranks `r + 2` and `r + 1`, the class of `ℒ` in
`Pic(X)`, and the closed immersion of projective bundles the surjection `ℰ ⟶ 𝓕` induces.

## References

* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v₁ w

namespace Stacks.WeilCohomology

/-! ### The ring-theoretic expansion -/

/-- **The expansion behind the Whitney sum formula.** Let `φ : A₁ ⟶ A₂` be a ring map, let
`x ∈ A₂`, let `l ∈ A₁` have central image, and let `cF : ℕ → A₁` satisfy `cF_0 = 1` and
`cF_j = 0` for `j > r + 1`. Write
`a = ∑_{k=0}^{r+1} (-1)^k x^k φ(cF_{r+1-k})`
and suppose `x a = φ(l) a`. Then the family `d` with `d_0 = 1` and
`d_{j+1} = cF_{j+1} + l · cF_j` satisfies
`∑_{k=0}^{r+2} (-1)^k x^k φ(d_{r+2-k}) = 0`.

Only the two top terms of the expansion survive, and they cancel: the `cF` half of the sum is
`-x a + (-1)^{r+1} x^{r+2}`, the `l · cF` half is `φ(l) a`, and the term at `k = r + 2` is
`(-1)^{r+2} x^{r+2}`. -/
theorem sum_eq_zero_of_divisorRelation {A₁ A₂ : Type*} [Ring A₁] [Ring A₂]
    (φ : A₁ →+* A₂) (x : A₂) (l : A₁) (cF d : ℕ → A₁) (r : ℕ)
    (hcF0 : cF 0 = 1) (hcFgt : ∀ j : ℕ, r + 1 < j → cF j = 0)
    (hd0 : d 0 = 1) (hdsucc : ∀ j : ℕ, d (j + 1) = cF (j + 1) + l * cF j)
    (hcomm : ∀ b : A₂, φ l * b = b * φ l)
    (hkey : x * (∑ k ∈ Finset.range (r + 2), ((-1 : ℤ) ^ k) • (x ^ k * φ (cF (r + 1 - k)))) =
      φ l * ∑ k ∈ Finset.range (r + 2), ((-1 : ℤ) ^ k) • (x ^ k * φ (cF (r + 1 - k)))) :
    ∑ k ∈ Finset.range (r + 3), ((-1 : ℤ) ^ k) • (x ^ k * φ (d (r + 2 - k))) = 0 := by
  classical
  set a : A₂ := ∑ k ∈ Finset.range (r + 2), ((-1 : ℤ) ^ k) • (x ^ k * φ (cF (r + 1 - k)))
    with ha
  -- the top term of such a sum, where the coefficient family is `1` at `0`
  have hone : ∀ (c : ℕ → A₁) (m : ℕ), c 0 = 1 → x ^ m * φ (c (m - m)) = x ^ m := fun c m h => by
    rw [Nat.sub_self, h, map_one, mul_one]
  rw [Finset.sum_range_succ, hone d _ hd0]
  have hexp : ∀ k ∈ Finset.range (r + 2),
      ((-1 : ℤ) ^ k) • (x ^ k * φ (d (r + 2 - k))) =
        ((-1 : ℤ) ^ k) • (x ^ k * φ (cF (r + 2 - k)))
          + φ l * (((-1 : ℤ) ^ k) • (x ^ k * φ (cF (r + 1 - k)))) := by
    intro k hk
    have hk' : k ≤ r + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hstep : d (r + 2 - k) = cF (r + 2 - k) + l * cF (r + 1 - k) := by
      obtain ⟨m, hm⟩ : ∃ m, r + 2 - k = m + 1 := ⟨r + 1 - k, by omega⟩
      rw [hm, hdsucc, show m = r + 1 - k from by omega]
    rw [hstep, map_add, map_mul, mul_add, smul_add]
    congr 1
    rw [← mul_assoc, ← hcomm (x ^ k), mul_assoc, ← mul_smul_comm]
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ← Finset.mul_sum, ← ha]
  have hsplit : a = (∑ k ∈ Finset.range (r + 1),
      ((-1 : ℤ) ^ k) • (x ^ k * φ (cF (r + 1 - k)))) + ((-1 : ℤ) ^ (r + 1)) • x ^ (r + 1) := by
    rw [ha, Finset.sum_range_succ]
    rw [hone _ _ hcF0]
  have hS1 : ∑ k ∈ Finset.range (r + 2), ((-1 : ℤ) ^ k) • (x ^ k * φ (cF (r + 2 - k))) =
      -(x * a) + ((-1 : ℤ) ^ (r + 1)) • x ^ (r + 2) := by
    rw [Finset.sum_range_succ' (fun k => ((-1 : ℤ) ^ k) • (x ^ k * φ (cF (r + 2 - k)))) (r + 1)]
    have hfirst : ((-1 : ℤ) ^ 0) • (x ^ 0 * φ (cF (r + 2 - 0))) = 0 := by
      rw [Nat.sub_zero, hcFgt (r + 2) (by omega)]
      simp
    rw [hfirst, add_zero]
    have hshift : ∀ k ∈ Finset.range (r + 1),
        ((-1 : ℤ) ^ (k + 1)) • (x ^ (k + 1) * φ (cF (r + 2 - (k + 1)))) =
          -x * (((-1 : ℤ) ^ k) • (x ^ k * φ (cF (r + 1 - k)))) := by
      intro k _
      rw [show r + 2 - (k + 1) = r + 1 - k from by omega, pow_succ' x k, mul_assoc,
        pow_succ (-1 : ℤ) k, mul_smul, neg_one_zsmul, smul_neg, ← mul_smul_comm, neg_mul]
    rw [Finset.sum_congr rfl hshift, ← Finset.mul_sum,
      show (∑ k ∈ Finset.range (r + 1), ((-1 : ℤ) ^ k) • (x ^ k * φ (cF (r + 1 - k))))
        = a - ((-1 : ℤ) ^ (r + 1)) • x ^ (r + 1) from by rw [hsplit]; abel,
      mul_sub, neg_mul, neg_mul, mul_smul_comm, ← pow_succ' x (r + 1)]
    abel
  rw [hS1]
  have hAC : -(x * a) + φ l * a = 0 := by rw [hkey]; abel
  have hcancel : ((-1 : ℤ) ^ (r + 1)) • x ^ (r + 2) + ((-1 : ℤ) ^ (r + 2)) • x ^ (r + 2) =
      (0 : A₂) := by
    rw [← add_smul, show ((-1 : ℤ) ^ (r + 1) + (-1 : ℤ) ^ (r + 2)) = 0 from by rw [pow_succ]; ring,
      zero_smul]
  rw [show -(x * a) + ((-1 : ℤ) ^ (r + 1)) • x ^ (r + 2) + φ l * a
        + ((-1 : ℤ) ^ (r + 2)) • x ^ (r + 2)
      = (-(x * a) + φ l * a)
        + (((-1 : ℤ) ^ (r + 1)) • x ^ (r + 2) + ((-1 : ℤ) ^ (r + 2)) • x ^ (r + 2)) from by abel,
    hAC, hcancel, add_zero]

/-! ### The Whitney sum formula -/

namespace ChernSetup

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **The Whitney sum formula for an invertible submodule.** Let `0 ⟶ ℒ ⟶ ℰ ⟶ 𝓕 ⟶ 0` be a short
exact sequence of finite locally free `𝒪_X`-modules with `ℒ` invertible of class `Lc` in
`Pic(X)`, with `ℰ` of constant rank `r + 2` and `𝓕` of constant rank `r + 1`. Write
`p : P = 𝐏(ℰ) ⟶ X` and `p' : P' = 𝐏(𝓕) ⟶ X` for the projective bundles. Suppose given

* the closed immersion `i : P' ⟶ P` over `X` induced by the surjection `ℰ ⟶ 𝓕`, under which
  `c₁^A(𝒪_P(1))` restricts to `c₁^A(𝒪_{P'}(1))`;
* the class `D = 𝒪_P(P') ∈ Pic(P)` with `c₁^A(D) = c₁^A(𝒪_P(1)) - p^*c₁^A(ℒ)`, and condition (5)
  of the standing situation for it.

Then `c^A_{n+1}(ℰ) = c^A_{n+1}(𝓕) + c₁^A(ℒ) ∪ c^A_n(𝓕)`.

Equation 45.12.1.1 for `𝓕`, pulled back along `i`, says that
`a = ∑_k (-1)^k c₁^A(𝒪_P(1))^k ∪ p^*c^A_{r+1-k}(𝓕)` is killed by `i^*`; condition (5) then
kills `a ∪ c₁^A(D)`, and expanding `c₁^A(D)` turns that into equation 45.12.1.1 for `ℰ` with
`c^A_j(ℰ)` replaced by `c^A_j(𝓕) + c₁^A(ℒ) ∪ c^A_{j-1}(𝓕)`. -/
theorem chernClass_add_one_of_invertibleSub (𝔄 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (E F : (S.obj X).Modules) (Lc : (S.obj X).picardGroup) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1 + 1))
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (r + 1))
    (i : (𝔄.bundleDatum X F r hF).bundle ⟶ (𝔄.bundleDatum X E (r + 1) hE).bundle)
    (hi : i ≫ (𝔄.bundleDatum X E (r + 1) hE).proj = (𝔄.bundleDatum X F r hF).proj)
    (hitwist : 𝔄.pull i (𝔄.c₁ (𝔄.bundleDatum X E (r + 1) hE).bundle
        (𝔄.bundleDatum X E (r + 1) hE).twistClass) =
      𝔄.c₁ (𝔄.bundleDatum X F r hF).bundle (𝔄.bundleDatum X F r hF).twistClass)
    (D : (S.obj (𝔄.bundleDatum X E (r + 1) hE).bundle).picardGroup)
    (hD : 𝔄.c₁ (𝔄.bundleDatum X E (r + 1) hE).bundle D =
      𝔄.c₁ (𝔄.bundleDatum X E (r + 1) hE).bundle (𝔄.bundleDatum X E (r + 1) hE).twistClass -
        𝔄.pull (𝔄.bundleDatum X E (r + 1) hE).proj (𝔄.c₁ X Lc))
    (hdiv : ∀ a : 𝔄.A (𝔄.bundleDatum X E (r + 1) hE).bundle, 𝔄.pull i a = 0 →
      a * 𝔄.c₁ (𝔄.bundleDatum X E (r + 1) hE).bundle D = 0)
    (n : ℕ) :
    𝔄.chernClass X E (r + 1) hE (n + 1) =
      𝔄.chernClass X F r hF (n + 1) + 𝔄.c₁ X Lc * 𝔄.chernClass X F r hF n := by
  classical
  have hcFgt : ∀ j : ℕ, r + 1 < j → 𝔄.chernClass X F r hF j = 0 := fun j hj =>
    𝔄.chernClass_of_gt X F r hF hj
  -- `p^*c₁^A(ℒ) = c₁^A(𝒪_P(1)) - c₁^A(D)` is central, being a difference of central classes
  have hLeq : 𝔄.pull (𝔄.bundleDatum X E (r + 1) hE).proj (𝔄.c₁ X Lc) =
      𝔄.c₁ (𝔄.bundleDatum X E (r + 1) hE).bundle (𝔄.bundleDatum X E (r + 1) hE).twistClass -
        𝔄.c₁ (𝔄.bundleDatum X E (r + 1) hE).bundle D := by rw [hD]; abel
  have hcomm : ∀ b : 𝔄.A (𝔄.bundleDatum X E (r + 1) hE).bundle,
      𝔄.pull (𝔄.bundleDatum X E (r + 1) hE).proj (𝔄.c₁ X Lc) * b =
        b * 𝔄.pull (𝔄.bundleDatum X E (r + 1) hE).proj (𝔄.c₁ X Lc) := by
    intro b
    rw [hLeq, sub_mul, mul_sub, 𝔄.c₁_central _ _ b, 𝔄.c₁_central _ D b]
  -- equation 45.12.1.1 for `𝓕`, as a sum over `Finset.range`
  have hFrel : ∑ k ∈ Finset.range (r + 2), ((-1 : ℤ) ^ k) •
      (𝔄.c₁ (𝔄.bundleDatum X F r hF).bundle (𝔄.bundleDatum X F r hF).twistClass ^ k *
        𝔄.pull (𝔄.bundleDatum X F r hF).proj (𝔄.chernClass X F r hF (r + 1 - k))) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => ((-1 : ℤ) ^ k) •
      (𝔄.c₁ (𝔄.bundleDatum X F r hF).bundle (𝔄.bundleDatum X F r hF).twistClass ^ k *
        𝔄.pull (𝔄.bundleDatum X F r hF).proj (𝔄.chernClass X F r hF (r + 1 - k)))) (r + 2)]
    exact 𝔄.sum_chernClass_eq_zero X F r hF
  -- the element of `A(P)` that condition (5) is applied to
  set a := ∑ k ∈ Finset.range (r + 2), ((-1 : ℤ) ^ k) •
      (𝔄.c₁ (𝔄.bundleDatum X E (r + 1) hE).bundle
            (𝔄.bundleDatum X E (r + 1) hE).twistClass ^ k *
        𝔄.pull (𝔄.bundleDatum X E (r + 1) hE).proj
          (𝔄.chernClass X F r hF (r + 1 - k))) with ha
  -- `a` is killed by `i^*`
  have hia : 𝔄.pull i a = 0 := by
    rw [ha, map_sum, ← hFrel]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, map_mul, map_pow, hitwist, ← RingHom.comp_apply,
      ← 𝔄.pull_comp i (𝔄.bundleDatum X E (r + 1) hE).proj, hi]
  -- condition (5), with `c₁^A(D) = x - Λ` and both factors central
  have hkey : 𝔄.c₁ (𝔄.bundleDatum X E (r + 1) hE).bundle
        (𝔄.bundleDatum X E (r + 1) hE).twistClass * a =
      𝔄.pull (𝔄.bundleDatum X E (r + 1) hE).proj (𝔄.c₁ X Lc) * a := by
    have h := hdiv _ hia
    rw [← 𝔄.c₁_central _ D _, hD, sub_mul, sub_eq_zero] at h
    exact h
  -- the candidate family of Chern classes of `ℰ`
  obtain ⟨d, hd0, hdsucc⟩ : ∃ d : ℕ → 𝔄.A X, d 0 = 1 ∧
      ∀ j : ℕ, d (j + 1) =
        𝔄.chernClass X F r hF (j + 1) + 𝔄.c₁ X Lc * 𝔄.chernClass X F r hF j :=
    ⟨fun j => if j = 0 then 1 else
      𝔄.chernClass X F r hF j + 𝔄.c₁ X Lc * 𝔄.chernClass X F r hF (j - 1), by simp,
      by intro j; simp⟩
  have hdtop : ∀ j : ℕ, r + 1 + 1 < j → d j = 0 := by
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [hdsucc, hcFgt (j' + 1) (by omega), hcFgt j' (by omega), mul_zero, add_zero]
  have hmain := sum_eq_zero_of_divisorRelation
    (𝔄.pull (𝔄.bundleDatum X E (r + 1) hE).proj)
    (𝔄.c₁ (𝔄.bundleDatum X E (r + 1) hE).bundle (𝔄.bundleDatum X E (r + 1) hE).twistClass)
    (𝔄.c₁ X Lc) (𝔄.chernClass X F r hF) d r (𝔄.chernClass_zero X F r hF) hcFgt hd0 hdsucc
    hcomm hkey
  have hrel : ∑ k : Fin (r + 1 + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      (𝔄.c₁ (𝔄.bundleDatum X E (r + 1) hE).bundle
            (𝔄.bundleDatum X E (r + 1) hE).twistClass ^ (k : ℕ) *
        𝔄.pull (𝔄.bundleDatum X E (r + 1) hE).proj (d (r + 1 + 1 - (k : ℕ)))) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => ((-1 : ℤ) ^ k) •
      (𝔄.c₁ (𝔄.bundleDatum X E (r + 1) hE).bundle
            (𝔄.bundleDatum X E (r + 1) hE).twistClass ^ k *
        𝔄.pull (𝔄.bundleDatum X E (r + 1) hE).proj (d (r + 1 + 1 - k)))) (r + 1 + 2)]
    exact hmain
  rw [← 𝔄.chernClass_eq_of_relation X E (r + 1) hE d hd0 hdtop hrel (n + 1), hdsucc]

end ChernSetup

end Stacks.WeilCohomology

end
