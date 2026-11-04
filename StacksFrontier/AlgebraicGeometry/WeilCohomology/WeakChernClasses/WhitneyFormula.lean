module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.WhitneyFormula
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.TotalChernClass

/-!
# The Whitney sum formula for an invertible submodule, in the weak standing situation

The Whitney sum formula for an invertible submodule, stated for
`Stacks.WeilCohomology.Weak.ChernSetup`: the standing situation of Stacks Section 45.12 in which
the projective bundle formula, condition (4), is only asked to be injective and to resolve the top
power `c₁^A(𝒪_P(1))^{r+1}` of the twist class. The proofs use condition (4) only through these two
properties.

## References

* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v₁ w

namespace Stacks.WeilCohomology.Weak

/-! ### The ring-theoretic expansion -/

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
theorem chernClass_add_one_of_invertibleSub (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (E F : (S.obj X).Modules) (Lc : (S.obj X).picardGroup) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1 + 1))
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (r + 1))
    (i : (𝔚.bundleDatum X F r hF).bundle ⟶ (𝔚.bundleDatum X E (r + 1) hE).bundle)
    (hi : i ≫ (𝔚.bundleDatum X E (r + 1) hE).proj = (𝔚.bundleDatum X F r hF).proj)
    (hitwist : 𝔚.pull i (𝔚.c₁ (𝔚.bundleDatum X E (r + 1) hE).bundle
        (𝔚.bundleDatum X E (r + 1) hE).twistClass) =
      𝔚.c₁ (𝔚.bundleDatum X F r hF).bundle (𝔚.bundleDatum X F r hF).twistClass)
    (D : (S.obj (𝔚.bundleDatum X E (r + 1) hE).bundle).picardGroup)
    (hD : 𝔚.c₁ (𝔚.bundleDatum X E (r + 1) hE).bundle D =
      𝔚.c₁ (𝔚.bundleDatum X E (r + 1) hE).bundle (𝔚.bundleDatum X E (r + 1) hE).twistClass -
        𝔚.pull (𝔚.bundleDatum X E (r + 1) hE).proj (𝔚.c₁ X Lc))
    (hdiv : ∀ a : 𝔚.A (𝔚.bundleDatum X E (r + 1) hE).bundle, 𝔚.pull i a = 0 →
      a * 𝔚.c₁ (𝔚.bundleDatum X E (r + 1) hE).bundle D = 0)
    (n : ℕ) :
    𝔚.chernClass X E (r + 1) hE (n + 1) =
      𝔚.chernClass X F r hF (n + 1) + 𝔚.c₁ X Lc * 𝔚.chernClass X F r hF n := by
  classical
  have hcFgt : ∀ j : ℕ, r + 1 < j → 𝔚.chernClass X F r hF j = 0 := fun j hj =>
    𝔚.chernClass_of_gt X F r hF hj
  -- `p^*c₁^A(ℒ) = c₁^A(𝒪_P(1)) - c₁^A(D)` is central, being a difference of central classes
  have hLeq : 𝔚.pull (𝔚.bundleDatum X E (r + 1) hE).proj (𝔚.c₁ X Lc) =
      𝔚.c₁ (𝔚.bundleDatum X E (r + 1) hE).bundle (𝔚.bundleDatum X E (r + 1) hE).twistClass -
        𝔚.c₁ (𝔚.bundleDatum X E (r + 1) hE).bundle D := by rw [hD]; abel
  have hcomm : ∀ b : 𝔚.A (𝔚.bundleDatum X E (r + 1) hE).bundle,
      𝔚.pull (𝔚.bundleDatum X E (r + 1) hE).proj (𝔚.c₁ X Lc) * b =
        b * 𝔚.pull (𝔚.bundleDatum X E (r + 1) hE).proj (𝔚.c₁ X Lc) := by
    intro b
    rw [hLeq, sub_mul, mul_sub, 𝔚.c₁_central _ _ b, 𝔚.c₁_central _ D b]
  -- equation 45.12.1.1 for `𝓕`, as a sum over `Finset.range`
  have hFrel : ∑ k ∈ Finset.range (r + 2), ((-1 : ℤ) ^ k) •
      (𝔚.c₁ (𝔚.bundleDatum X F r hF).bundle (𝔚.bundleDatum X F r hF).twistClass ^ k *
        𝔚.pull (𝔚.bundleDatum X F r hF).proj (𝔚.chernClass X F r hF (r + 1 - k))) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact 𝔚.sum_chernClass_eq_zero X F r hF
  -- the element of `A(P)` that condition (5) is applied to is killed by `i^*`
  have hia : 𝔚.pull i (∑ k ∈ Finset.range (r + 2), ((-1 : ℤ) ^ k) •
      (𝔚.c₁ (𝔚.bundleDatum X E (r + 1) hE).bundle
            (𝔚.bundleDatum X E (r + 1) hE).twistClass ^ k *
        𝔚.pull (𝔚.bundleDatum X E (r + 1) hE).proj
          (𝔚.chernClass X F r hF (r + 1 - k)))) = 0 := by
    rw [map_sum, ← hFrel]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, map_mul, map_pow, hitwist, ← RingHom.comp_apply,
      ← 𝔚.pull_comp i (𝔚.bundleDatum X E (r + 1) hE).proj, hi]
  -- condition (5), with `c₁^A(D) = x - Λ` and both factors central
  have hkey : 𝔚.c₁ (𝔚.bundleDatum X E (r + 1) hE).bundle
        (𝔚.bundleDatum X E (r + 1) hE).twistClass *
      (∑ k ∈ Finset.range (r + 2), ((-1 : ℤ) ^ k) •
        (𝔚.c₁ (𝔚.bundleDatum X E (r + 1) hE).bundle
              (𝔚.bundleDatum X E (r + 1) hE).twistClass ^ k *
          𝔚.pull (𝔚.bundleDatum X E (r + 1) hE).proj
            (𝔚.chernClass X F r hF (r + 1 - k)))) =
      𝔚.pull (𝔚.bundleDatum X E (r + 1) hE).proj (𝔚.c₁ X Lc) *
      ∑ k ∈ Finset.range (r + 2), ((-1 : ℤ) ^ k) •
        (𝔚.c₁ (𝔚.bundleDatum X E (r + 1) hE).bundle
              (𝔚.bundleDatum X E (r + 1) hE).twistClass ^ k *
          𝔚.pull (𝔚.bundleDatum X E (r + 1) hE).proj
            (𝔚.chernClass X F r hF (r + 1 - k))) := by
    have h := hdiv _ hia
    rw [← 𝔚.c₁_central _ D _, hD, sub_mul, sub_eq_zero] at h
    exact h
  -- the candidate family of Chern classes of `ℰ`
  obtain ⟨d, hd0, hdsucc⟩ : ∃ d : ℕ → 𝔚.A X, d 0 = 1 ∧
      ∀ j : ℕ, d (j + 1) =
        𝔚.chernClass X F r hF (j + 1) + 𝔚.c₁ X Lc * 𝔚.chernClass X F r hF j :=
    ⟨fun j => if j = 0 then 1 else
      𝔚.chernClass X F r hF j + 𝔚.c₁ X Lc * 𝔚.chernClass X F r hF (j - 1), by simp,
      by intro j; simp⟩
  have hdtop : ∀ j : ℕ, r + 1 + 1 < j → d j = 0 := by
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [hdsucc, hcFgt (j' + 1) (by omega), hcFgt j' (by omega), mul_zero, add_zero]
  have hmain := sum_eq_zero_of_divisorRelation
    (𝔚.pull (𝔚.bundleDatum X E (r + 1) hE).proj)
    (𝔚.c₁ (𝔚.bundleDatum X E (r + 1) hE).bundle (𝔚.bundleDatum X E (r + 1) hE).twistClass)
    (𝔚.c₁ X Lc) (𝔚.chernClass X F r hF) d r (𝔚.chernClass_zero X F r hF) hcFgt hd0 hdsucc
    hcomm hkey
  have hrel : ∑ k : Fin (r + 1 + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      (𝔚.c₁ (𝔚.bundleDatum X E (r + 1) hE).bundle
            (𝔚.bundleDatum X E (r + 1) hE).twistClass ^ (k : ℕ) *
        𝔚.pull (𝔚.bundleDatum X E (r + 1) hE).proj (d (r + 1 + 1 - (k : ℕ)))) = 0 := by
    exact (Fin.sum_univ_eq_sum_range (fun k => _) _).trans hmain
  rw [← 𝔚.chernClass_eq_of_relation X E (r + 1) hE d hd0 hdtop hrel (n + 1), hdsucc]

end ChernSetup

end Stacks.WeilCohomology.Weak

end
