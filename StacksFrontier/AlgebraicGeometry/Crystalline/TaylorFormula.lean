module

public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorCocycle
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Taylor's formula and the semilinearity of the Taylor comparison of [Stacks, Tag 07JH]

The `f`-semilinearity of the Taylor sum `m ↦ ∑_K ξ^{[K]} ⊗ θ_K(m)`,

`∑_K ξ^{[K]} ⊗ θ_K(a m) = f(a) · ∑_K ξ^{[K]} ⊗ θ_K(m)`,

is reduced to Taylor's formula in `B`,

`f(a) = ∑_J g(∂_J a) ξ^{[J]}`,

which involves the two rings, the two divided power maps and the coordinate operators of `D`, and
no module and no connection. The module half of the reduction is the Leibniz rule for the
composite coordinate operators

`θ_L (a · m) = ∑_{J + K = L} (∏_i binom(l_i, j_i)) · (∂_J a · θ_K m)`,

derived from the first-order Leibniz rule `θ_i (a m) = a θ_i m + ∂_i(a) m`. Its binomial
coefficients are those of `DividedPowers.prod_dpow_mul`, which multiplies two divided power
monomials of the same family.

## Main results

* `Crystalline.iterate_smul_eq`: the Leibniz rule for the iterates of one coordinate operator,
  `θ^n (a m) = ∑_{j + k = n} binom(n, j) · (δ^j a · θ^k m)`.
* `Crystalline.thetaPow_smul_eq` and `Crystalline.thetaPow_smul_eq_support`: the multi-index
  Leibniz rule, with the coefficient product over a finite set containing the support of the
  multi-index and over that support itself.
* `Crystalline.taylorMonomial_mul`: `ξ^{[J]} ξ^{[K]} = (∏_i binom(j_i + k_i, j_i)) ξ^{[J + K]}`.
* `Crystalline.taylorSum_smul_eq_of_taylorFormula`: the `f`-semilinearity of the Taylor sum, from
  the Leibniz rule and Taylor's formula in `B`.
* `Crystalline.exists_isTwistedTaylorComparison_of_taylorFormula`: the Taylor comparison predicate
  `Crystalline.IsTwistedTaylorComparison` is inhabited as soon as Taylor's formula holds in `B`.
* `Crystalline.taylorFormula_refl`: Taylor's formula in `B` holds at the datum `f = g`.
* `Crystalline.iterate_map_sum` and `Crystalline.iterate_map_nsmul`: an iterate of an additive map
  commutes with a finite sum and with multiplication by a natural number.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
-/

@[expose] public section

open scoped TensorProduct

-- The name `Finset.antidiagonal` is ambiguous once `Mathlib/Data/Finset/MulAntidiagonal.lean`
-- is in scope: the additive form of `Finset.mulAntidiagonal` carries it too, with a different
-- signature. This opens the `Finset.HasAntidiagonal` one.
open Finset.HasAntidiagonal

universe u uI w

namespace Crystalline

/-! ### The Leibniz rule for the iterates of one coordinate operator -/

section OneVariable

variable {D : Type u} [CommRing D] {M : Type w} [AddCommGroup M] [Module D M]

/-- An additive map commutes with a finite sum. -/
theorem iterate_map_sum {f : M → M} (hf : ∀ x y, f (x + y) = f x + f y) (b : ℕ) {α : Type*}
    (s : Finset α) (g : α → M) : f^[b] (∑ x ∈ s, g x) = ∑ x ∈ s, f^[b] (g x) :=
  map_sum (AddMonoidHom.mk' f^[b] (iterate_map_add hf b)) g s

/-- An additive map commutes with multiplication by a natural number. -/
theorem iterate_map_nsmul {f : M → M} (hf : ∀ x y, f (x + y) = f x + f y) (b c : ℕ) (x : M) :
    f^[b] (c • x) = c • f^[b] x :=
  (AddMonoidHom.mk' f^[b] (iterate_map_add hf b)).map_nsmul c x

/-- **The Leibniz rule for the iterates of a coordinate operator.** If `θ` is additive and obeys
the first-order Leibniz rule `θ (a · m) = a · θ m + δ(a) · m` for an operator `δ` on the ring, then

`θ^n (a · m) = ∑_{j + k = n} binom(n, j) · (δ^j a · θ^k m)`. -/
@[sga "3 VIIA 5.2" "more general"]
theorem iterate_smul_eq {th : M → M} {de : D → D} (hth : ∀ x y, th (x + y) = th x + th y)
    (hleib : ∀ (a : D) (m : M), th (a • m) = a • th m + de a • m) (n : ℕ) (a : D) (m : M) :
    th^[n] (a • m) = ∑ q ∈ antidiagonal n, n.choose q.1 • (de^[q.1] a • th^[q.2] m) := by
  induction n generalizing a m with
  | zero => simp
  | succ n ih =>
      have hA : th^[n] (a • th m) =
          ∑ q ∈ antidiagonal (n + 1), n.choose q.1 • (de^[q.1] a • th^[q.2] m) := by
        rw [Finset.Nat.sum_antidiagonal_succ' (f := fun q : ℕ × ℕ ↦
            n.choose q.1 • (de^[q.1] a • th^[q.2] m)), Nat.choose_succ_self, zero_smul,
          zero_add, ih a (th m)]
        exact Finset.sum_congr rfl fun q _ ↦ by rw [Function.iterate_succ_apply]
      have hB : th^[n] (de a • m) =
          ∑ q ∈ antidiagonal n, n.choose q.1 • (de^[q.1 + 1] a • th^[q.2] m) := by
        rw [ih (de a) m]
        exact Finset.sum_congr rfl fun q _ ↦ by rw [Function.iterate_succ_apply]
      rw [Function.iterate_succ_apply, hleib, iterate_map_add hth, hA, hB,
        Finset.Nat.sum_antidiagonal_succ (f := fun q : ℕ × ℕ ↦
          (n + 1).choose q.1 • (de^[q.1] a • th^[q.2] m)),
        Finset.Nat.sum_antidiagonal_succ (f := fun q : ℕ × ℕ ↦
          n.choose q.1 • (de^[q.1] a • th^[q.2] m)),
        add_assoc, ← Finset.sum_add_distrib]
      refine congrArg₂ _ (by rw [Nat.choose_zero_right, Nat.choose_zero_right])
        (Finset.sum_congr rfl fun q _ ↦ ?_)
      rw [Nat.choose_succ_succ', add_smul, add_comm]

end OneVariable

/-! ### The Leibniz rule for the composite coordinate operators -/

section MultiIndex

variable {D : Type u} [CommRing D] {M : Type w} [AddCommGroup M] [Module D M] {ι : Type uI}
  [DecidableEq ι] {theta : ι → (M → M)} {thetaPow : (ι →₀ ℕ) → (M → M)} {delta : ι → (D → D)}
  {deltaPow : (ι →₀ ℕ) → (D → D)}

/-- **The Leibniz rule for the composite coordinate operators of [Stacks, Tag 07JH]**:

`θ_L (a · m) = ∑_{J + K = L} (∏_i binom(l_i, j_i)) · (∂_J a · θ_K m)`,

the sum being over the antidiagonal of the multi-index `L` and the product over any finite set of
indices containing the support of `L`. Here `θ` and `∂` are composite coordinate operator families
in the sense of `Crystalline.IsThetaMonomialFamily`, on `M` and on the ring `D` respectively, the
`θ_i` are additive, and they satisfy the first-order Leibniz rule
`θ_i (a · m) = a · θ_i m + ∂_i(a) · m`. -/
@[sga "3 VIIA 5.2" "more general"]
theorem thetaPow_smul_eq (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hfamD : IsThetaMonomialFamily D delta deltaPow)
    (hthAdd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y)
    (hleib : ∀ (i : ι) (a : D) (m : M), theta i (a • m) = a • theta i m + delta i a • m)
    (a : D) (m : M) (s : Finset ι) (L : ι →₀ ℕ) (hL : L.support ⊆ s) :
    thetaPow L (a • m) =
      ∑ P ∈ antidiagonal L,
        (∏ i ∈ s, (L i).choose (P.1 i)) • (deltaPow P.1 a • thetaPow P.2 m) := by
  classical
  induction s using Finset.induction generalizing L with
  | empty =>
      have hL0 : L = 0 := Finsupp.support_eq_empty.mp (Finset.subset_empty.mp hL)
      subst hL0
      simp [hfamM.apply_zero, hfamD.apply_zero]
  | @insert j s hj ih =>
      have hne : ∀ i ∈ s, i ≠ j := fun i hi ↦ ne_of_mem_of_not_mem hi hj
      have hL' : (L.erase j).support ⊆ s := by
        intro i hi
        rw [Finsupp.support_erase, Finset.mem_erase] at hi
        exact (Finset.mem_insert.mp (hL hi.2)).resolve_left hi.1
      have heq : L.erase j + Finsupp.single j (L j) = L := by
        rw [add_comm]; exact Finsupp.single_add_erase j L
      have hthetaL : thetaPow L (a • m) =
          (theta j)^[L j] (thetaPow (L.erase j) (a • m)) :=
        congrFun (heq ▸ hfamM.add_single (L.erase j) j (L j)) (a • m)
      have hterm : ∀ P ∈ antidiagonal (L.erase j),
          (theta j)^[L j] ((∏ i ∈ s, ((L.erase j) i).choose (P.1 i)) •
              (deltaPow P.1 a • thetaPow P.2 m)) =
            ∑ uv ∈ antidiagonal (L j),
              (∏ i ∈ insert j s, (L i).choose ((Finsupp.single j uv.1 + P.1) i)) •
                (deltaPow (Finsupp.single j uv.1 + P.1) a •
                  thetaPow (Finsupp.single j uv.2 + P.2) m) := by
        intro P hP
        rw [mem_antidiagonal] at hP
        have hP1j : P.1 j = 0 := by
          have h := congrArg (fun g : ι →₀ ℕ ↦ g j) hP
          simp only [Finsupp.add_apply, Finsupp.erase_same] at h
          omega
        rw [iterate_map_nsmul (hthAdd j) (L j), iterate_smul_eq (hthAdd j) (hleib j) (L j),
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun uv _ ↦ ?_
        have hd : (delta j)^[uv.1] (deltaPow P.1 a) =
            deltaPow (Finsupp.single j uv.1 + P.1) a := by
          have h2 : Finsupp.single j uv.1 + P.1 = P.1 + Finsupp.single j uv.1 := add_comm _ _
          rw [h2, congrFun (hfamD.add_single P.1 j uv.1) a]
          rfl
        have ht : (theta j)^[uv.2] (thetaPow P.2 m) =
            thetaPow (Finsupp.single j uv.2 + P.2) m := by
          have h2 : Finsupp.single j uv.2 + P.2 = P.2 + Finsupp.single j uv.2 := add_comm _ _
          rw [h2, congrFun (hfamM.add_single P.2 j uv.2) m]
          rfl
        have hcoef : (∏ i ∈ insert j s, (L i).choose ((Finsupp.single j uv.1 + P.1) i)) =
            (∏ i ∈ s, ((L.erase j) i).choose (P.1 i)) * (L j).choose uv.1 := by
          rw [Finset.prod_insert hj, mul_comm]
          congr 1
          · refine Finset.prod_congr rfl fun i hi ↦ ?_
            rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (hne i hi), zero_add,
              Finsupp.erase_ne (hne i hi)]
          · rw [Finsupp.add_apply, Finsupp.single_eq_same, hP1j, add_zero]
        rw [hd, ht, hcoef, smul_smul]
      rw [hthetaL, ih (L.erase j) hL', iterate_map_sum (hthAdd j) (L j),
        Finset.sum_congr rfl hterm, Finset.sum_comm]
      exact (Finsupp.sum_antidiagonal_eq_sum_antidiagonal_erase j L
        (fun uu vv ↦ (∏ i ∈ insert j s, (L i).choose (uu i)) •
          (deltaPow uu a • thetaPow vv m))).symm

/-- **The Leibniz rule for the composite coordinate operators, with the product over the support
of the multi-index.** This is `Crystalline.thetaPow_smul_eq` at the index set `L.support`. -/
theorem thetaPow_smul_eq_support (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hfamD : IsThetaMonomialFamily D delta deltaPow)
    (hthAdd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y)
    (hleib : ∀ (i : ι) (a : D) (m : M), theta i (a • m) = a • theta i m + delta i a • m)
    (a : D) (m : M) (L : ι →₀ ℕ) :
    thetaPow L (a • m) =
      ∑ P ∈ antidiagonal L,
        (∏ i ∈ L.support, (L i).choose (P.1 i)) • (deltaPow P.1 a • thetaPow P.2 m) :=
  thetaPow_smul_eq hfamM hfamD hthAdd hleib a m L.support L Finset.Subset.rfl

end MultiIndex

/-! ### The product of two divided power monomials of the same family -/

section Monomial

variable (B : DividedPowerRing.{u}) {ι : Type uI} [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The product of two divided power monomials of the same family**:

`ξ^{[J]} ξ^{[K]} = (∏_i binom(j_i + k_i, j_i)) ξ^{[J + K]}`. -/
theorem taylorMonomial_mul {xi : ι → (B : Type u)} (hxi : ∀ i, xi i ∈ B.ideal) (J K : ι →₀ ℕ) :
    taylorMonomial B xi J * taylorMonomial B xi K =
      (∏ i ∈ (J + K).support, ((J + K) i).choose (J i)) • taylorMonomial B xi (J + K) := by
  classical
  simp only [taylorMonomial, nsmul_eq_mul, Nat.cast_prod]
  rw [B.dividedPowers.prod_dpow_mul_support hxi J K]
  exact congrArg₂ _ (Finset.prod_congr rfl fun i _ ↦ by rw [Finsupp.add_apply]) rfl

omit [DecidableEq ι] in
/-- **The divided power monomials of the zero family vanish away from the empty multi-index.** -/
theorem taylorMonomial_zero_family {J : ι →₀ ℕ} (hJ : J ≠ 0) :
    taylorMonomial B (0 : ι → (B : Type u)) J = 0 := by
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hJ
  rw [taylorMonomial]
  exact Finset.prod_eq_zero hi
    (B.dividedPowers.dpow_eval_zero (Finsupp.mem_support_iff.mp hi))

end Monomial

/-! ### The semilinearity of the Taylor sum -/

section Semilinear

variable (p : ℕ) {D : DividedPowerRing.{u}} {B : DividedPowerRing.{u}}
  [Algebra (D : Type u) (B : Type u)] {M : Type u} [AddCommGroup M] [Module (D : Type u) M]
  {ι : Type uI} [DecidableEq ι] {theta : ι → (M → M)} {thetaPow : (ι →₀ ℕ) → (M → M)}
  {delta : ι → (D.carrier → D.carrier)} {deltaPow : (ι →₀ ℕ) → (D.carrier → D.carrier)}

omit [DecidableEq ι] in
/-- **The `f`-semilinearity of the Taylor sum of [Stacks, Tag 07JH] modulo a submodule, from
Taylor's formula in `B`.** If `Filt` is a submodule of `B ⊗_D M` containing every `b ⊗ y` with
`y ∈ p^N M` (`hdrop`), then

`∑_{L ∈ sL} ξ^{[L]} ⊗ θ_L(a m) ≡ f(a) · ∑_{K ∈ s} ξ^{[K]} ⊗ θ_K(m)` modulo `Filt`.

Here `θ` and `∂` satisfy the hypotheses of `Crystalline.thetaPow_smul_eq`, `ξ` lies in the divided
power ideal of `B`, `θ_K m ∈ p^N M` for `K ∉ s` (`hs`), Taylor's formula
`f(a) = ∑_{J ∈ t} g(∂_J a) ξ^{[J]}` holds in `B` (`htaylor`) with every term outside `t` zero
(`htvan`), and `sL` contains every `J + K` with `J ∈ t` and `K ∈ s` (`hsL`). -/
theorem taylorSum_smul_eq_of_taylorFormula_mem (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hfamD : IsThetaMonomialFamily (D : Type u) delta deltaPow)
    (hthAdd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y)
    (hleib : ∀ (i : ι) (a : (D : Type u)) (m : M),
      theta i (a • m) = a • theta i m + delta i a • m)
    {xi : ι → (B : Type u)} (hxi : ∀ i, xi i ∈ B.ideal) {N : ℕ}
    (Filt : Submodule (B : Type u) ((B : Type u) ⊗[(D : Type u)] M))
    (hdrop : ∀ (b : (B : Type u)) {y : M}, y ∈ pPowSmul p (D : Type u) M N →
      b ⊗ₜ[(D : Type u)] y ∈ Filt)
    (f : SecondDividedPowerMap D B) (a : (D : Type u))
    (m : M) (s t sL : Finset (ι →₀ ℕ))
    (hs : ∀ K ∉ s, thetaPow K m ∈ pPowSmul p (D : Type u) M N)
    (htaylor : f.ringHom a =
      ∑ J ∈ t, algebraMap (D : Type u) (B : Type u) (deltaPow J a) * taylorMonomial B xi J)
    (htvan : ∀ J ∉ t,
      algebraMap (D : Type u) (B : Type u) (deltaPow J a) * taylorMonomial B xi J = 0)
    (hsL : ∀ J ∈ t, ∀ K ∈ s, J + K ∈ sL) :
    ∑ L ∈ sL, taylorMonomial B xi L ⊗ₜ[(D : Type u)] thetaPow L (a • m) -
      f.ringHom a • ∑ K ∈ s, taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K m ∈ Filt := by
  classical
  set F : (ι →₀ ℕ) × (ι →₀ ℕ) → (B : Type u) ⊗[(D : Type u)] M := fun P ↦
    (algebraMap (D : Type u) (B : Type u) (deltaPow P.1 a) * taylorMonomial B xi P.1 *
      taylorMonomial B xi P.2) ⊗ₜ[(D : Type u)] thetaPow P.2 m with hFdef
  have hterm : ∀ (J K : ι →₀ ℕ) (d : (D : Type u)) (y : M),
      taylorMonomial B xi (J + K) ⊗ₜ[(D : Type u)]
          ((∏ i ∈ (J + K).support, ((J + K) i).choose (J i)) • (d • y)) =
        (algebraMap (D : Type u) (B : Type u) d * taylorMonomial B xi J *
          taylorMonomial B xi K) ⊗ₜ[(D : Type u)] y := by
    intro J K d y
    have h1 : taylorMonomial B xi J * taylorMonomial B xi K =
        ((∏ i ∈ (J + K).support, ((J + K) i).choose (J i) : ℕ) : (B : Type u)) *
          taylorMonomial B xi (J + K) := by
      rw [taylorMonomial_mul B hxi J K, nsmul_eq_mul]
    have hb : ((∏ i ∈ (J + K).support, ((J + K) i).choose (J i) : ℕ) : (B : Type u)) *
          algebraMap (D : Type u) (B : Type u) d * taylorMonomial B xi (J + K) =
        algebraMap (D : Type u) (B : Type u) d * taylorMonomial B xi J *
          taylorMonomial B xi K := by
      rw [mul_assoc (algebraMap (D : Type u) (B : Type u) d), h1]
      ring
    rw [← Nat.cast_smul_eq_nsmul (D : Type u), smul_smul, ← TensorProduct.smul_tmul,
      Algebra.smul_def, map_mul, map_natCast, hb]
  have hdisj : (sL : Set (ι →₀ ℕ)).PairwiseDisjoint fun L : ι →₀ ℕ ↦ antidiagonal L := by
    intro L _ L' _ hLL'
    simp only [Function.onFun, Finset.disjoint_left]
    intro P hP hP'
    exact hLL' ((mem_antidiagonal.mp hP).symm.trans (mem_antidiagonal.mp hP'))
  have hA : ∑ L ∈ sL, taylorMonomial B xi L ⊗ₜ[(D : Type u)] thetaPow L (a • m) =
      ∑ P ∈ sL.biUnion fun L ↦ antidiagonal L, F P := by
    rw [Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun L _ ↦ ?_
    rw [thetaPow_smul_eq_support hfamM hfamD hthAdd hleib a m L, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun P hP ↦ ?_
    rw [mem_antidiagonal] at hP
    subst hP
    exact hterm P.1 P.2 (deltaPow P.1 a) (thetaPow P.2 m)
  have hsub : t ×ˢ s ⊆ sL.biUnion fun L ↦ antidiagonal L := by
    intro P hP
    obtain ⟨hP1, hP2⟩ := Finset.mem_product.mp hP
    exact Finset.mem_biUnion.mpr
      ⟨P.1 + P.2, hsL P.1 hP1 P.2 hP2, mem_antidiagonal.mpr rfl⟩
  have hB : ∑ P ∈ sL.biUnion fun L ↦ antidiagonal L, F P - ∑ P ∈ t ×ˢ s, F P ∈ Filt := by
    rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
    refine Submodule.sum_mem _ fun P hP ↦ ?_
    obtain ⟨-, hPn⟩ := Finset.mem_sdiff.mp hP
    by_cases h1 : P.1 ∈ t
    · exact hdrop _ (hs P.2 fun h ↦ hPn (Finset.mem_product.mpr ⟨h1, h⟩))
    · change (algebraMap (D : Type u) (B : Type u) (deltaPow P.1 a) * taylorMonomial B xi P.1 *
        taylorMonomial B xi P.2) ⊗ₜ[(D : Type u)] thetaPow P.2 m ∈ Filt
      rw [htvan P.1 h1, zero_mul, TensorProduct.zero_tmul]
      exact Submodule.zero_mem _
  have hC : ∑ P ∈ t ×ˢ s, F P =
      f.ringHom a • ∑ K ∈ s, taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K m := by
    rw [Finset.sum_product, Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun K _ ↦ ?_
    simp only [hFdef]
    rw [← TensorProduct.sum_tmul, ← Finset.sum_mul, ← htaylor, ← smul_eq_mul,
      TensorProduct.smul_tmul']
  rw [hA, ← hC]
  exact hB

omit [DecidableEq ι] in
/-- **The `f`-semilinearity of the Taylor sum of [Stacks, Tag 07JH], from Taylor's formula in
`B`.** If `p^N = 0` in `B` then, under the hypotheses of
`Crystalline.taylorSum_smul_eq_of_taylorFormula_mem`,

`∑_{L ∈ sL} ξ^{[L]} ⊗ θ_L(a m) = f(a) · ∑_{K ∈ s} ξ^{[K]} ⊗ θ_K(m)`. -/
theorem taylorSum_smul_eq_of_taylorFormula (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hfamD : IsThetaMonomialFamily (D : Type u) delta deltaPow)
    (hthAdd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y)
    (hleib : ∀ (i : ι) (a : (D : Type u)) (m : M),
      theta i (a • m) = a • theta i m + delta i a • m)
    {xi : ι → (B : Type u)} (hxi : ∀ i, xi i ∈ B.ideal) {N : ℕ}
    (hpB : ((p : (B : Type u))) ^ N = 0) (f : SecondDividedPowerMap D B) (a : (D : Type u))
    (m : M) (s t sL : Finset (ι →₀ ℕ))
    (hs : ∀ K ∉ s, thetaPow K m ∈ pPowSmul p (D : Type u) M N)
    (htaylor : f.ringHom a =
      ∑ J ∈ t, algebraMap (D : Type u) (B : Type u) (deltaPow J a) * taylorMonomial B xi J)
    (htvan : ∀ J ∉ t,
      algebraMap (D : Type u) (B : Type u) (deltaPow J a) * taylorMonomial B xi J = 0)
    (hsL : ∀ J ∈ t, ∀ K ∈ s, J + K ∈ sL) :
    ∑ L ∈ sL, taylorMonomial B xi L ⊗ₜ[(D : Type u)] thetaPow L (a • m) =
      f.ringHom a • ∑ K ∈ s, taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K m := by
  have hmem := taylorSum_smul_eq_of_taylorFormula_mem p hfamM hfamD hthAdd hleib hxi ⊥
    (fun b _ hy ↦ (Submodule.mem_bot _).mpr (tmul_eq_zero_of_mem_pPowSmul hpB b hy)) f a m s t sL
    hs htaylor htvan hsL
  rwa [Submodule.mem_bot, sub_eq_zero] at hmem

omit [DecidableEq ι] in
/-- **The Taylor comparison predicate of [Stacks, Tag 07JH] holds as soon as Taylor's formula
holds in `B`.** Suppose `p^N = 0` in `B`, the set of multi-indices `L` with `θ_L m ∉ p^N M` is
finite for every `m` (`hfin`), and for every `a ∈ D` Taylor's formula

`f(a) = ∑_J g(∂_J a) ξ^{[J]}`

holds with a finite sum (`htay`). Then there is an `f`-semilinear map `T : M → B ⊗_D M` with
`Crystalline.IsTwistedTaylorComparison p D B M f thetaPow xi T`. -/
theorem exists_isTwistedTaylorComparison_of_taylorFormula
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hfamD : IsThetaMonomialFamily (D : Type u) delta deltaPow)
    (hthAdd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y)
    (hleib : ∀ (i : ι) (a : (D : Type u)) (m : M),
      theta i (a • m) = a • theta i m + delta i a • m)
    {xi : ι → (B : Type u)} (hxi : ∀ i, xi i ∈ B.ideal) {N : ℕ}
    (hpB : ((p : (B : Type u))) ^ N = 0) (f : SecondDividedPowerMap D B)
    (htay : ∀ a : (D : Type u), ∃ t : Finset (ι →₀ ℕ),
      (f.ringHom a = ∑ J ∈ t,
          algebraMap (D : Type u) (B : Type u) (deltaPow J a) * taylorMonomial B xi J) ∧
        ∀ J ∉ t, algebraMap (D : Type u) (B : Type u) (deltaPow J a) *
          taylorMonomial B xi J = 0)
    (hfin : ∀ m : M, {L : ι →₀ ℕ | thetaPow L m ∉ pPowSmul p (D : Type u) M N}.Finite) :
    ∃ T : M →ₛₗ[f.ringHom] ((B : Type u) ⊗[(D : Type u)] M),
      IsTwistedTaylorComparison p D B M f thetaPow xi T := by
  classical
  set G : M → (ι →₀ ℕ) → (B : Type u) ⊗[(D : Type u)] M := fun y L ↦
    taylorMonomial B xi L ⊗ₜ[(D : Type u)] thetaPow L y with hG
  have hvan : ∀ (y : M) (L : ι →₀ ℕ), L ∉ (hfin y).toFinset →
      thetaPow L y ∈ pPowSmul p (D : Type u) M N := fun y _ hL ↦
    not_not.mp fun hc ↦ hL ((hfin y).mem_toFinset.mpr hc)
  have hterm : ∀ (y : M) (L : ι →₀ ℕ),
      thetaPow L y ∈ pPowSmul p (D : Type u) M N → G y L = 0 := fun y _ hL ↦
    taylorTerm_eq_zero_of_mem_pPowSmul p D B M thetaPow hpB xi hL
  have hsupp : ∀ y : M, Function.support (G y) ⊆ ↑(hfin y).toFinset := by
    intro y L hL
    rw [Set.Finite.coe_toFinset]
    exact fun hc ↦ hL (hterm y L hc)
  have hfs : ∀ y : M, Function.HasFiniteSupport (G y) := fun y ↦
    Set.Finite.subset (hfin y).toFinset.finite_toSet (hsupp y)
  have hsub : ∀ (y : M) (sm : Finset (ι →₀ ℕ)), (hfin y).toFinset ⊆ sm →
      (∑ᶠ L, G y L) = ∑ L ∈ sm, G y L := by
    intro y sm hsm
    exact finsum_eq_sum_of_support_subset _ ((hsupp y).trans (Finset.coe_subset.mpr hsm))
  refine exists_isTwistedTaylorComparison_of_sum xi (fun y ↦ ∑ᶠ L, G y L) (fun y ↦ ?_)
    (fun y y' ↦ ?_) (fun a y ↦ ?_)
  · rw [hsub y _ Finset.Subset.rfl]
    exact hasTaylorSum_of_eq_zero p D B M thetaPow xi y _ fun L hL ↦
      hterm y L (hvan y L hL)
  · have hpt : ∀ L : ι →₀ ℕ, G (y + y') L = G y L + G y' L := by
      intro L
      change taylorMonomial B xi L ⊗ₜ[(D : Type u)] thetaPow L (y + y') = _
      rw [hfamM.map_add hthAdd L y y', TensorProduct.tmul_add]
    rw [finsum_congr hpt, finsum_add_distrib (hfs y) (hfs y')]
  · obtain ⟨t, htaylor, htvan⟩ := htay a
    set sm : Finset (ι →₀ ℕ) := (hfin y).toFinset with hsm
    set sL : Finset (ι →₀ ℕ) :=
      ((t ×ˢ sm).image fun P : (ι →₀ ℕ) × (ι →₀ ℕ) ↦ P.1 + P.2) ∪ (hfin (a • y)).toFinset
      with hsLdef
    have hsL : ∀ J ∈ t, ∀ K ∈ sm, J + K ∈ sL := fun J hJ K hK ↦
      Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨(J, K), Finset.mem_product.mpr ⟨hJ, hK⟩, rfl⟩)
    rw [hsub (a • y) sL Finset.subset_union_right, hsub y sm Finset.Subset.rfl]
    exact taylorSum_smul_eq_of_taylorFormula p hfamM hfamD hthAdd hleib hxi hpB f a y sm t sL
      (fun K hK ↦ hvan y K hK) htaylor htvan hsL

/-- **Taylor's formula in `B` at the datum `f = g`** of `Crystalline.SecondDividedPowerMap.refl`,
where the coordinate differences `ξ_i` vanish: it holds with `t = {0}`. -/
theorem taylorFormula_refl (D : DividedPowerRing.{u}) {ι : Type uI}
    {delta : ι → (D.carrier → D.carrier)} {deltaPow : (ι →₀ ℕ) → (D.carrier → D.carrier)}
    (hfamD : IsThetaMonomialFamily D.carrier delta deltaPow) (a : D.carrier) :
    ∃ t : Finset (ι →₀ ℕ),
      ((SecondDividedPowerMap.refl D).ringHom a = ∑ J ∈ t,
          algebraMap D.carrier D.carrier (deltaPow J a) *
            taylorMonomial D (0 : ι → D.carrier) J) ∧
        ∀ J ∉ t, algebraMap D.carrier D.carrier (deltaPow J a) *
          taylorMonomial D (0 : ι → D.carrier) J = 0 := by
  classical
  refine ⟨{0}, ?_, fun J hJ ↦ ?_⟩
  · rw [Finset.sum_singleton, taylorMonomial_zero, mul_one, hfamD.apply_zero]
    rfl
  · rw [taylorMonomial_zero_family D (by simpa using hJ), mul_zero]

end Semilinear

end Crystalline

end
