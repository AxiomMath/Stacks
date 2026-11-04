module

public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.RingTheory.DividedPowers.Basic

/-!
# The multi-index formulas for divided power monomials

`DividedPowers.dpow_add` is the binomial formula without binomial coefficients in one variable:
`x^{[n]}` of a sum is `∑_{u + v = n} x^{[u]} y^{[v]}`.  This file proves the formula for a
**divided power monomial in several variables**,

`∏_i (x_i + y_i)^{[k_i]} = ∑_{K' + K'' = K} (∏_i x_i^{[k'_i]}) (∏_i y_i^{[k''_i]})`,

the sum being over the antidiagonal of the multi-index `K` in `ι →₀ ℕ`, together with the
**multi-index product formula**

`(∏_i x_i^{[j_i]}) (∏_i x_i^{[k_i]}) = (∏_i binom(j_i + k_i, j_i)) ∏_i x_i^{[j_i + k_i]}`,

which is `DividedPowers.mul_dpow` taken over a product of indices.

## Main results

* `Finsupp.sum_antidiagonal_eq_sum_antidiagonal_erase`: the antidiagonal of a multi-index splits,
  at any one index, into the antidiagonal of that entry times the antidiagonal of the multi-index
  with that entry erased.
* `DividedPowers.prod_dpow_add`: the multi-index binomial formula, for a product over a finite set
  of indices containing the support of the multi-index.
* `DividedPowers.prod_dpow_add_support`: the same with every product taken over the support of the
  multi-index.
* `DividedPowers.prod_dpow_mul` and `DividedPowers.prod_dpow_mul_support`: the multi-index product
  formula, in the same two forms.

## References

* [P. Berthelot (1974), *Cohomologie cristalline des schémas de caractéristique $p$ > 0*]
  [Berthelot-1974], 1.1
-/

@[expose] public section

namespace Finsupp

variable {ι : Type*} [DecidableEq ι]

/-- If two multi-indices add up to `K.erase a`, both vanish at `a`. -/
private theorem apply_eq_zero_of_add_eq_erase {κ : Type*} {a : κ} {K L₁ L₂ : κ →₀ ℕ}
    (h : L₁ + L₂ = K.erase a) : L₁ a = 0 ∧ L₂ a = 0 := by
  classical
  have h := congrArg (fun f : κ →₀ ℕ ↦ f a) h
  simp only [add_apply, erase_same] at h
  omega

/-- The antidiagonal of a multi-index splits at any one index: summing a function over the pairs
`(K', K'')` with `K' + K'' = K` is the same as summing, over the pairs `(u, v)` with `u + v = K a`
and the pairs `(L', L'')` with `L' + L'' = K.erase a`, the function at
`(single a u + L', single a v + L'')`. -/
theorem sum_antidiagonal_eq_sum_antidiagonal_erase {N : Type*} [AddCommMonoid N] (a : ι)
    (K : ι →₀ ℕ) (F : (ι →₀ ℕ) → (ι →₀ ℕ) → N) :
    ∑ L ∈ Finset.antidiagonal K, F L.1 L.2 =
      ∑ uv ∈ Finset.antidiagonal (K a), ∑ L ∈ Finset.antidiagonal (K.erase a),
        F (single a uv.1 + L.1) (single a uv.2 + L.2) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij'
    (fun L ↦ ((L.1 a, L.2 a), (erase a L.1, erase a L.2)))
    (fun q ↦ (single a q.1.1 + q.2.1, single a q.1.2 + q.2.2)) ?_ ?_ ?_ ?_ ?_
  · intro L hL
    rw [Finset.mem_antidiagonal] at hL
    refine Finset.mem_product.mpr ⟨Finset.mem_antidiagonal.mpr ?_,
      Finset.mem_antidiagonal.mpr ?_⟩
    · rw [← add_apply, hL]
    · rw [← erase_add, hL]
  · intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
    rw [Finset.mem_antidiagonal] at hq1 hq2
    refine Finset.mem_antidiagonal.mpr ?_
    calc single a q.1.1 + q.2.1 + (single a q.1.2 + q.2.2)
        = single a (q.1.1 + q.1.2) + (q.2.1 + q.2.2) := by rw [single_add]; abel
      _ = K := by rw [hq1, hq2, single_add_erase]
  · intro L _
    exact Prod.ext (single_add_erase a L.1) (single_add_erase a L.2)
  · intro q hq
    obtain ⟨-, hq2⟩ := Finset.mem_product.mp hq
    rw [Finset.mem_antidiagonal] at hq2
    have hz := apply_eq_zero_of_add_eq_erase hq2
    have hval : ∀ (u : ℕ) (L : ι →₀ ℕ), L a = 0 → (single a u + L) a = u := by
      intro u L hL; simp [hL]
    have herase : ∀ (u : ℕ) (L : ι →₀ ℕ), L a = 0 → erase a (single a u + L) = L := by
      intro u L hL
      rw [erase_add, erase_single, zero_add, erase_of_notMem_support (by simp [hL])]
    show (((single a q.1.1 + q.2.1) a, (single a q.1.2 + q.2.2) a),
      (erase a (single a q.1.1 + q.2.1), erase a (single a q.1.2 + q.2.2))) = q
    rw [hval q.1.1 q.2.1 hz.1, hval q.1.2 q.2.2 hz.2, herase q.1.1 q.2.1 hz.1,
      herase q.1.2 q.2.2 hz.2]
  · intro L _
    show F L.1 L.2 = F (single a (L.1 a) + erase a L.1) (single a (L.2 a) + erase a L.2)
    rw [single_add_erase, single_add_erase]

end Finsupp

namespace DividedPowers

variable {A : Type*} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I)

/-- A product of divided powers over the support of `L` extends to any finite set containing it. -/
private theorem prod_dpow_support_eq_prod {ι : Type*} {x : ι → A} (hx : ∀ i, x i ∈ I)
    {s : Finset ι} (L : ι →₀ ℕ) (hL : L.support ⊆ s) :
    (∏ i ∈ L.support, hI.dpow (L i) (x i)) = ∏ i ∈ s, hI.dpow (L i) (x i) := by
  refine Finset.prod_subset hL fun i _ hi ↦ ?_
  rw [Finsupp.notMem_support_iff.mp hi, hI.dpow_zero (hx i)]

/-- The multi-index binomial formula for divided powers:

`∏_i (x_i + y_i)^{[k_i]} = ∑_{K' + K'' = K} (∏_i x_i^{[k'_i]}) (∏_i y_i^{[k''_i]})`,

the sum running over the antidiagonal of the multi-index `K` in `ι →₀ ℕ`, and the products over a
finite set `s` of indices containing the support of `K`, for `x_i, y_i ∈ I`. -/
theorem prod_dpow_add {ι : Type*} [DecidableEq ι] {x y : ι → A} (s : Finset ι)
    (hx : ∀ i ∈ s, x i ∈ I) (hy : ∀ i ∈ s, y i ∈ I) (K : ι →₀ ℕ) (hK : K.support ⊆ s) :
    (∏ i ∈ s, hI.dpow (K i) (x i + y i)) =
      ∑ L ∈ Finset.antidiagonal K,
        (∏ i ∈ s, hI.dpow (L.1 i) (x i)) * (∏ i ∈ s, hI.dpow (L.2 i) (y i)) := by
  classical
  induction s using Finset.induction generalizing K with
  | empty =>
      obtain rfl : K = 0 := Finsupp.support_eq_empty.mp (Finset.subset_empty.mp hK)
      simp
  | @insert a s ha ih =>
      have hxs : ∀ i ∈ s, x i ∈ I := fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)
      have hys : ∀ i ∈ s, y i ∈ I := fun i hi ↦ hy i (Finset.mem_insert_of_mem hi)
      have hne : ∀ i ∈ s, i ≠ a := fun i hi ↦ ne_of_mem_of_not_mem hi ha
      have hK' : (K.erase a).support ⊆ s := by
        intro i hi
        rw [Finsupp.support_erase, Finset.mem_erase] at hi
        exact (Finset.mem_insert.mp (hK hi.2)).resolve_left hi.1
      have hres : ∀ i ∈ s, (K.erase a) i = K i := fun i hi ↦ Finsupp.erase_ne (hne i hi)
      rw [Finset.prod_insert ha,
        hI.dpow_add (hx a (Finset.mem_insert_self a s)) (hy a (Finset.mem_insert_self a s)),
        Finset.prod_congr rfl (fun i hi ↦ by rw [← hres i hi]), ih hxs hys _ hK',
        Finset.sum_mul_sum]
      refine Eq.trans ?_ (Finsupp.sum_antidiagonal_eq_sum_antidiagonal_erase a K
        (fun u v ↦ (∏ i ∈ insert a s, hI.dpow (u i) (x i)) *
          ∏ i ∈ insert a s, hI.dpow (v i) (y i))).symm
      refine Finset.sum_congr rfl fun uv huv ↦ Finset.sum_congr rfl fun L hL ↦ ?_
      rw [Finset.mem_antidiagonal] at hL
      have hz := Finsupp.apply_eq_zero_of_add_eq_erase hL
      have key : ∀ (u : ℕ) (L' : ι →₀ ℕ) (z : ι → A), L' a = 0 → (∀ i ∈ s, z i ∈ I) →
          (∏ i ∈ insert a s, hI.dpow ((Finsupp.single a u + L') i) (z i)) =
            hI.dpow u (z a) * ∏ i ∈ s, hI.dpow (L' i) (z i) := by
        intro u L' z hL' _
        rw [Finset.prod_insert ha]
        congr 1
        · simp [hL']
        · refine Finset.prod_congr rfl fun i hi ↦ ?_
          rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (hne i hi), zero_add]
      rw [key uv.1 L.1 x hz.1 hxs, key uv.2 L.2 y hz.2 hys]
      ring

/-- The multi-index binomial formula for divided powers, with every product over the support of
the multi-index it belongs to: for `x_i, y_i ∈ I`,
`∏_{i ∈ K.support} (x_i + y_i)^{[k_i]}` is the sum over `K' + K'' = K` of
`(∏_{i ∈ K'.support} x_i^{[k'_i]}) (∏_{i ∈ K''.support} y_i^{[k''_i]})`. -/
theorem prod_dpow_add_support {ι : Type*} [DecidableEq ι] {x y : ι → A} (hx : ∀ i, x i ∈ I)
    (hy : ∀ i, y i ∈ I) (K : ι →₀ ℕ) :
    (∏ i ∈ K.support, hI.dpow (K i) (x i + y i)) =
      ∑ L ∈ Finset.antidiagonal K,
        (∏ i ∈ L.1.support, hI.dpow (L.1 i) (x i)) *
          (∏ i ∈ L.2.support, hI.dpow (L.2 i) (y i)) := by
  classical
  rw [hI.prod_dpow_add K.support (fun i _ ↦ hx i) (fun i _ ↦ hy i) K Finset.Subset.rfl]
  refine Finset.sum_congr rfl fun L hL ↦ ?_
  rw [Finset.mem_antidiagonal] at hL
  have h1 : L.1.support ⊆ K.support := by
    rw [← hL]; exact Finsupp.support_mono le_self_add
  have h2 : L.2.support ⊆ K.support := by
    rw [← hL]; exact Finsupp.support_mono le_add_self
  rw [hI.prod_dpow_support_eq_prod hx L.1 h1, hI.prod_dpow_support_eq_prod hy L.2 h2]

/-- The multi-index product formula for divided powers:

`(∏_i x_i^{[j_i]}) (∏_i x_i^{[k_i]}) = (∏_i binom(j_i + k_i, j_i)) ∏_i x_i^{[j_i + k_i]}`,

the products being over a finite set `s` of indices with `x_i ∈ I`. -/
theorem prod_dpow_mul {ι : Type*} {x : ι → A} (s : Finset ι) (hx : ∀ i ∈ s, x i ∈ I)
    (J K : ι →₀ ℕ) :
    (∏ i ∈ s, hI.dpow (J i) (x i)) * (∏ i ∈ s, hI.dpow (K i) (x i)) =
      (∏ i ∈ s, ((J i + K i).choose (J i) : A)) * ∏ i ∈ s, hI.dpow (J i + K i) (x i) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i hi ↦ hI.mul_dpow (hx i hi)

/-- The multi-index product formula for divided powers, with every product over the support of the
multi-index it belongs to: for `x_i ∈ I`, `(∏_{i ∈ J.support} x_i^{[j_i]}) (∏_{i ∈ K.support}
x_i^{[k_i]})` is `∏_{i ∈ (J + K).support} binom(j_i + k_i, j_i) x_i^{[j_i + k_i]}`. -/
theorem prod_dpow_mul_support {ι : Type*} [DecidableEq ι] {x : ι → A} (hx : ∀ i, x i ∈ I)
    (J K : ι →₀ ℕ) :
    (∏ i ∈ J.support, hI.dpow (J i) (x i)) * (∏ i ∈ K.support, hI.dpow (K i) (x i)) =
      (∏ i ∈ (J + K).support, ((J i + K i).choose (J i) : A)) *
        ∏ i ∈ (J + K).support, hI.dpow ((J + K) i) (x i) := by
  classical
  rw [hI.prod_dpow_support_eq_prod hx J (Finsupp.support_mono le_self_add),
    hI.prod_dpow_support_eq_prod hx K (Finsupp.support_mono le_add_self),
    hI.prod_dpow_mul (J + K).support (fun i _ ↦ hx i) J K]
  exact congrArg _ (Finset.prod_congr rfl fun i _ ↦ by rw [Finsupp.add_apply])

end DividedPowers

end
