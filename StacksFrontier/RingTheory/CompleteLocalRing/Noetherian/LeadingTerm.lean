module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Algebra.Order.Sub.Unbundled.Hom
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Leading-term data for a local ring with finitely generated maximal ideal

This file defines the single-step approximation property `SingleStep R J a d` of an ideal `J`,
spans `m ^ n` by monomials in generators `ω` of the maximal ideal `m`
(`pow_maximalIdeal_eq_span_monomials`), and develops the representative map `reprMap R ω` from
`MvPolynomial (Fin t) (ResidueField R)` to `R` and the leading-term predicate `leadingMem R ω J`.
-/

/-!
### A complete local ring with finitely generated maximal ideal is Noetherian

A module `M` is `I`-adically complete when the natural map `M → lim_n M / I^n M` is an
isomorphism; in Mathlib this is `IsAdicComplete I M`, the conjunction of `IsHausdorff I M` and
`IsPrecomplete I M`. A complete local ring is a local ring `R` with
`IsAdicComplete (IsLocalRing.maximalIdeal R) R`.
-/

@[expose] public section

open IsLocalRing

/-- The single-step approximation property for an ideal `J` with respect to a finite family
`a : Fin r → R` and degrees `d : Fin r → ℕ`: each `a i` lies in `J` and in `m ^ (d i)`, and for
every `n` and every `x ∈ J ∩ m^n` there are coefficients `c i ∈ m^(n - d i)` with
`x - Σ_i c i * a i ∈ m^(n+1)`. -/
def SingleStep (R : Type*) [CommRing R] [IsLocalRing R]
    (J : Ideal R) {r : ℕ} (a : Fin r → R) (d : Fin r → ℕ) : Prop :=
  (∀ i, a i ∈ J) ∧
  (∀ i, a i ∈ (IsLocalRing.maximalIdeal R ^ (d i) : Ideal R)) ∧
  (∀ n : ℕ, ∀ x ∈ (IsLocalRing.maximalIdeal R ^ n : Ideal R), x ∈ J →
    ∃ c : Fin r → R,
      (∀ i, c i ∈ (IsLocalRing.maximalIdeal R ^ (n - d i) : Ideal R)) ∧
      x - ∑ i, c i * a i ∈ (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R))

/-!
### Leading-term data

Throughout, `m = maximalIdeal R`, `ω : Fin t → R` are generators of `m`
(`m = span (range ω)`), and `S = MvPolynomial (Fin t) (ResidueField R)`.
-/

/-- For a finitely generated maximal ideal `m = span (range ω)`, the power `m ^ n` is spanned
over `R` by the degree-`n` monomials `∏ j, ω j ^ (e j)` with `∑ j, e j = n`. -/
theorem pow_maximalIdeal_eq_span_monomials
    (R : Type*) [CommRing R] [IsLocalRing R]
    {t : ℕ} (ω : Fin t → R) (hω : IsLocalRing.maximalIdeal R = Ideal.span (Set.range ω))
    (n : ℕ) :
    (IsLocalRing.maximalIdeal R ^ n : Ideal R)
      = Ideal.span (Set.range (fun e : {e : Fin t → ℕ // ∑ j, e j = n} => ∏ j, ω j ^ (e.1 j))) := by
  classical
  rw [hω]
  have hsplit : ∀ (e : Fin t → ℕ) (k : Fin t),
      e k + ∑ x ∈ Finset.univ \ {k}, e x = ∑ j, e j := by
    intro e k
    rw [← Finset.sum_erase_add Finset.univ e (Finset.mem_univ k), add_comm]
    congr 1
    rw [Finset.erase_eq]
  have hmono : ∀ (k : Fin t) (e : Fin t → ℕ),
      ∏ j, ω j ^ (Function.update e k (e k + 1) j) = ω k * ∏ j, ω j ^ (e j) := by
    intro k e
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    rw [← Finset.mul_prod_erase Finset.univ (fun j => ω j ^ e j) (Finset.mem_univ k)]
    rw [Function.update_self, pow_succ]
    rw [Finset.prod_congr rfl
      (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])]
    ring
  induction n with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    symm
    rw [Ideal.eq_top_iff_one]
    apply Ideal.subset_span
    exact ⟨⟨fun _ => 0, by simp⟩, by simp⟩
  | succ n ih =>
    rw [pow_succ', ih, Ideal.span_mul_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro z ⟨x, ⟨k, rfl⟩, y, ⟨e, rfl⟩, rfl⟩
      apply Ideal.subset_span
      refine ⟨⟨Function.update e.val k (e.val k + 1), ?_⟩, ?_⟩
      · rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
        have h1 := hsplit e.val k
        have h2 := e.property
        omega
      · show ∏ j, ω j ^ (Function.update e.val k (e.val k + 1) j) = ω k * ∏ j, ω j ^ (e.val j)
        exact hmono k e.val
    · rw [Ideal.span_le]
      rintro z ⟨e, rfl⟩
      have hsum := e.property
      have hne : (Finset.univ.filter (fun k => 0 < e.val k)).Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        have hz : ∑ j, e.val j = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          by_contra hj
          have hmem : j ∈ Finset.univ.filter (fun k => 0 < e.val k) := by
            simp [Nat.pos_of_ne_zero hj]
          rw [h] at hmem
          exact absurd hmem (Finset.notMem_empty j)
        omega
      obtain ⟨k, hk⟩ := hne
      simp only [Finset.mem_filter] at hk
      apply Ideal.subset_span
      refine ⟨ω k, ⟨k, rfl⟩, ∏ j, ω j ^ (Function.update e.val k (e.val k - 1) j),
        ⟨⟨Function.update e.val k (e.val k - 1), ?_⟩, rfl⟩, ?_⟩
      · rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
        have h1 := hsplit e.val k
        omega
      · have key := hmono k (Function.update e.val k (e.val k - 1))
        rw [Function.update_self] at key
        have heq :
            Function.update (Function.update e.val k (e.val k - 1)) k (e.val k - 1 + 1)
              = e.val := by
          funext j
          by_cases hj : j = k
          · subst hj; rw [Function.update_self]; omega
          · simp [Function.update_of_ne hj]
        rw [heq] at key
        exact key.symm

/-!
### The representative map and the leading-term ideal

`reprMap R ω f` lifts each coefficient of `f ∈ S` to `R` through `residueSection` and
substitutes `ω` for the variables. `leadingMem R ω J f` holds when every homogeneous component
`f_n` of `f` has `reprMap R ω f_n ∈ (m^n ⊓ J) ⊔ m^(n+1)`.
-/

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A set-theoretic section of the residue map `R → ResidueField R`, given by
`Quotient.out`. -/
noncomputable def residueSection (R : Type*) [CommRing R] [IsLocalRing R] :
    IsLocalRing.ResidueField R → R := Quotient.out

/-- The representative in `R` of `f ∈ MvPolynomial (Fin t) (ResidueField R)`:
`reprMap R ω f = Σ_{α ∈ supp f} residueSection R (coeff α f) * ∏_j ω j ^ (α j)`. -/
noncomputable def reprMap (R : Type*) [CommRing R] [IsLocalRing R] {t : ℕ} (ω : Fin t → R)
    (f : MvPolynomial (Fin t) (IsLocalRing.ResidueField R)) : R :=
  ∑ α ∈ f.support, residueSection R (f.coeff α) * ∏ j, ω j ^ (α j)

/-- A polynomial `f` lies in the leading-term ideal of `J` when every homogeneous component
`f_n` has its representative `reprMap R ω f_n` in `(m^n ⊓ J) ⊔ m^(n+1)`. -/
noncomputable def leadingMem (R : Type*) [CommRing R] [IsLocalRing R] {t : ℕ} (ω : Fin t → R)
    (J : Ideal R) (f : MvPolynomial (Fin t) (IsLocalRing.ResidueField R)) : Prop :=
  ∀ n : ℕ, reprMap R ω (MvPolynomial.homogeneousComponent n f)
      ∈ (IsLocalRing.maximalIdeal R ^ n ⊓ J) ⊔ (IsLocalRing.maximalIdeal R ^ (n + 1))

/-- `ω^α ∈ m^(∑ α)`: a degree-`|α|` monomial in the generators lies in `m^{|α|}`. -/
theorem prod_pow_mem_maximalIdeal_pow (R : Type*) [CommRing R] [IsLocalRing R] {t : ℕ}
    (ω : Fin t → R)
    (hω : IsLocalRing.maximalIdeal R = Ideal.span (Set.range ω)) (α : Fin t →₀ ℕ) :
    (∏ j, ω j ^ (α j)) ∈ IsLocalRing.maximalIdeal R ^ (∑ j, α j) := by
  have hmem : ∀ j, ω j ∈ IsLocalRing.maximalIdeal R := fun j => by
    rw [hω]; exact Ideal.subset_span ⟨j, rfl⟩
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod (fun j _ => Ideal.pow_mem_pow (hmem j) _)

/-- `x - y ∈ m ↔ residue x = residue y`. -/
theorem sub_mem_maximalIdeal_iff_residue_eq (R : Type*) [CommRing R] [IsLocalRing R] (x y : R) :
    x - y ∈ IsLocalRing.maximalIdeal R ↔ IsLocalRing.residue R x = IsLocalRing.residue R y := by
  rw [IsLocalRing.residue_def, IsLocalRing.residue_def]; exact (Ideal.Quotient.eq).symm

/-- `residueSection` is a genuine section of the residue map. -/
@[simp]
theorem residue_residueSection (R : Type*) [CommRing R] [IsLocalRing R]
    (c : IsLocalRing.ResidueField R) :
    IsLocalRing.residue R (residueSection R c) = c := by
  rw [IsLocalRing.residue_def]; exact Quotient.out_eq c

/-- `residueSection 0 ∈ m`. -/
theorem residueSection_zero_mem_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R] :
    residueSection R 0 ∈ IsLocalRing.maximalIdeal R := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]; exact Quotient.out_eq (0 : IsLocalRing.ResidueField R)

/-- Additivity defect of `residueSection` lands in `m`. -/
theorem residueSection_add_sub_sub_mem_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R]
    (a b : IsLocalRing.ResidueField R) :
    residueSection R (a + b) - residueSection R a - residueSection R b ∈
      IsLocalRing.maximalIdeal R := by
  have h : residueSection R (a + b) - (residueSection R a + residueSection R b) ∈
      IsLocalRing.maximalIdeal R := by
    rw [sub_mem_maximalIdeal_iff_residue_eq, map_add, residue_residueSection,
      residue_residueSection, residue_residueSection]
  have heq : residueSection R (a + b) - residueSection R a - residueSection R b
       = residueSection R (a + b) - (residueSection R a + residueSection R b) := by ring
  rw [heq]; exact h

/-- Multiplicativity defect of `residueSection` lands in `m`. -/
theorem residueSection_mul_sub_mul_mem_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R]
    (a b : IsLocalRing.ResidueField R) :
    residueSection R (a * b) - residueSection R a * residueSection R b ∈
      IsLocalRing.maximalIdeal R := by
  rw [sub_mem_maximalIdeal_iff_residue_eq, map_mul, residue_residueSection,
    residue_residueSection, residue_residueSection]

/-- A homogeneous degree-`n` polynomial has all support exponents of total degree `n`. -/
theorem sum_eq_of_isHomogeneous_of_mem_support (R : Type*) [CommRing R] [IsLocalRing R] {t n : ℕ}
    {f : MvPolynomial (Fin t) (IsLocalRing.ResidueField R)}
    (hf : f.IsHomogeneous n) {α : Fin t →₀ ℕ} (hα : α ∈ f.support) : ∑ j, α j = n := by
  have h := hf (MvPolynomial.mem_support_iff.mp hα)
  rw [Finsupp.weight_apply] at h
  simp only [Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [← h, Finset.sum_subset (Finset.subset_univ α.support)]
  intro x _ hx; simpa using hx

/-- A sum of terms `c i * ω^(γ i)` with `c i ∈ m` and `|γ i| = n` lies in `m ^ (n + 1)`. -/
private theorem sum_mul_prod_pow_mem_pow_succ (R : Type*) [CommRing R] [IsLocalRing R] {t n : ℕ}
    (ω : Fin t → R) (hω : IsLocalRing.maximalIdeal R = Ideal.span (Set.range ω)) {ι : Type*}
    (s : Finset ι) (γ : ι → Fin t →₀ ℕ) (c : ι → R)
    (hc : ∀ i ∈ s, c i ∈ IsLocalRing.maximalIdeal R) (hdeg : ∀ i ∈ s, ∑ j, γ i j = n) :
    ∑ i ∈ s, c i * ∏ j, ω j ^ (γ i j) ∈ IsLocalRing.maximalIdeal R ^ (n + 1) := by
  refine Ideal.sum_mem _ fun i hi => ?_
  rw [pow_succ']
  exact Ideal.mul_mem_mul (hc i hi)
    (by rw [← hdeg i hi]; exact prod_pow_mem_maximalIdeal_pow R ω hω (γ i))

/-- `reprMap` over its own support agrees, mod `m^{n+1}`, with the sum over any
finset of degree-`n` exponents containing the support. -/
theorem reprMap_eq_sum_on (R : Type*) [CommRing R] [IsLocalRing R] {t n : ℕ} (ω : Fin t → R)
    (hω : IsLocalRing.maximalIdeal R = Ideal.span (Set.range ω))
    (f : MvPolynomial (Fin t) (IsLocalRing.ResidueField R)) (s : Finset (Fin t →₀ ℕ))
    (hsub : f.support ⊆ s) (hdeg : ∀ α ∈ s, ∑ j, α j = n) :
    reprMap R ω f - ∑ α ∈ s, residueSection R (f.coeff α) * ∏ j, ω j ^ (α j)
      ∈ IsLocalRing.maximalIdeal R ^ (n+1) := by
  classical
  rw [reprMap, ← Finset.sum_sdiff hsub]
  have hrw : (∑ α ∈ f.support, residueSection R (f.coeff α) * ∏ j, ω j ^ (α j))
      - ((∑ x ∈ s \ f.support, residueSection R (f.coeff x) * ∏ j, ω j ^ x j)
         + ∑ x ∈ f.support, residueSection R (f.coeff x) * ∏ j, ω j ^ x j)
      = - ∑ x ∈ s \ f.support, residueSection R (f.coeff x) * ∏ j, ω j ^ x j := by ring
  rw [hrw, ← Finset.sum_neg_distrib]
  simp only [← neg_mul]
  refine sum_mul_prod_pow_mem_pow_succ R ω hω _ (fun α => α)
    (fun α => -residueSection R (f.coeff α)) (fun α hα => ?_)
    fun α hα => hdeg α (Finset.mem_sdiff.mp hα).1
  rw [MvPolynomial.notMem_support_iff.mp (Finset.mem_sdiff.mp hα).2]
  exact neg_mem (residueSection_zero_mem_maximalIdeal R)

/-- For homogeneous degree-`n` polynomials,
`reprMap (p+q) - reprMap p - reprMap q ∈ m^{n+1}`. -/
theorem reprMap_add_defect (R : Type*) [CommRing R] [IsLocalRing R] {t n : ℕ} (ω : Fin t → R)
    (hω : IsLocalRing.maximalIdeal R = Ideal.span (Set.range ω))
    (p q : MvPolynomial (Fin t) (IsLocalRing.ResidueField R))
    (hp : p.IsHomogeneous n) (hq : q.IsHomogeneous n) :
    reprMap R ω (p + q) - reprMap R ω p - reprMap R ω q ∈ IsLocalRing.maximalIdeal R ^ (n+1) := by
  classical
  set s : Finset (Fin t →₀ ℕ) := (p + q).support ∪ p.support ∪ q.support with hs
  have hpq : (p + q).IsHomogeneous n := hp.add hq
  have hdeg : ∀ α ∈ s, ∑ j, α j = n := by
    intro α hα
    rw [hs, Finset.mem_union, Finset.mem_union] at hα
    rcases hα with (h | h) | h
    · exact sum_eq_of_isHomogeneous_of_mem_support R hpq h
    · exact sum_eq_of_isHomogeneous_of_mem_support R hp h
    · exact sum_eq_of_isHomogeneous_of_mem_support R hq h
  have e1 := reprMap_eq_sum_on R ω hω (p+q) s
    (by rw [hs]; exact Finset.subset_union_left.trans Finset.subset_union_left) hdeg
  have e2 := reprMap_eq_sum_on R ω hω p s
    (by rw [hs]; exact Finset.subset_union_right.trans Finset.subset_union_left) hdeg
  have e3 := reprMap_eq_sum_on R ω hω q s (by rw [hs]; exact Finset.subset_union_right) hdeg
  have hdefect := sum_mul_prod_pow_mem_pow_succ R ω hω s (fun α => α)
    (fun α => residueSection R ((p + q).coeff α)
      - residueSection R (p.coeff α) - residueSection R (q.coeff α))
    (fun α _ => by
      simpa only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using residueSection_add_sub_sub_mem_maximalIdeal R _ _)
    hdeg
  simp only [sub_mul, Finset.sum_sub_distrib] at hdefect
  convert Ideal.add_mem _ (Ideal.sub_mem _ (Ideal.sub_mem _ e1 e2) e3) hdefect using 1
  ring

/-- For a finite family of homogeneous degree-`n` polynomials,
`reprMap (∑ P b) - ∑ reprMap (P b) ∈ m^{n+1}`. -/
theorem reprMap_sum_defect (R : Type*) [CommRing R] [IsLocalRing R] {t n : ℕ} (ω : Fin t → R)
    (hω : IsLocalRing.maximalIdeal R = Ideal.span (Set.range ω)) {ι : Type*} (T : Finset ι)
    (P : ι → MvPolynomial (Fin t) (IsLocalRing.ResidueField R))
    (hP : ∀ b ∈ T, (P b).IsHomogeneous n) :
    reprMap R ω (∑ b ∈ T, P b) - ∑ b ∈ T, reprMap R ω (P b)
      ∈ IsLocalRing.maximalIdeal R ^ (n + 1) := by
  classical
  induction T using Finset.induction with
  | empty => simp [reprMap]
  | insert b T hbT ih =>
    rw [Finset.sum_insert hbT, Finset.sum_insert hbT]
    have hT : ∀ c ∈ T, (P c).IsHomogeneous n := fun c hc => hP c (Finset.mem_insert_of_mem hc)
    convert Ideal.add_mem _ (reprMap_add_defect R ω hω _ _ (hP b (Finset.mem_insert_self b T))
      (MvPolynomial.IsHomogeneous.sum _ _ _ hT)) (ih hT) using 1
    ring

/-- For `f` homogeneous of degree `d` and `∑ β = e`,
`reprMap (X^β·b · f) ≡ (lift b)·ω^β·reprMap f (mod m^{e+d+1})`. -/
theorem reprMap_monomial_mul (R : Type*) [CommRing R] [IsLocalRing R] {t d e : ℕ} (ω : Fin t → R)
    (hω : IsLocalRing.maximalIdeal R = Ideal.span (Set.range ω))
    (β : Fin t →₀ ℕ) (hβ : ∑ j, β j = e) (b : IsLocalRing.ResidueField R)
    (f : MvPolynomial (Fin t) (IsLocalRing.ResidueField R)) (hf : f.IsHomogeneous d) :
    reprMap R ω (MvPolynomial.monomial β b * f)
      - residueSection R b * (∏ j, ω j ^ (β j)) * reprMap R ω f
      ∈ IsLocalRing.maximalIdeal R ^ (e + d + 1) := by
  classical
  set s : Finset (Fin t →₀ ℕ) := Finset.image (fun α => β + α) f.support with hs
  have hdeg : ∀ γ ∈ s, ∑ j, γ j = e + d := by
    intro γ hγ
    rw [hs, Finset.mem_image] at hγ
    obtain ⟨α, hα, rfl⟩ := hγ
    rw [show (∑ j, (β + α) j) = (∑ j, β j) + (∑ j, α j) from by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [Finsupp.add_apply])]
    rw [hβ, sum_eq_of_isHomogeneous_of_mem_support R hf hα]
  have hsub : (MvPolynomial.monomial β b * f).support ⊆ s := by
    intro γ hγ
    rw [MvPolynomial.mem_support_iff] at hγ
    rw [hs, Finset.mem_image]
    by_cases hble : β ≤ γ
    · refine ⟨γ - β, ?_, by rw [add_tsub_cancel_of_le hble]⟩
      rw [MvPolynomial.mem_support_iff]; intro h; apply hγ
      rw [MvPolynomial.coeff_monomial_mul']; simp [hble, h]
    · exfalso; apply hγ; rw [MvPolynomial.coeff_monomial_mul']; simp [hble]
  have e1 := reprMap_eq_sum_on R ω hω (MvPolynomial.monomial β b * f) s hsub hdeg
  have hinj : Set.InjOn (fun α => β + α) f.support := fun a _ b _ h => by simpa using h
  have hsum : (∑ γ ∈ s, residueSection R ((MvPolynomial.monomial β b * f).coeff γ)
        * ∏ j, ω j ^ (γ j))
      = ∑ α ∈ f.support, residueSection R (b * f.coeff α)
          * ∏ j, ω j ^ ((β + α) j) := by
    rw [hs, Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun α _ => by rw [MvPolynomial.coeff_monomial_mul])
  rw [hsum] at e1
  have hexp : residueSection R b * (∏ j, ω j ^ (β j)) * reprMap R ω f
      = ∑ α ∈ f.support, (residueSection R b * residueSection R (f.coeff α))
          * ∏ j, ω j ^ ((β + α) j) := by
    rw [reprMap, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [show (∏ j, ω j ^ ((β + α) j)) = (∏ j, ω j ^ (β j)) * (∏ j, ω j ^ (α j)) from by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun j _ => by rw [Finsupp.add_apply, pow_add])]
    ring
  rw [hexp]
  have hdef := sum_mul_prod_pow_mem_pow_succ R ω hω f.support (fun α => β + α)
    (fun α => residueSection R (b * f.coeff α)
      - residueSection R b * residueSection R (f.coeff α))
    (fun α _ => residueSection_mul_sub_mul_mem_maximalIdeal R b _)
    (fun α hα => hdeg (β + α) (by rw [hs, Finset.mem_image]; exact ⟨α, hα, rfl⟩))
  simp only [sub_mul, Finset.sum_sub_distrib] at hdef
  convert Ideal.add_mem _ e1 hdef using 1
  ring

/-- Degree-`n` component of a monomial-times-polynomial (`e = ∑ β ≤ n`). -/
theorem homogeneousComponent_monomial_mul (R : Type*) [CommRing R] [IsLocalRing R] {t : ℕ}
    (β : Fin t →₀ ℕ) {e : ℕ}
    (hβ : ∑ j, β j = e) (b : IsLocalRing.ResidueField R)
    (f : MvPolynomial (Fin t) (IsLocalRing.ResidueField R)) (n : ℕ) (hle : e ≤ n) :
    MvPolynomial.homogeneousComponent n (MvPolynomial.monomial β b * f)
      = MvPolynomial.monomial β b * MvPolynomial.homogeneousComponent (n - e) f := by
  classical
  ext γ
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_monomial_mul',
    MvPolynomial.coeff_monomial_mul']
  by_cases hβγ : β ≤ γ
  · simp only [hβγ, ite_true]
    rw [MvPolynomial.coeff_homogeneousComponent]
    have hβdeg : β.degree = e := by rw [Finsupp.degree_eq_sum]; exact hβ
    have hle2 : e ≤ γ.degree := by
      rw [← hβdeg, Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
      exact Finset.sum_le_sum (fun j _ => hβγ j)
    have hdegsub : (γ - β).degree = γ.degree - e := by
      have h := map_tsub_of_le Finsupp.degree γ β hβγ
      rw [← h, hβdeg]
    by_cases hd : γ.degree = n
    · simp only [hd, ite_true]; rw [hdegsub, hd, ite_eq_left (by omega)]
    · simp only [hd, ite_false]; rw [hdegsub, ite_eq_right (by intro h; apply hd; omega), mul_zero]
  · simp [hβγ]

/-- `J`-absorption: `c·w·x ∈ (m^{e+k}∩J)⊔m^{e+k+1}` when `w∈m^e`, `x∈(m^k∩J)⊔m^{k+1}`. -/
theorem mul_mul_mem_inf_sup_pow_add (R : Type*) [CommRing R] [IsLocalRing R] (J : Ideal R)
    (e k : ℕ) (c w x : R)
    (hw : w ∈ IsLocalRing.maximalIdeal R ^ e)
    (hx : x ∈ (IsLocalRing.maximalIdeal R ^ k ⊓ J) ⊔ (IsLocalRing.maximalIdeal R ^ (k + 1))) :
    c * w * x ∈ (IsLocalRing.maximalIdeal R ^ (e + k) ⊓ J)
      ⊔ (IsLocalRing.maximalIdeal R ^ (e + k + 1)) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [mul_add]
  refine Submodule.add_mem _
    (Submodule.mem_sup_left ⟨?_, Ideal.mul_mem_left _ _ hy.2⟩) (Submodule.mem_sup_right ?_)
  · rw [pow_add, show c * w * y = w * (c * y) by ring]
    exact Ideal.mul_mem_mul hw (Ideal.mul_mem_left _ c hy.1)
  · rw [show e + k + 1 = e + (k + 1) by ring, pow_add, show c * w * z = w * (c * z) by ring]
    exact Ideal.mul_mem_mul hw (Ideal.mul_mem_left _ c hz)

/-- `leadingMem` holds for `0`. -/
theorem leadingMem_zero (R : Type*) [CommRing R] [IsLocalRing R] {t : ℕ} (ω : Fin t → R)
    (J : Ideal R) : leadingMem R ω J 0 := by
  intro n
  rw [map_zero, reprMap]
  simp only [MvPolynomial.support_zero, Finset.sum_empty]
  exact Submodule.mem_sup_right (Submodule.zero_mem _)

/-- `leadingMem` is closed under addition. -/
theorem leadingMem_add (R : Type*) [CommRing R] [IsLocalRing R] {t : ℕ} (ω : Fin t → R)
    (hω : IsLocalRing.maximalIdeal R = Ideal.span (Set.range ω)) (J : Ideal R)
    (f g : MvPolynomial (Fin t) (IsLocalRing.ResidueField R))
    (hf : leadingMem R ω J f) (hg : leadingMem R ω J g) :
    leadingMem R ω J (f + g) := by
  intro n
  rw [map_add]
  set p := MvPolynomial.homogeneousComponent n f
  set q := MvPolynomial.homogeneousComponent n g
  have hp : p.IsHomogeneous n := MvPolynomial.homogeneousComponent_isHomogeneous n f
  have hq : q.IsHomogeneous n := MvPolynomial.homogeneousComponent_isHomogeneous n g
  have hdef := reprMap_add_defect R ω hω p q hp hq
  convert Submodule.add_mem _ (Submodule.add_mem _ (hf n) (hg n))
    (Submodule.mem_sup_right hdef) using 1
  ring

/-- `leadingMem` is closed under multiplication by a monomial. -/
theorem leadingMem_monomial_mul (R : Type*) [CommRing R] [IsLocalRing R] {t : ℕ} (ω : Fin t → R)
    (hω : IsLocalRing.maximalIdeal R = Ideal.span (Set.range ω)) (J : Ideal R)
    (β : Fin t →₀ ℕ) (b : IsLocalRing.ResidueField R)
    (f : MvPolynomial (Fin t) (IsLocalRing.ResidueField R)) (hf : leadingMem R ω J f) :
    leadingMem R ω J (MvPolynomial.monomial β b * f) := by
  classical
  intro n
  set e := ∑ j, β j with he
  by_cases hle : e ≤ n
  · rw [homogeneousComponent_monomial_mul R β rfl b f n hle]
    have hhom : (MvPolynomial.homogeneousComponent (n - e) f).IsHomogeneous (n - e) :=
      MvPolynomial.homogeneousComponent_isHomogeneous (n-e) f
    have hdefect := reprMap_monomial_mul R ω hω β rfl b
      (MvPolynomial.homogeneousComponent (n-e) f) hhom
    have hω_mem : (∏ j, ω j ^ (β j)) ∈ IsLocalRing.maximalIdeal R ^ e := by
      rw [he]; exact prod_pow_mem_maximalIdeal_pow R ω hω β
    have hmain : residueSection R b * (∏ j, ω j ^ (β j))
        * reprMap R ω (MvPolynomial.homogeneousComponent (n-e) f)
        ∈ (IsLocalRing.maximalIdeal R ^ (e + (n-e)) ⊓ J)
          ⊔ (IsLocalRing.maximalIdeal R ^ (e + (n-e) + 1)) :=
      mul_mul_mem_inf_sup_pow_add R J e (n-e) (residueSection R b) _ _ hω_mem (hf (n-e))
    rw [show e + (n - e) = n from by omega] at hmain
    rw [show e + (n - e) + 1 = n + 1 from by omega] at hdefect
    convert Submodule.add_mem _ hmain (Submodule.mem_sup_right hdefect) using 1
    ring
  · have hzero : MvPolynomial.homogeneousComponent n (MvPolynomial.monomial β b * f) = 0 := by
      ext γ
      rw [MvPolynomial.coeff_homogeneousComponent, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      split_ifs with hdeg
      · rw [MvPolynomial.coeff_monomial_mul']
        split_ifs with hβγ
        · exfalso
          have hsum : (∑ j, β j) ≤ ∑ j, γ j := Finset.sum_le_sum (fun j _ => hβγ j)
          rw [Finsupp.degree_eq_sum] at hdeg
          omega
        · rfl
      · rfl
    simpa [hzero] using leadingMem_zero R ω J n
