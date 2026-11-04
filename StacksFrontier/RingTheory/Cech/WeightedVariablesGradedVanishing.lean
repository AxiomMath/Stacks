module

public import StacksFrontier.RingTheory.Cech.GradedSubcomplex
public import StacksFrontier.RingTheory.Cech.FlatKoszulVanishing
public import StacksFrontier.RingTheory.Koszul.Localization
public import StacksFrontier.RingTheory.MvPolynomial.VariablesRegular

/-!
# The graded Čech complex of the last `n` variables of `R[x₁, …, x_m, y₁, …, y_n]`

Let `A = R[x₁, …, x_m, y₁, …, y_n]`, graded by `deg xᵢ = 0` and `deg yⱼ = 1`, and consider the
extended alternating Čech complex `C^•(y₁, …, y_n; A)`, whose degree-`p` term is the direct sum of
the localizations of `A` at the products of `p` of the `yⱼ`. Every term is `ℤ`-graded and the
differential preserves degrees. This file proves that **in every degree `p ≥ 1` and every weight
`e > -n`, a homogeneous cocycle of weight `e` is the coboundary of a homogeneous cochain of weight
`e`**.

In degrees `p < n` this holds in every weight: the `yⱼ` are a Koszul-regular sequence, so the
complex is exact outside its top degree `n`, and a homogeneous coboundary is the coboundary of a
homogeneous cochain (`Cech.exists_eq_cechD_of_exactAt`). In the top degree `n` every cochain is a
cocycle, and the weight bound is what makes it a coboundary: a fraction `μ / (y₁ ⋯ y_n)ᵏ` with `μ`
a monomial of `y`-weight `e + nk > n(k - 1)` has some exponent `μ(yⱼ) ≥ k`, so it is the image of
the fraction `(μ / yⱼᵏ) / (y₁ ⋯ ŷⱼ ⋯ y_n)ᵏ` of the localization omitting `yⱼ`. This is the
algebraic content of the vanishing `H^q(𝐏^{n-1}, 𝒪(e)) = 0` for `q > 0` and `e > -n`
([Stacks, Tag 01XT]), with the extra variables `xᵢ` as coefficients.

## Main definitions

* `Cech.WeightedVariables.yVar`: the family `y₁, …, y_n` of `A`.
* `Cech.WeightedVariables.natGrading` and `Cech.WeightedVariables.intGrading`: the grading of `A`
  by `deg yⱼ = 1`, valued in `ℕ` (the grading of the ring) and in `ℤ` (the grading of `A` as a
  module, which is what the localizations inherit).

## Main results

* `Cech.WeightedVariables.isKoszulRegular_yVar`: the `yⱼ` are Koszul-regular.
* `Cech.WeightedVariables.exists_eq_cechD_of_ne`: the statement outside the top degree, in every
  weight.
* `Cech.WeightedVariables.exists_eq_cechD_top`: the top-degree statement.
* `Cech.WeightedVariables.exists_eq_cechD_of_neg_lt`: **the main statement**, in every degree
  `p + 1` (it is vacuous in degree `1`, where it says that a homogeneous cocycle comes from `A`).
* `Cech.WeightedVariables.exists_eq_cechD_sum`: the same for a finite sum of homogeneous
  cocycles of weights at least `e`.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open MvPolynomial

attribute [local instance] instVAddNatIntGradedLocalizedModule

universe u

namespace Cech.WeightedVariables

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- The polynomial ring `A = R[x₁, …, x_m, y₁, …, y_n]`. -/
abbrev Ring : Type u := MvPolynomial (Fin m ⊕ Fin n) R

/-- The family `y₁, …, y_n` of `A`. -/
abbrev yVar : Fin n → Ring R m n := fun j => X (Sum.inr j)

/-- The grading of `A` by `deg xᵢ = 0`, `deg yⱼ = 1`, valued in `ℕ`. -/
abbrev natGrading : ℕ → Submodule R (Ring R m n) :=
  weightedHomogeneousSubmodule R (Sum.elim 0 1 : Fin m ⊕ Fin n → ℕ)

/-- The grading of `A` by `deg xᵢ = 0`, `deg yⱼ = 1`, valued in `ℤ`. -/
abbrev intGrading : ℤ → Submodule R (Ring R m n) :=
  weightedHomogeneousSubmodule R (Sum.elim 0 1 : Fin m ⊕ Fin n → ℤ)

/-- `A` is a graded algebra for the `ℕ`-valued grading `natGrading`. -/
instance : GradedAlgebra (natGrading R m n) := weightedGradedAlgebra R _

/-- `A` is a graded algebra for the `ℤ`-valued grading `intGrading`. -/
instance : GradedAlgebra (intGrading R m n) := weightedGradedAlgebra R _

/-- The weight of a monomial, read in `ℤ`, is the cast of its weight in `ℕ`. -/
theorem weight_int (μ : Fin m ⊕ Fin n →₀ ℕ) :
    Finsupp.weight (Sum.elim 0 1 : Fin m ⊕ Fin n → ℤ) μ =
      (Finsupp.weight (Sum.elim 0 1 : Fin m ⊕ Fin n → ℕ) μ : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rcases v with v | v <;> simp

/-- The part of `ℕ`-weight `i` of `A` lies in its part of `ℤ`-weight `i`. -/
theorem natGrading_le_intGrading (i : ℕ) :
    natGrading R m n i ≤ intGrading R m n (i : ℤ) := by
  intro a ha μ hμ
  rw [weight_int, ha hμ]

/-- `A` is a graded module over itself, the `ℕ`-graded ring acting on the `ℤ`-graded module. -/
instance : SetLike.GradedSMul (natGrading R m n) (intGrading R m n) where
  smul_mem {i j} a b ha hb := by
    have := (natGrading_le_intGrading R m n i ha).mul hb
    simpa [HVAdd.hVAdd, VAdd.vadd] using this

/-- Each `yⱼ` is homogeneous of weight `1`. -/
theorem yVar_mem (j : Fin n) : yVar R m n j ∈ natGrading R m n 1 := by
  simpa using isWeightedHomogeneous_X R (Sum.elim 0 1 : Fin m ⊕ Fin n → ℕ) (Sum.inr j)

/-! ### Koszul regularity of the `yⱼ` -/

/-- The identification `A ≅ R[x][y]` carrying `yⱼ` to the `j`-th variable. -/
def ringEquiv : MvPolynomial (Fin n) (MvPolynomial (Fin m) R) ≃ₐ[R] Ring R m n :=
  ((renameEquiv R (Equiv.sumComm (Fin m) (Fin n))).trans
    (sumAlgEquiv R (Fin n) (Fin m))).symm

/-- `ringEquiv` carries the `j`-th variable of `R[x][y]` to `yⱼ`. -/
theorem ringEquiv_X (j : Fin n) : ringEquiv R m n (X j) = yVar R m n j := by
  rw [ringEquiv, AlgEquiv.symm_apply_eq, AlgEquiv.trans_apply, renameEquiv_apply, rename_X]
  exact (sumAlgEquiv_X_inl R (Fin n) (Fin m) j).symm

/-- **The `yⱼ` are a Koszul-regular sequence in `A`**. -/
theorem isKoszulRegular_yVar [Nontrivial R] (n' : ℕ) :
    Koszul.IsKoszulRegular (yVar R m (n' + 1)) := by
  let : Algebra (MvPolynomial (Fin (n' + 1)) (MvPolynomial (Fin m) R)) (Ring R m (n' + 1)) :=
    (ringEquiv R m (n' + 1)).toRingEquiv.toRingHom.toAlgebra
  have : Module.Flat (MvPolynomial (Fin (n' + 1)) (MvPolynomial (Fin m) R))
      (Ring R m (n' + 1)) :=
    Module.Flat.of_linearEquiv
      ((LinearEquiv.ofBijective
        (Algebra.linearMap (MvPolynomial (Fin (n' + 1)) (MvPolynomial (Fin m) R))
          (Ring R m (n' + 1)))
        (ringEquiv R m (n' + 1)).bijective).symm)
  have h := Koszul.isKoszulRegular_map_of_flat (S := Ring R m (n' + 1))
    (X : Fin (n' + 1) → MvPolynomial (Fin (n' + 1)) (MvPolynomial (Fin m) R))
    (MvPolynomial.isKoszulRegular_X (n'))
  convert h using 1
  funext j
  exact (ringEquiv_X R m (n' + 1) j).symm

/-! ### Exactness outside the top degree -/

/-- **Outside the top degree a homogeneous cocycle is a homogeneous coboundary**, in every
weight. -/
theorem exists_eq_cechD_of_ne [Nontrivial R] (n' : ℕ) (e : ℤ) (p : ℕ) (hp : p + 1 ≠ n' + 1)
    {z : cechTerm (yVar R m (n' + 1)) (Ring R m (n' + 1)) (p + 1)}
    (hz : z ∈ gradedCechTerm (natGrading R m (n' + 1)) (intGrading R m (n' + 1))
      (yVar R m (n' + 1)) e (p + 1))
    (hdz : cechD (yVar R m (n' + 1)) (Ring R m (n' + 1)) (p + 1) z = 0) :
    ∃ w ∈ gradedCechTerm (natGrading R m (n' + 1)) (intGrading R m (n' + 1))
      (yVar R m (n' + 1)) e p, cechD (yVar R m (n' + 1)) (Ring R m (n' + 1)) p w = z := by
  have h0 := Cech.cechComplex_homology_isZero_of_isKoszulRegular (yVar R m (n' + 1))
    (isKoszulRegular_yVar R m n') (p + 1) hp
  exact exists_eq_cechD_of_exactAt (natGrading R m (n' + 1)) (intGrading R m (n' + 1))
    (yVar R m (n' + 1)) (c := fun _ => 1) (yVar_mem R m (n' + 1)) e p
    (((cechComplex _ _).exactAt_iff_isZero_homology (p + 1)).2 h0) hz hdz

/-! ### The top degree -/

/-- The `y`-weight of a monomial is the sum of its exponents at the `yⱼ`. -/
theorem weight_int_eq_sum (μ : Fin m ⊕ Fin n →₀ ℕ) :
    Finsupp.weight (Sum.elim 0 1 : Fin m ⊕ Fin n → ℤ) μ = ∑ j : Fin n, (μ (Sum.inr j) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]
  simp

/-- A monomial of `y`-weight `> n(k - 1)` has some exponent `≥ k` at a `yⱼ`. -/
theorem exists_le_of_weight (μ : Fin m ⊕ Fin n →₀ ℕ) (k : ℕ)
    (h : (n : ℤ) * ((k : ℤ) - 1) < Finsupp.weight (Sum.elim 0 1 : Fin m ⊕ Fin n → ℤ) μ) :
    ∃ j, k ≤ μ (Sum.inr j) := by
  by_contra hne
  push Not at hne
  rw [weight_int_eq_sum] at h
  have : ∑ j : Fin n, (μ (Sum.inr j) : ℤ) ≤ ∑ _j : Fin n, ((k : ℤ) - 1) :=
    Finset.sum_le_sum fun j _ => by have := hne j; omega
  simp at this
  linarith

/-- Two summands of the Čech term indexed by equal sets receive the same image of a transition
map. -/
theorem lof_cechι_congr {N : ℕ} {p : ℕ} {s t t' : Finset (Fin N)} (htt' : t = t')
    (ht : t.card = p) (ht' : t'.card = p) (h : s ⊆ t) (h' : s ⊆ t')
    (x : cechMod (yVar R m N) (Ring R m N) s) :
    DirectSum.lof (Ring R m N) {u : Finset (Fin N) // u.card = p}
        (fun u => cechMod (yVar R m N) (Ring R m N) u.1) ⟨t, ht⟩
        (cechι (yVar R m N) (Ring R m N) h x) =
      DirectSum.lof (Ring R m N) {u : Finset (Fin N) // u.card = p}
        (fun u => cechMod (yVar R m N) (Ring R m N) u.1) ⟨t', ht'⟩
        (cechι (yVar R m N) (Ring R m N) h' x) := by
  subst htt'
  rfl

/-- A product of distinct `yⱼ` is a nonzero element of `y`-weight its number of factors. -/
theorem prod_yVar_mem [Nontrivial R] {N : ℕ} (s : Finset (Fin N)) :
    (∏ i ∈ s, yVar R m N i) ∈ natGrading R m N s.card ∧ (∏ i ∈ s, yVar R m N i) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · simpa using SetLike.prod_mem_graded (A := natGrading R m N) (i := fun _ => 1)
      (g := fun i => yVar R m N i) (F := s) (fun i _ => yVar_mem R m N i)
  · have h : (∏ i ∈ s, yVar R m N i) =
        monomial (∑ i ∈ s, Finsupp.single (Sum.inr i) 1) (1 : R) := by
      rw [monomial_sum_one]; rfl
    rw [h, Ne, monomial_eq_zero]; exact one_ne_zero

/-- **The top-degree statement**: in degree `n` every fraction of weight `e > -n` is the
coboundary of a cochain of weight `e`. -/
theorem exists_eq_cechD_top [Nontrivial R] (n' : ℕ) (e : ℤ) (he : -((n' : ℤ) + 1) < e)
    (z : cechTerm (yVar R m (n' + 1)) (Ring R m (n' + 1)) (n' + 1))
    (hz : z ∈ gradedCechTerm (natGrading R m (n' + 1)) (intGrading R m (n' + 1))
      (yVar R m (n' + 1)) e (n' + 1)) :
    ∃ w ∈ gradedCechTerm (natGrading R m (n' + 1)) (intGrading R m (n' + 1))
      (yVar R m (n' + 1)) e n', cechD (yVar R m (n' + 1)) (Ring R m (n' + 1)) n' w = z := by
  classical
  let U : {u : Finset (Fin (n' + 1)) // u.card = n' + 1} := ⟨Finset.univ, by simp⟩
  let S : AddSubgroup (cechMod (yVar R m (n' + 1)) (Ring R m (n' + 1)) U.1) :=
    { carrier := {x | ∃ w ∈ gradedCechTerm (natGrading R m (n' + 1)) (intGrading R m (n' + 1))
          (yVar R m (n' + 1)) e n',
        cechD (yVar R m (n' + 1)) (Ring R m (n' + 1)) n' w =
          DirectSum.lof (Ring R m (n' + 1)) _
            (fun u => cechMod (yVar R m (n' + 1)) (Ring R m (n' + 1)) u.1) U x}
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      add_mem' := by
        rintro a b ⟨w, hw, hw'⟩ ⟨w', hw₂, hw₂'⟩
        exact ⟨w + w', add_mem hw hw₂, by rw [map_add, hw', hw₂', map_add]⟩
      neg_mem' := by
        rintro a ⟨w, hw, hw'⟩
        exact ⟨-w, neg_mem hw, by rw [map_neg, hw', map_neg]⟩ }
  have hzU : z = DirectSum.lof (Ring R m (n' + 1)) _
      (fun u => cechMod (yVar R m (n' + 1)) (Ring R m (n' + 1)) u.1) U (z U) := by
    refine DFinsupp.ext fun u => ?_
    obtain rfl : u = U := Subtype.ext (Finset.eq_univ_of_card _ (by simpa using u.2))
    rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]
  have hgen : Stacks.GradedLocalization.gradedPiece (natGrading R m (n' + 1))
      (intGrading R m (n' + 1)) (∏ i ∈ U.1, yVar R m (n' + 1) i) e ≤ S := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨d, k, hf, a, ha, rfl⟩
    obtain ⟨hfN, hne⟩ := prod_yVar_mem R m U.1
    obtain rfl : d = n' + 1 := by
      have := IsWeightedHomogeneous.inj_right hne hf hfN
      simpa [U] using this
    rw [← a.support_sum_monomial_coeff]
    have hadd : ∀ (a b : Ring R m (n' + 1))
        (s : Submonoid.powers (∏ i ∈ U.1, yVar R m (n' + 1) i)),
        LocalizedModule.mk (a + b) s = LocalizedModule.mk a s + LocalizedModule.mk b s := by
      intro a b s
      rw [LocalizedModule.mk_add_mk, ← smul_add, LocalizedModule.mk_cancel_common_left]
    have hmk : ∀ (t : Finset (Fin m ⊕ Fin (n' + 1) →₀ ℕ))
        (g : (Fin m ⊕ Fin (n' + 1) →₀ ℕ) → Ring R m (n' + 1)),
        (∀ μ ∈ t, LocalizedModule.mk (g μ)
          (⟨(∏ i ∈ U.1, yVar R m (n' + 1) i) ^ k, ⟨k, rfl⟩⟩ :
            Submonoid.powers (∏ i ∈ U.1, yVar R m (n' + 1) i)) ∈ S) →
        LocalizedModule.mk (∑ μ ∈ t, g μ)
          (⟨(∏ i ∈ U.1, yVar R m (n' + 1) i) ^ k, ⟨k, rfl⟩⟩ :
            Submonoid.powers (∏ i ∈ U.1, yVar R m (n' + 1) i)) ∈ S := by
      intro t g hg
      induction t using Finset.induction_on with
      | empty => simp
      | insert μ t hμ ih =>
        rw [Finset.sum_insert hμ, hadd]
        exact add_mem (hg μ (Finset.mem_insert_self _ _))
          (ih fun ν hν => hg ν (Finset.mem_insert_of_mem hν))
    refine hmk _ _ fun μ hμ => ?_
    have hwμ : Finsupp.weight (Sum.elim 0 1 : Fin m ⊕ Fin (n' + 1) → ℤ) μ =
        e + k • ((n' + 1 : ℕ) : ℤ) :=
      ha (by simpa using hμ)
    obtain ⟨i, hi⟩ := exists_le_of_weight m (n' + 1) μ k (by
      rw [hwμ, nsmul_eq_mul]; push_cast; nlinarith)
    set μ' := μ - Finsupp.single (Sum.inr i) k with hμ'
    have hμμ' : μ = μ' + Finsupp.single (Sum.inr i) k := by
      rw [hμ', tsub_add_cancel_of_le]
      intro v
      by_cases hv : v = Sum.inr i
      · subst hv; simpa using hi
      · simp [Ne.symm hv]
    let s : {u : Finset (Fin (n' + 1)) // u.card = n'} :=
      ⟨Finset.univ.erase i, by rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; simp⟩
    let x : cechMod (yVar R m (n' + 1)) (Ring R m (n' + 1)) s.1 :=
      LocalizedModule.mk (monomial μ' (a.coeff μ))
        (⟨(∏ j ∈ s.1, yVar R m (n' + 1) j) ^ k, ⟨k, rfl⟩⟩ :
          Submonoid.powers (∏ j ∈ s.1, yVar R m (n' + 1) j))
    refine ⟨cechSign s.1 i • DirectSum.lof (Ring R m (n' + 1)) _
      (fun u => cechMod (yVar R m (n' + 1)) (Ring R m (n' + 1)) u.1) s x, ?_, ?_⟩
    · refine zsmul_mem (lof_mem_gradedCechTerm s ?_) _
      have hfs := (prod_yVar_mem R m s.1).1
      rw [s.2] at hfs
      refine Stacks.GradedLocalization.mk_mem_gradedPiece (natGrading R m (n' + 1))
        (intGrading R m (n' + 1)) hfs ?_
      refine isWeightedHomogeneous_monomial _ _ _ ?_
      have hsingle : Finsupp.weight (Sum.elim 0 1 : Fin m ⊕ Fin (n' + 1) → ℤ)
          (Finsupp.single (Sum.inr i) k) = k := by
        simp [Finsupp.weight_apply, Finsupp.sum_single_index]
      have h1 : Finsupp.weight (Sum.elim 0 1 : Fin m ⊕ Fin (n' + 1) → ℤ) μ =
          Finsupp.weight (Sum.elim 0 1 : Fin m ⊕ Fin (n' + 1) → ℤ) μ' + k := by
        conv_lhs => rw [hμμ']
        rw [map_add, hsingle]
      rw [hwμ, nsmul_eq_mul] at h1
      rw [nsmul_eq_mul]
      push_cast at h1
      linarith
    · rw [map_zsmul, cechD_lof]
      have hcompl : s.1ᶜ = {i} := by
        ext j; simp [s, eq_comm]
      have hi' : i ∈ s.1ᶜ := by rw [hcompl]; exact Finset.mem_singleton_self i
      have hatt : s.1ᶜ.attach = {⟨i, hi'⟩} := by
        ext ⟨j, hj⟩
        simp only [Finset.mem_attach, Finset.mem_singleton, true_iff, Subtype.mk.injEq]
        rw [hcompl] at hj; exact Finset.mem_singleton.1 hj
      rw [hatt, Finset.sum_singleton, smul_smul]
      have hsign : cechSign s.1 i * cechSign s.1 i = 1 := by
        rw [cechSign, ← pow_add, ← two_mul, pow_mul]; simp
      rw [hsign, one_smul,
        lof_cechι_congr R m (Finset.insert_erase (Finset.mem_univ i)) _ U.2 _
          (Finset.erase_subset i Finset.univ)]
      congr 1
      rw [cechι_mk_pow]
      have hsd : Finset.univ \ Finset.univ.erase i = {i} := by
        ext j; simp [eq_comm]
      have hnum : (∏ j ∈ Finset.univ \ Finset.univ.erase i, yVar R m (n' + 1) j) ^ k •
          monomial μ' (a.coeff μ) = monomial μ (a.coeff μ) := by
        rw [hsd, Finset.prod_singleton, smul_eq_mul, X_pow_eq_monomial, monomial_mul_monomial,
          one_mul, add_comm (Finsupp.single (Sum.inr i) k) μ', ← hμμ']
      rw [hnum]
  obtain ⟨w, hw, hw'⟩ := hgen (mem_gradedCechTerm.1 hz U)
  exact ⟨w, hw, hw'.trans hzU.symm⟩

/-! ### Every degree -/

/-- The Čech terms of a trivial ring vanish. -/
theorem cechTerm_eq_zero_of_subsingleton [Subsingleton R] {N p : ℕ}
    (z : cechTerm (yVar R m N) (Ring R m N) p) : z = 0 := by
  have : Subsingleton (Ring R m N) := inferInstance
  refine DFinsupp.ext fun s => ?_
  have : Subsingleton (cechMod (yVar R m N) (Ring R m N) s.1) := by
    refine ⟨fun a b => ?_⟩
    induction a using LocalizedModule.induction_on with
    | h x t =>
      induction b using LocalizedModule.induction_on with
      | h x' t' => rw [Subsingleton.elim x x', Subsingleton.elim t t']
  exact Subsingleton.elim _ _

/-- **A homogeneous cocycle of weight `e > -n` is the coboundary of a homogeneous cochain of
weight `e`**, in the extended Čech complex `C^•(y₁, …, y_n; A)` and in every degree `p + 1`. -/
theorem exists_eq_cechD_of_neg_lt (e : ℤ) (he : -(n : ℤ) < e) (p : ℕ)
    {z : cechTerm (yVar R m n) (Ring R m n) (p + 1)}
    (hz : z ∈ gradedCechTerm (natGrading R m n) (intGrading R m n) (yVar R m n) e (p + 1))
    (hdz : cechD (yVar R m n) (Ring R m n) (p + 1) z = 0) :
    ∃ w ∈ gradedCechTerm (natGrading R m n) (intGrading R m n) (yVar R m n) e p,
      cechD (yVar R m n) (Ring R m n) p w = z := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, zero_mem _, by rw [map_zero, cechTerm_eq_zero_of_subsingleton R m z]⟩
  obtain _ | n' := n
  · refine ⟨0, zero_mem _, ?_⟩
    rw [map_zero]
    refine (DFinsupp.ext fun s => ?_).symm
    exfalso
    have := s.2
    rw [Finset.card_eq_zero.2 (Finset.eq_empty_of_isEmpty s.1)] at this
    omega
  by_cases hp : p + 1 = n' + 1
  · obtain rfl : p = n' := by omega
    exact exists_eq_cechD_top R m p e (by push_cast at he; linarith) z hz
  · exact exists_eq_cechD_of_ne R m n' e p hp hz hdz

/-- **The same for a finite sum of homogeneous cocycles of weights `≥ e > -n`**: a cocycle which
is a finite sum of homogeneous cochains of weights at least `e` is the coboundary of a finite sum
of homogeneous cochains of the same weights. -/
theorem exists_eq_cechD_sum (e : ℤ) (he : -(n : ℤ) < e) (p : ℕ) (t : Finset ℤ)
    (ht : ∀ d ∈ t, e ≤ d) (z : ℤ → cechTerm (yVar R m n) (Ring R m n) (p + 1))
    (hz : ∀ d ∈ t,
      z d ∈ gradedCechTerm (natGrading R m n) (intGrading R m n) (yVar R m n) d (p + 1))
    (hdz : cechD (yVar R m n) (Ring R m n) (p + 1) (∑ d ∈ t, z d) = 0) :
    ∃ w : ℤ → cechTerm (yVar R m n) (Ring R m n) p,
      (∀ d ∈ t, w d ∈ gradedCechTerm (natGrading R m n) (intGrading R m n) (yVar R m n) d p) ∧
        cechD (yVar R m n) (Ring R m n) p (∑ d ∈ t, w d) = ∑ d ∈ t, z d := by
  classical
  have hcoc : ∀ d ∈ t, cechD (yVar R m n) (Ring R m n) (p + 1) (z d) = 0 := by
    intro d hd
    rw [map_sum] at hdz
    exact eq_zero_of_sum_mem_gradedCechTerm_eq_zero (natGrading R m n) (intGrading R m n)
      (yVar R m n) (c := fun _ => 1) (yVar_mem R m n) (p + 1 + 1) t _
      (fun d hd => cechD_mem_gradedCechTerm (natGrading R m n) (intGrading R m n) (yVar R m n)
        (c := fun _ => 1) (yVar_mem R m n) d (p + 1) (hz d hd)) hdz hd
  have hex : ∀ d ∈ t, ∃ w ∈ gradedCechTerm (natGrading R m n) (intGrading R m n) (yVar R m n) d p,
      cechD (yVar R m n) (Ring R m n) p w = z d := fun d hd =>
    exists_eq_cechD_of_neg_lt R m n d (lt_of_lt_of_le he (ht d hd)) p (hz d hd) (hcoc d hd)
  choose! w hw hw' using hex
  exact ⟨w, hw, by rw [map_sum]; exact Finset.sum_congr rfl hw'⟩

end Cech.WeightedVariables

end
