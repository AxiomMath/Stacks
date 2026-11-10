/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CharPoly
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.DegreePolynomial

/-!
# The trace of an endomorphism of an abelian variety as an intersection number

Let `A` be an abelian variety of dimension `g ≥ 1` over a field `k`, `N` an invertible module on
`A` and `α : A ⟶ A` a homomorphism. Write `Q(f) = [f^* N] ∈ Pic(A)` for a morphism `f : A ⟶ A`
over `k`, `W = [N] + [(-1)^* N]`, and

`B(α, 1) = [(α + 1)^* N] - [α^* N] - [N]`

for the biadditive form attached to `Q` by the theorem of the cube (Tag 0BFE). Then

`Tr(α) · (W^g · A) = 2 ∑_{i < g} (W, …, B(α, 1), …, W · A)`,

with `B(α, 1)` in the `i`-th slot. Here `Tr(α)` is `Stacks.Groupoids.abelianVarietyTrace`, the
trace of `α` on the `ℓ`-adic Tate module for every `ℓ` invertible in `k`
(`Stacks.Groupoids.trace_tateModuleMap_eq_abelianVarietyTrace`). No symmetry of `N` is assumed.

The proof is the classical one ([Mumford, *Abelian varieties*, §19], [Milne, *Abelian varieties*,
I.10]). By the theorem of the cube, `2 Q(α - n) = U + n V + n² W` with `U = 2 Q(α)` and
`V = N⁻ - N - 2 B(α, 1)`, where `N⁻ = [(-1)^* N]`. The degree of an isogeny scales intersection
numbers (Tag 0BET), so `((2 Q(α - n))^g · A) = 2^g deg(α - n) (N^g · A) = 2^g χ_α(n) (N^g · A)`,
where `χ_α` is the characteristic polynomial (`Stacks.Groupoids.endCharPoly`). Both sides are
polynomials in `n`; comparing the coefficients of `n^(2g)` and `n^(2g-1)`, and subtracting the
same comparison for the trivial endomorphism, gives the formula.

## Main definitions

* `Stacks.QuadraticMap.quadraticExpansionPoly`: the polynomial `n ↦ I(U + nV + n²W, …)` for a
  multilinear form `I`.
* `Stacks.Groupoids.endPullbackClass`: the class `[f^* N]` in `Pic(A)`.

## Main results

* `Stacks.QuadraticMap.coeff_quadraticExpansionPoly`: the coefficient of `n^(2d-1)` in
  `I(U + nV + n²W, …)` is `∑_i I(W, …, V, …, W)`.
* `Stacks.Groupoids.abelianVarietyTrace_mul_eq_sum`: `Tr(α) · (W^g · A)` as a sum of intersection
  numbers with `[N] - [(-1)^* N] + 2 B(α, 1)` in one slot.
* `Stacks.Groupoids.abelianVarietyTrace_mul_eq_two_mul_sum`: the trace formula above.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.QuadraticMap

open Finset

variable {G : Type*} [AddCommGroup G]

/-- The expansion of `n ↦ I(U + nV + n²W, …, U + nV + n²W)` as a polynomial in `n`, for a
multilinear form `I` on `G^d`. -/
def quadraticExpansionPoly {d : ℕ} (I : MultilinearMap ℤ (fun _ : Fin d => G) ℤ) (U V W : G) :
    ℚ[X] :=
  ∑ σ : Fin d → Fin 3, C ((I fun i => ![U, V, W] (σ i) : ℤ) : ℚ) * Polynomial.X ^ (∑ i, (σ i : ℕ))

/-- Evaluating `quadraticExpansionPoly I U V W` at an integer `n` gives
`I(U + nV + n²W, …, U + nV + n²W)`. -/
theorem eval_quadraticExpansionPoly {d : ℕ} (I : MultilinearMap ℤ (fun _ : Fin d => G) ℤ)
    (U V W : G) (n : ℤ) :
    (quadraticExpansionPoly I U V W).eval (n : ℚ) =
      ((I fun _ => U + n • V + n ^ 2 • W : ℤ) : ℚ) := by
  classical
  have hsum : U + n • V + n ^ 2 • W = ∑ j : Fin 3, (n ^ (j : ℕ)) • ![U, V, W] j := by
    simp [Fin.sum_univ_three, add_assoc]
  rw [hsum, MultilinearMap.map_sum, quadraticExpansionPoly, eval_finsetSum, Int.cast_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul, eval_mul, eval_C, eval_pow, eval_X,
    Int.cast_mul, Int.cast_prod, mul_comm]
  push_cast
  rw [prod_pow_eq_pow_sum]

/-- For `σ : Fin d → Fin 3`, the sums of `σ i` and of `2 - σ i` add up to `2d`. -/
private theorem sum_add_sum_two_sub {d : ℕ} (σ : Fin d → Fin 3) :
    ∑ i, (σ i : ℕ) + ∑ i, (2 - (σ i : ℕ)) = 2 * d := by
  rw [← sum_add_distrib]
  have : ∀ i, (σ i : ℕ) + (2 - (σ i : ℕ)) = 2 := fun i => by have := (σ i).isLt; omega
  simp [this, mul_comm]

/-- For `d > 0`, a map `Fin d → Fin 3` whose values sum to `2d - 1` takes the value `1` exactly
once and the value `2` everywhere else. -/
theorem exists_eq_update_of_sum_eq {d : ℕ} (hd : 0 < d) (σ : Fin d → Fin 3)
    (hσ : ∑ i, (σ i : ℕ) = 2 * d - 1) :
    ∃ i, σ = Function.update (fun _ => (2 : Fin 3)) i 1 := by
  classical
  set τ : Fin d → ℕ := fun i => 2 - (σ i : ℕ) with hτ
  have hle : ∀ i, (σ i : ℕ) ≤ 2 := fun i => Nat.lt_succ_iff.mp (σ i).isLt
  have hsplit : ∑ i, (σ i : ℕ) + ∑ i, τ i = 2 * d := sum_add_sum_two_sub σ
  have hτsum : ∑ i, τ i = 1 := by omega
  obtain ⟨i, -, hi⟩ : ∃ i ∈ (univ : Finset (Fin d)), τ i ≠ 0 := by
    by_contra h
    push Not at h
    rw [sum_eq_zero fun i hi => h i hi] at hτsum
    exact zero_ne_one hτsum
  have hrest := add_sum_erase univ τ (mem_univ i)
  rw [hτsum] at hrest
  have hτi : τ i = 1 := by omega
  have hzero : ∀ j ∈ univ.erase i, τ j = 0 := sum_eq_zero_iff.mp (by omega)
  refine ⟨i, funext fun j => ?_⟩
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    apply Fin.ext
    simp only [hτ] at hτi
    have := hle j
    simp only [Fin.isValue, Fin.val_one]
    omega
  · rw [Function.update_of_ne hj]
    have h0 := hzero j (mem_erase.mpr ⟨hj, mem_univ j⟩)
    simp only [hτ] at h0
    apply Fin.ext
    have := hle j
    simp only [Fin.isValue, Fin.val_two]
    omega

/-- The coefficient of `n^(2d-1)` in `n ↦ I(U + nV + n²W, …)` on `G^d`, `d > 0`. -/
theorem coeff_quadraticExpansionPoly {d : ℕ} (hd : 0 < d)
    (I : MultilinearMap ℤ (fun _ : Fin d => G) ℤ) (U V W : G) :
    (quadraticExpansionPoly I U V W).coeff (2 * d - 1) =
      ∑ i : Fin d, ((I (Function.update (fun _ => W) i V) : ℤ) : ℚ) := by
  classical
  set upd : Fin d → (Fin d → Fin 3) :=
    fun i => Function.update (fun _ => (2 : Fin 3)) i 1 with hupd
  have hupd_apply : ∀ i j, (upd i j : ℕ) = if j = i then 1 else 2 := fun i j => by
    by_cases h : j = i
    · subst h; simp [hupd]
    · simp [hupd, h]
  have hsum_upd : ∀ i, ∑ j, (upd i j : ℕ) = 2 * d - 1 := fun i => by
    simp only [hupd_apply]
    rw [sum_ite, filter_eq' univ i, filter_ne' univ i, sum_const, sum_const,
      card_erase_of_mem (mem_univ i), ite_eq_left (mem_univ i), card_singleton, card_univ,
      Fintype.card_fin]
    simp only [smul_eq_mul]
    omega
  have hinj : Function.Injective upd := fun i i' h => by
    have := congrFun h i
    by_contra hne
    have h1 : (upd i i : ℕ) = 1 := by rw [hupd_apply, ite_eq_left rfl]
    have h2 : (upd i' i : ℕ) = 2 := by rw [hupd_apply, ite_eq_right hne]
    rw [this] at h1
    omega
  have hfilter : univ.filter (fun σ : Fin d → Fin 3 => 2 * d - 1 = ∑ i, (σ i : ℕ)) =
      univ.image upd := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h
      obtain ⟨i, hi⟩ := exists_eq_update_of_sum_eq hd σ h.symm
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, rfl⟩
      exact (hsum_upd i).symm
  rw [quadraticExpansionPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [← sum_filter, hfilter, sum_image fun i _ i' _ h => hinj h]
  refine sum_congr rfl fun i _ => ?_
  congr 3
  funext j
  by_cases h : j = i
  · subst h; simp [hupd]
  · simp [hupd, Function.update_of_ne h]

/-- The coefficient of `n^(2d)` in `n ↦ I(U + nV + n²W, …)` on `G^d` is `I(W, …, W)`. -/
theorem coeff_two_mul_quadraticExpansionPoly {d : ℕ}
    (I : MultilinearMap ℤ (fun _ : Fin d => G) ℤ) (U V W : G) :
    (quadraticExpansionPoly I U V W).coeff (2 * d) = ((I fun _ => W : ℤ) : ℚ) := by
  classical
  have hle : ∀ (σ : Fin d → Fin 3) i, (σ i : ℕ) ≤ 2 := fun σ i => Nat.lt_succ_iff.mp (σ i).isLt
  have hfilter : univ.filter (fun σ : Fin d → Fin 3 => 2 * d = ∑ i, (σ i : ℕ)) =
      {fun _ => (2 : Fin 3)} := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro h
      have hsum : ∑ i, (2 - (σ i : ℕ)) = 0 := by
        have := sum_add_sum_two_sub σ
        omega
      funext i
      have := (sum_eq_zero_iff.mp hsum) i (mem_univ i)
      have := hle σ i
      apply Fin.ext
      simp only [Fin.isValue, Fin.val_two]
      omega
    · rintro rfl
      simp [mul_comm]
  rw [quadraticExpansionPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [← sum_filter, hfilter, sum_singleton]
  rfl

end Stacks.QuadraticMap

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [AlgebraicGeometry.IsAbelianVariety k A]

/-- The class `Q(f) = [f^* N]` in `Pic(A)` of the pullback of `N` along a morphism `f : A ⟶ A`
over `k`, on the additive group of such morphisms. -/
abbrev endPullbackClass (N : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hN : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf N)
    (x : Additive (A ⟶ A)) :
    Stacks.SheafOfModules.PicardGroup A.left.presheaf A.left.ringCatIsSheaf :=
  Stacks.SheafOfModules.pullbackPicardClass (Additive.toMul x).left N hN

omit [IsCommMonObj A] in
/-- The theorem of the cube for `endPullbackClass`:
`Q(x + y + z) + Q(x) + Q(y) + Q(z) = Q(x + y) + Q(x + z) + Q(y + z)`. -/
theorem endPullbackClass_cube (N : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hN : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf N)
    (x y z : Additive (A ⟶ A)) :
    endPullbackClass A N hN (x + y + z) + endPullbackClass A N hN x + endPullbackClass A N hN y +
        endPullbackClass A N hN z =
      endPullbackClass A N hN (x + y) + endPullbackClass A N hN (x + z) +
        endPullbackClass A N hN (y + z) :=
  pullbackPicardClass_cubeRelation A (hasTheoremOfTheCube k A) N hN
    (Additive.toMul x) (Additive.toMul y) (Additive.toMul z)

omit [IsCommMonObj A] in
/-- `(f^* N)^g · A = deg f · (N^g · A)` on classes, for every morphism `f : A ⟶ A` over `k`
([Stacks, Tag 0BET], `Stacks.Groupoids.endDegree_mul_selfIntersectionNumber`). -/
theorem picardIntersection_endPullbackClass
    (N : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hN : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf N)
    (f : A ⟶ A) :
    picardIntersection k A.hom (𝟙 A.left) (abelianVarietyDimension A)
        (topologicalKrullDim_eq_abelianVarietyDimension A).le
        (fun _ => endPullbackClass A N hN (Additive.ofMul f)) =
      endDegree A f * selfIntersectionNumber k A.hom (𝟙 A.left) (abelianVarietyDimension A)
        (topologicalKrullDim_eq_abelianVarietyDimension A).le N := by
  have : SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatSheaf.2 N := hN
  have : SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatSheaf.2
      ((Scheme.Modules.pullback f.left).obj N) :=
    RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme _ N
  have hform := picardIntersection_picardClass k A.hom (𝟙 A.left) _
    (topologicalKrullDim_eq_abelianVarietyDimension A).le
    (fun _ => (Scheme.Modules.pullback f.left).obj N)
  rw [← selfIntersectionNumber_eq_intersectionNumber] at hform
  rw [endDegree_mul_selfIntersectionNumber A f N, ← hform]
  rfl

/-- **The trace of an endomorphism as an intersection number.** For an abelian variety `A` of
dimension `g ≥ 1`, an invertible module `N` on `A` and a homomorphism `α : A ⟶ A`, write
`Q(f) = [f^* N]`, `W = Q(1) + Q(-1) = [N] + [(-1)^* N]` and `B(α, 1) = Q(α + 1) - Q(α) - Q(1)`.
Then `Tr(α) · (W^g · A) = ∑_i (W, …, Q(1) - Q(-1) + 2 B(α, 1), …, W · A)`, the `i`-th slot
carrying `Q(1) - Q(-1) + 2 B(α, 1)`. -/
theorem abelianVarietyTrace_mul_eq_sum
    (N : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hN : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf N)
    (α : A ⟶ A) [IsMonHom α] (hg : 0 < abelianVarietyDimension A) :
    let Q := endPullbackClass A N hN
    let I := picardIntersection k A.hom (𝟙 A.left) (abelianVarietyDimension A)
      (topologicalKrullDim_eq_abelianVarietyDimension A).le
    let W := Q (Additive.ofMul (𝟙 A)) + Q (-Additive.ofMul (𝟙 A))
    (abelianVarietyTrace A α : ℚ) * (I fun _ => W : ℤ) =
      ∑ i : Fin (abelianVarietyDimension A), ((I (Function.update (fun _ => W) i
        (Q (Additive.ofMul (𝟙 A)) - Q (-Additive.ofMul (𝟙 A)) +
          (2 : ℤ) • Stacks.QuadraticMap.cubeBilin Q (Additive.ofMul α) (Additive.ofMul (𝟙 A))))
        : ℤ) : ℚ) := by
  intro Q I W
  have hQ := endPullbackClass_cube A N hN
  set e := Additive.ofMul (𝟙 A)
  set a := Additive.ofMul α
  set B := Stacks.QuadraticMap.cubeBilin Q a e
  set I0 := selfIntersectionNumber k A.hom (𝟙 A.left) (abelianVarietyDimension A)
    (topologicalKrullDim_eq_abelianVarietyDimension A).le N
  set U := (2 : ℤ) • Q a
  set V := Q (-e) - Q e - (2 : ℤ) • B
  have hexp : ∀ n : ℤ, (2 : ℤ) • Q (Additive.ofMul (α * ((𝟙 A) ^ n)⁻¹)) =
      U + n • V + n ^ 2 • W := by
    intro n
    have h := Stacks.QuadraticMap.two_smul_map_sum_zsmul_of_cube hQ ![1, n] ![a, -e]
    have hsum : ∑ k, (![1, n] : Fin 2 → ℤ) k • (![a, -e] : Fin 2 → Additive (A ⟶ A)) k =
        Additive.ofMul (α * ((𝟙 A) ^ n)⁻¹) := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul]
      rw [ofMul_mul, ofMul_inv, ofMul_zpow, smul_neg]
    rw [hsum] at h
    have hB : Stacks.QuadraticMap.cubeBilin Q a (-e) = -B := by
      simpa using Stacks.QuadraticMap.cubeBilin_zsmul hQ 1 (-1) a e
    rw [h, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      lt_self_iff_false, ite_false, zero_smul, add_zero, Fin.zero_lt_one, ite_true,
      not_lt_zero, neg_neg]
    simp only [U, V, W, Q, B, e, a] at hB ⊢
    rw [hB]
    module
  set c : ℚ := ((2 ^ abelianVarietyDimension A * I0 : ℤ) : ℚ)
  have heval : ∀ n : ℤ, (Stacks.QuadraticMap.quadraticExpansionPoly I U V W).eval (n : ℚ) =
      (C c * endCharPoly A α).eval (n : ℚ) := by
    intro n
    rw [Stacks.QuadraticMap.eval_quadraticExpansionPoly, ← hexp n, eval_mul, eval_C,
      eval_intCast_endCharPoly]
    have h2 : (I fun _ => (2 : ℤ) • Q (Additive.ofMul (α * ((𝟙 A) ^ n)⁻¹))) =
        2 ^ abelianVarietyDimension A *
          I (fun _ => Q (Additive.ofMul (α * ((𝟙 A) ^ n)⁻¹))) := by
      rw [MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul]
    rw [h2]
    simp only [I, Q]
    rw [picardIntersection_endPullbackClass]
    simp only [c]
    push_cast
    ring
  have hpoly : Stacks.QuadraticMap.quadraticExpansionPoly I U V W = C c * endCharPoly A α :=
    Polynomial.eq_of_infinite_eval_eq _ _
      (Set.infinite_of_injective_forall_mem (f := fun n : ℤ => (n : ℚ)) Int.cast_injective heval)
  have hmonic := endCharPoly_monic A α
  have hdeg := natDegree_endCharPoly A α
  have hW : ((I fun _ => W : ℤ) : ℚ) = c := by
    rw [← Stacks.QuadraticMap.coeff_two_mul_quadraticExpansionPoly I U V W, hpoly, coeff_C_mul,
      ← hdeg, hmonic.coeff_natDegree, mul_one]
  have hV :
      ∑ i : Fin (abelianVarietyDimension A), ((I (Function.update (fun _ => W) i V) : ℤ) : ℚ) =
        c * (endCharPoly A α).nextCoeff := by
    rw [← Stacks.QuadraticMap.coeff_quadraticExpansionPoly hg I U V W, hpoly, coeff_C_mul,
      nextCoeff_of_natDegree_pos (by omega), hdeg]
  have hneg : Q e - Q (-e) + (2 : ℤ) • B = -V := by
    simp only [V]; abel
  simp only [abelianVarietyTrace]
  rw [hW, hneg]
  simp only [MultilinearMap.map_update_neg, Int.cast_neg, Finset.sum_neg_distrib, hV]
  ring

/-- The characteristic polynomial of the trivial endomorphism is `X^(2g)`. -/
theorem endCharPoly_one :
    endCharPoly A (1 : A ⟶ A) = Polynomial.X ^ (2 * abelianVarietyDimension A) := by
  refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => (n : ℚ)) Int.cast_injective ?_
  intro n
  change (endCharPoly A 1).eval (n : ℚ) =
    (Polynomial.X ^ (2 * abelianVarietyDimension A)).eval (n : ℚ)
  rw [eval_intCast_endCharPoly, one_mul, ← zpow_neg, eval_pow, eval_X]
  have h := endDegree_zpow_id_eq_pow A (-n)
  have h' : ((endDegree A ((𝟙 A : A ⟶ A) ^ (-n)) : ℤ) : ℚ) =
      (((-n) ^ (2 * abelianVarietyDimension A) : ℤ) : ℚ) := by rw [h]
  push_cast at h'
  rw [h', pow_mul, pow_mul, neg_sq]

/-- The trace of the trivial endomorphism is `0`. -/
theorem abelianVarietyTrace_one (hg : 0 < abelianVarietyDimension A) :
    abelianVarietyTrace A (1 : A ⟶ A) = 0 := by
  rw [abelianVarietyTrace, endCharPoly_one, nextCoeff_of_natDegree_pos (by
    rw [natDegree_X_pow]; omega), natDegree_X_pow, coeff_X_pow, ite_eq_right (by omega), neg_zero]

/-- **The trace of an endomorphism as an intersection number**, with the biadditive form alone:
`Tr(α) · (W^g · A) = 2 ∑_i (W, …, B(α, 1), …, W · A)` for `W = [N] + [(-1)^* N]` and
`B(α, 1) = [(α + 1)^* N] - [α^* N] - [N]`. -/
theorem abelianVarietyTrace_mul_eq_two_mul_sum
    (N : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hN : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf N)
    (α : A ⟶ A) [IsMonHom α] (hg : 0 < abelianVarietyDimension A) :
    let Q := endPullbackClass A N hN
    let I := picardIntersection k A.hom (𝟙 A.left) (abelianVarietyDimension A)
      (topologicalKrullDim_eq_abelianVarietyDimension A).le
    let W := Q (Additive.ofMul (𝟙 A)) + Q (-Additive.ofMul (𝟙 A))
    (abelianVarietyTrace A α : ℚ) * (I fun _ => W : ℤ) =
      2 * ∑ i : Fin (abelianVarietyDimension A), ((I (Function.update (fun _ => W) i
        (Stacks.QuadraticMap.cubeBilin Q (Additive.ofMul α) (Additive.ofMul (𝟙 A)))) : ℤ) : ℚ) := by
  intro Q I W
  have hQ := endPullbackClass_cube A N hN
  have h1 := abelianVarietyTrace_mul_eq_sum A N hN (1 : A ⟶ A) hg
  have hα := abelianVarietyTrace_mul_eq_sum A N hN α hg
  simp only at h1 hα
  have hB0 : Stacks.QuadraticMap.cubeBilin Q (Additive.ofMul (1 : A ⟶ A)) (Additive.ofMul (𝟙 A)) =
      0 := by
    simp only [Q, Stacks.QuadraticMap.cubeBilin, ofMul_one, zero_add,
      Stacks.QuadraticMap.map_zero_of_cube hQ, sub_zero, sub_self]
  rw [abelianVarietyTrace_one A hg, zero_mul, hB0, smul_zero, add_zero] at h1
  rw [hα, Finset.mul_sum, ← sub_zero (∑ i, _), h1, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MultilinearMap.map_update_add, MultilinearMap.map_update_smul, smul_eq_mul]
  push_cast
  ring

end Stacks.Groupoids
