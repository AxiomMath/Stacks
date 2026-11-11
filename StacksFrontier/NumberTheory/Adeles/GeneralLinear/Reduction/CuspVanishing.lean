module

public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.Reduction.Defs
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.CuspFormsFinite

/-!
# Cusp forms on `GL_n(A)` vanish near the cusps

Let `K` be a global function field over the finite field `k`, and let `f` be an unramified cusp
form on `GL_n(A)`. Let `b ∈ GL_n(A)` be upper triangular with diagonal `a`, and let `0 < r < n`
be such that `A = K + A(div a_i - div a_j)` for all `i < r ≤ j`; by Riemann–Roch this holds once
all `N(div a_i - div a_j)` with `i < r ≤ j` are large. Then `f (b) = 0`.

The proof generalizes the case `n = 2`
(`Stacks.Adeles.GlobalFunctionField.IsUnramifiedCuspForm.eq_zero_of_sup_eq_top`). The subgroup
`U` of the `z ∈ N_r(A)` for which `b z b⁻¹` has integral entries is open, and the integrand
`z ↦ f (b (1 + z))` is invariant under `U` because `b (1 + y) b⁻¹ = 1 + b y b⁻¹ ∈ GL_n(O)` for
`y ∈ U`. Moreover `N_r(A) = N_r(K) + U`: the entry `(i, j)` of `b z b⁻¹` is
`a_i z_{ij} a_j⁻¹` plus terms in the entries `z_{i'j'}` with `i ≤ i'`, `j' ≤ j` and
`(i', j') ≠ (i, j)`, so the entries of an element of `N_r(K)` can be chosen one level
`n - i + j` at a time. The constant term with the transversal `{0}` is then `f (b)`.

## Main results

* `Stacks.Adeles.GeneralLinear.IsUnramifiedCuspFormGL.eq_zero_of_sup_eq_top`.
* `Stacks.Adeles.GeneralLinear.cuspVanishing`.
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GeneralLinear

open Stacks.Adeles.GlobalFunctionField

section Triangular

variable {R : Type*} [CommRing R] {n : ℕ}

/-- For upper triangular `B` and `B'`, the entry `(p, q)` of `B z B'` vanishes when `z` vanishes
at every `(i, j)` with `p ≤ i` and `j ≤ q`. -/
public theorem mul_mul_apply_eq_zero_of_upper {B z B' : Matrix (Fin n) (Fin n) R}
    (hB : ∀ i j, j < i → B i j = 0) (hB' : ∀ i j, j < i → B' i j = 0) {p q : Fin n}
    (hz : ∀ i j, p ≤ i → j ≤ q → z i j = 0) : (B * z * B') p q = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j ≤ q
  · rw [Matrix.mul_apply, Finset.sum_eq_zero fun i _ => ?_, zero_mul]
    by_cases hi : p ≤ i
    · rw [hz i j hi hj, mul_zero]
    · rw [hB p i (not_le.1 hi), zero_mul]
  · rw [hB' j q (not_le.1 hj), mul_zero]

/-- For upper triangular `B` and `B'`, the entry `(p, q)` of `B z B'` is `B_{pp} z_{pq} B'_{qq}`
when `z` vanishes at every `(i, j) ≠ (p, q)` with `p ≤ i` and `j ≤ q`. -/
public theorem mul_mul_apply_eq_of_upper {B z B' : Matrix (Fin n) (Fin n) R}
    (hB : ∀ i j, j < i → B i j = 0) (hB' : ∀ i j, j < i → B' i j = 0) {p q : Fin n}
    (hz : ∀ i j, p ≤ i → j ≤ q → (i ≠ p ∨ j ≠ q) → z i j = 0) :
    (B * z * B') p q = B p p * z p q * B' q q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · rw [Matrix.mul_apply, Finset.sum_eq_single p]
    · intro i _ hi
      by_cases hpi : p ≤ i
      · rw [hz i q hpi le_rfl (Or.inl hi), mul_zero]
      · rw [hB p i (not_le.1 hpi), zero_mul]
    · simp
  · intro j _ hj
    by_cases hjq : j ≤ q
    · rw [Matrix.mul_apply, Finset.sum_eq_zero fun i _ => ?_, zero_mul]
      by_cases hpi : p ≤ i
      · rw [hz i j hpi hjq (Or.inr hj), mul_zero]
      · rw [hB p i (not_le.1 hpi), zero_mul]
    · rw [hB' j q (not_le.1 hjq), mul_zero]
  · simp

/-- Conjugating by upper triangular matrices preserves the unipotent radical `N_r`. -/
public theorem mul_mul_mem_unipotentRadical {B z B' : Matrix (Fin n) (Fin n) R}
    (hB : ∀ i j, j < i → B i j = 0) (hB' : ∀ i j, j < i → B' i j = 0) {r : ℕ}
    (hz : z ∈ unipotentRadical R n r) : B * z * B' ∈ unipotentRadical R n r := by
  intro p q hpq
  refine mul_mul_apply_eq_zero_of_upper hB hB' fun i j hi hj => hz i j fun h => hpq ⟨?_, ?_⟩
  · exact lt_of_le_of_lt (Fin.le_def.1 hi) h.1
  · exact h.2.trans (Fin.le_def.1 hj)

end Triangular

variable {K : Type u} [Field K] {n : ℕ}

/-- The inverse of an upper triangular `b` with diagonal `a` is upper triangular with
diagonal `a⁻¹`. -/
public theorem IsUpperTriangularWith.inv {b : GL (Fin n) (AdeleRing K)}
    {a : Fin n → (AdeleRing K)ˣ} (hb : IsUpperTriangularWith b a) :
    IsUpperTriangularWith b⁻¹ fun i => (a i)⁻¹ := by
  have htri : ∀ i j : Fin n, j < i → ((b⁻¹ : GL (Fin n) (AdeleRing K)) :
      Matrix (Fin n) (Fin n) (AdeleRing K)) i j = 0 := by
    have hbt : (b : Matrix (Fin n) (Fin n) (AdeleRing K)).BlockTriangular id :=
      fun i j h => hb.1 i j h
    let := Units.invertible b
    have := Matrix.blockTriangular_inv_of_blockTriangular hbt
    intro i j h
    rw [Matrix.coe_units_inv]
    exact this h
  refine ⟨htri, fun q => ?_⟩
  have h1 : ((b⁻¹ : GL (Fin n) (AdeleRing K)) : Matrix (Fin n) (Fin n) (AdeleRing K)) q q *
      (a q : AdeleRing K) = 1 := by
    have := congrFun (congrFun b.inv_mul q) q
    rw [Matrix.mul_apply, Finset.sum_eq_single q] at this
    · rwa [hb.2 q, Matrix.one_apply_eq] at this
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h | h
      · rw [htri q j h, zero_mul]
      · rw [hb.1 j q h, mul_zero]
    · simp
  calc ((b⁻¹ : GL (Fin n) (AdeleRing K)) : Matrix (Fin n) (Fin n) (AdeleRing K)) q q
      = ((b⁻¹ : GL (Fin n) (AdeleRing K)) : Matrix (Fin n) (Fin n) (AdeleRing K)) q q *
          ((a q : AdeleRing K) * ((a q)⁻¹ : (AdeleRing K)ˣ)) := by rw [Units.mul_inv, mul_one]
    _ = ((a q)⁻¹ : (AdeleRing K)ˣ) := by rw [← mul_assoc, h1, one_mul]

variable (n) in
/-- The subgroup of the `z ∈ N_r(A)` such that `b z b⁻¹` has integral entries. -/
public def conjIntegralSubgroup (b : GL (Fin n) (AdeleRing K)) (r : ℕ) :
    AddSubgroup (unipotentRadical (AdeleRing K) n r) where
  carrier := {z | ∀ p q, ((b : Matrix (Fin n) (Fin n) (AdeleRing K)) *
    (z : Matrix (Fin n) (Fin n) (AdeleRing K)) *
      ((b⁻¹ : GL (Fin n) (AdeleRing K)) : Matrix (Fin n) (Fin n) (AdeleRing K))) p q ∈
        integralAdeles K}
  zero_mem' p q := by simp
  add_mem' {z y} hz hy p q := by
    simpa [Matrix.mul_add, Matrix.add_mul] using (integralAdeles K).add_mem (hz p q) (hy p q)
  neg_mem' {z} hz p q := by
    simpa [Matrix.mul_neg, Matrix.neg_mul] using (integralAdeles K).neg_mem (hz p q)

/-- Membership in `conjIntegralSubgroup`. -/
public theorem mem_conjIntegralSubgroup {b : GL (Fin n) (AdeleRing K)} {r : ℕ}
    {z : unipotentRadical (AdeleRing K) n r} :
    z ∈ conjIntegralSubgroup n b r ↔ ∀ p q, ((b : Matrix (Fin n) (Fin n) (AdeleRing K)) *
      (z : Matrix (Fin n) (Fin n) (AdeleRing K)) *
        ((b⁻¹ : GL (Fin n) (AdeleRing K)) : Matrix (Fin n) (Fin n) (AdeleRing K))) p q ∈
          integralAdeles K :=
  Iff.rfl

/-- `conjIntegralSubgroup n b r` is open in `N_r(A)`. -/
public theorem isOpen_conjIntegralSubgroup (b : GL (Fin n) (AdeleRing K)) (r : ℕ) :
    IsOpen (conjIntegralSubgroup n b r : Set (unipotentRadical (AdeleRing K) n r)) := by
  have : Fact (∀ v : Place K, IsOpen (v.integers : Set v.completion)) :=
    ⟨fun v => Valued.isOpen_valuationSubring _⟩
  have hO : IsOpen (integralAdeles K : Set (AdeleRing K)) :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have : (conjIntegralSubgroup n b r : Set (unipotentRadical (AdeleRing K) n r)) =
      ⋂ p, ⋂ q, (fun z : unipotentRadical (AdeleRing K) n r =>
        ((b : Matrix (Fin n) (Fin n) (AdeleRing K)) *
          (z : Matrix (Fin n) (Fin n) (AdeleRing K)) *
            ((b⁻¹ : GL (Fin n) (AdeleRing K)) : Matrix (Fin n) (Fin n) (AdeleRing K))) p q) ⁻¹'
        (integralAdeles K : Set (AdeleRing K)) := by
    ext z
    simp only [SetLike.mem_coe, mem_conjIntegralSubgroup, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact isOpen_iInter_of_finite fun p => isOpen_iInter_of_finite fun q => hO.preimage
    (((continuous_const.matrix_mul continuous_subtype_val).matrix_mul
      continuous_const).matrix_elem p q)

/-- For `y ∈ conjIntegralSubgroup n b r`, `b (1 + y) = κ b` with `κ = 1 + b y b⁻¹ ∈ GL_n(O)`. -/
public theorem exists_mapO_mul_eq {b : GL (Fin n) (AdeleRing K)} {a : Fin n → (AdeleRing K)ˣ}
    (hb : IsUpperTriangularWith b a) {r : ℕ} {y : unipotentRadical (AdeleRing K) n r}
    (hy : y ∈ conjIntegralSubgroup n b r) :
    ∃ κ : GL (Fin n) (integralAdeles K), mapO K n κ * b = b * unipotentGL y := by
  set P := (b : Matrix (Fin n) (Fin n) (AdeleRing K)) *
    (y : Matrix (Fin n) (Fin n) (AdeleRing K)) *
      ((b⁻¹ : GL (Fin n) (AdeleRing K)) : Matrix (Fin n) (Fin n) (AdeleRing K)) with hP
  have hPN : P ∈ unipotentRadical (AdeleRing K) n r :=
    mul_mul_mem_unipotentRadical hb.1 hb.inv.1 y.2
  set W : Matrix (Fin n) (Fin n) (integralAdeles K) := Matrix.of fun p q => ⟨P p q, hy p q⟩
  have hW : W ∈ unipotentRadical (integralAdeles K) n r := fun p q h =>
    Subtype.ext (hPN p q h)
  refine ⟨unipotentGL ⟨W, hW⟩, ?_⟩
  have hmap : ((mapO K n (unipotentGL ⟨W, hW⟩) : GL (Fin n) (AdeleRing K)) :
      Matrix (Fin n) (Fin n) (AdeleRing K)) = 1 + P := by
    ext p q
    rw [GeneralLinearGroup.map_apply, coe_unipotentGL]
    by_cases h : p = q
    · subst h
      simp [W]
    · simp [W, Matrix.one_apply_ne h]
  ext1
  rw [Units.val_mul, Units.val_mul, hmap, coe_unipotentGL, hP, Matrix.add_mul, Matrix.one_mul,
    Matrix.mul_add, Matrix.mul_one]
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/-- The integrand `z ↦ f (b (1 + z))` of the constant term is invariant under
`conjIntegralSubgroup n b r`. -/
public theorem IsUnramifiedCuspFormGL.apply_mul_unipotentGL_add {Λ : Type w} [AddCommMonoid Λ]
    {f : GL (Fin n) (AdeleRing K) → Λ} (hf : IsUnramifiedCuspFormGL n f)
    {b : GL (Fin n) (AdeleRing K)} {a : Fin n → (AdeleRing K)ˣ}
    (hb : IsUpperTriangularWith b a) {r : ℕ} (z : unipotentRadical (AdeleRing K) n r)
    {y : unipotentRadical (AdeleRing K) n r} (hy : y ∈ conjIntegralSubgroup n b r) :
    f (b * unipotentGL (z + y)) = f (b * unipotentGL z) := by
  obtain ⟨κ, hκ⟩ := exists_mapO_mul_eq hb hy
  rw [add_comm, unipotentGL_add, ← mul_assoc, ← hκ, mul_assoc]
  exact hf.left_invariant _ κ

variable (k : Type u) [Field k] [Finite k] [Algebra k K] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- One entry of the approximation: when `A = K + A(div a_i - div a_j)`, every adele `x` is
`a_i κ a_j⁻¹` modulo `O` for a principal `κ`. -/
public theorem exists_principal_sub_mem_integralAdeles {a₁ a₂ : (AdeleRing K)ˣ}
    (h : principal k K ⊔ adeleLattice K (idelDiv k K a₁ - idelDiv k K a₂) = ⊤)
    (x : AdeleRing K) : ∃ κ ∈ principalAdeles K,
      x - (a₁ : AdeleRing K) * κ * ((a₂⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) ∈
        integralAdeles K := by
  have hprin : principal k K = (principalAdeles K).toAddSubgroup := by
    rw [principal, range_diag]
  have hx : ((a₁⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * x * (a₂ : AdeleRing K) ∈
      principal k K ⊔ adeleLattice K (idelDiv k K a₁ - idelDiv k K a₂) := by
    rw [h]
    exact AddSubgroup.mem_top _
  rw [hprin] at hx
  obtain ⟨κ, hκ, w, hw, hκw⟩ := AddSubgroup.mem_sup.1 hx
  refine ⟨κ, hκ, ?_⟩
  have h₁ := Units.mul_inv a₁
  have h₂ := Units.mul_inv a₂
  have heq : x - (a₁ : AdeleRing K) * κ * ((a₂⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) =
      ((a₂⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * ((a₁ : AdeleRing K) * w) := by
    linear_combination (-((a₁ : AdeleRing K) * ((a₂⁻¹ : (AdeleRing K)ˣ) : AdeleRing K))) * hκw -
      x * ((a₂ : AdeleRing K) * ((a₂⁻¹ : (AdeleRing K)ˣ) : AdeleRing K)) * h₁ - x * h₂
  rw [heq]
  have h1 := (idele_mul_mem_adeleLattice_iff k a₁).2 hw
  rw [sub_sub_cancel_left] at h1
  have h2 := (idele_mul_mem_adeleLattice_iff k a₂⁻¹ (E := -idelDiv k K a₂)).2 h1
  rw [idelDiv_inv, sub_neg_eq_add, neg_add_cancel] at h2
  exact mem_adeleLattice_zero_iff.1 h2

/-- The approximation, up to level `t`: when `A = K + A(div a_i - div a_j)` for all `i < r ≤ j`,
every `z ∈ N_r(A)` is congruent modulo `N_r(K)` to some `z'` such that the entries `(p, q)` of
`b z' b⁻¹` with `n - p + q < t` are integral. -/
public theorem exists_principalUnipotent_level {b : GL (Fin n) (AdeleRing K)}
    {a : Fin n → (AdeleRing K)ˣ} (hb : IsUpperTriangularWith b a) {r : ℕ}
    (hsup : ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) →
      principal k K ⊔ adeleLattice K (idelDiv k K (a i) - idelDiv k K (a j)) = ⊤)
    (z : unipotentRadical (AdeleRing K) n r) (t : ℕ) :
    ∃ c ∈ principalUnipotent K n r, ∀ p q : Fin n, n - (p : ℕ) + q < t →
      ((b : Matrix (Fin n) (Fin n) (AdeleRing K)) *
        ((z - c : unipotentRadical (AdeleRing K) n r) : Matrix (Fin n) (Fin n) (AdeleRing K)) *
          ((b⁻¹ : GL (Fin n) (AdeleRing K)) : Matrix (Fin n) (Fin n) (AdeleRing K))) p q ∈
        integralAdeles K := by
  classical
  induction t with
  | zero => exact ⟨0, zero_mem _, fun p q h => absurd h (Nat.not_lt_zero _)⟩
  | succ t ih =>
    obtain ⟨c, hc, H⟩ := ih
    set B := (b : Matrix (Fin n) (Fin n) (AdeleRing K))
    set B' := ((b⁻¹ : GL (Fin n) (AdeleRing K)) : Matrix (Fin n) (Fin n) (AdeleRing K))
    set P := B * ((z - c : unipotentRadical (AdeleRing K) n r) :
      Matrix (Fin n) (Fin n) (AdeleRing K)) * B' with hP
    have hex : ∀ i j : Fin n, ∃ κ ∈ principalAdeles K, (i : ℕ) < r → r ≤ (j : ℕ) →
        P i j - (a i : AdeleRing K) * κ * ((a j)⁻¹ : (AdeleRing K)ˣ) ∈ integralAdeles K := by
      intro i j
      by_cases hij : (i : ℕ) < r ∧ r ≤ (j : ℕ)
      · obtain ⟨κ, hκ, h⟩ := exists_principal_sub_mem_integralAdeles k (hsup i j hij.1 hij.2)
          (P i j)
        exact ⟨κ, hκ, fun _ _ => h⟩
      · exact ⟨0, zero_mem _, fun h1 h2 => absurd ⟨h1, h2⟩ hij⟩
    choose κ hκ hκP using hex
    set C : Matrix (Fin n) (Fin n) (AdeleRing K) := Matrix.of fun i j =>
      if n - (i : ℕ) + j = t ∧ (i : ℕ) < r ∧ r ≤ (j : ℕ) then κ i j else 0 with hC
    have hCN : C ∈ unipotentRadical (AdeleRing K) n r := fun i j h => by
      rw [hC, Matrix.of_apply, ite_eq_right_iff]
      exact fun h' => absurd h'.2 h
    set c' : unipotentRadical (AdeleRing K) n r := ⟨C, hCN⟩
    have hc' : c' ∈ principalUnipotent K n r := fun i j => by
      change C i j ∈ principalAdeles K
      rw [hC, Matrix.of_apply]
      split_ifs
      · exact hκ i j
      · exact zero_mem _
    refine ⟨c + c', add_mem hc hc', fun p q hpq => ?_⟩
    have hsplit : B * ((z - (c + c') : unipotentRadical (AdeleRing K) n r) :
        Matrix (Fin n) (Fin n) (AdeleRing K)) * B' = P - B * C * B' := by
      rw [hP, sub_add_eq_sub_sub, AddSubgroup.coe_sub _ (z - c) c', Matrix.mul_sub,
        Matrix.sub_mul]
    rw [hsplit, Matrix.sub_apply]
    have hp := p.isLt
    have hq := q.isLt
    rcases Nat.lt_succ_iff_lt_or_eq.1 hpq with hlt | heq
    · rw [mul_mul_apply_eq_zero_of_upper hb.1 hb.inv.1 fun i j hi hj => ?_, sub_zero]
      · exact H p q hlt
      · rw [hC, Matrix.of_apply, ite_eq_right_iff]
        rintro ⟨h, -⟩
        exfalso
        have := Fin.le_def.1 hi
        have := Fin.le_def.1 hj
        have := i.isLt
        omega
    · rw [mul_mul_apply_eq_of_upper hb.1 hb.inv.1 fun i j hi hj hne => ?_, hb.2 p,
        hb.inv.2 q]
      · by_cases hpq' : (p : ℕ) < r ∧ r ≤ (q : ℕ)
        · simp only [hC, Matrix.of_apply, heq, hpq'.1, hpq'.2, and_self, ↓reduceIte]
          exact hκP p q hpq'.1 hpq'.2
        · have hP0 : P p q = 0 :=
            mul_mul_mem_unipotentRadical hb.1 hb.inv.1 (z - c).2 p q hpq'
          rw [hC, Matrix.of_apply, ite_eq_right_iff.2 fun h => absurd h.2 hpq', hP0]
          simp
      · rw [hC, Matrix.of_apply, ite_eq_right_iff]
        rintro ⟨h, -⟩
        exfalso
        have := Fin.le_def.1 hi
        have := Fin.le_def.1 hj
        have := i.isLt
        rcases hne with hne | hne
        · exact hne (Fin.ext (by omega))
        · exact hne (Fin.ext (by omega))

/-- `N_r(A) = N_r(K) + U` for `U = conjIntegralSubgroup n b r`, when
`A = K + A(div a_i - div a_j)` for all `i < r ≤ j`. -/
public theorem principalUnipotent_sup_conjIntegralSubgroup_eq_top
    {b : GL (Fin n) (AdeleRing K)} {a : Fin n → (AdeleRing K)ˣ} (hb : IsUpperTriangularWith b a)
    {r : ℕ} (hsup : ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) →
      principal k K ⊔ adeleLattice K (idelDiv k K (a i) - idelDiv k K (a j)) = ⊤) :
    principalUnipotent K n r ⊔ conjIntegralSubgroup n b r = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨c, hc, H⟩ := exists_principalUnipotent_level k hb hsup z (2 * n)
  have hzc : z - c ∈ conjIntegralSubgroup n b r := fun p q =>
    H p q (by have := p.isLt; have := q.isLt; omega)
  have := AddSubgroup.add_mem_sup hc hzc
  rwa [add_sub_cancel] at this

/-- An unramified cusp form on `GL_n(A)` vanishes at an upper triangular `b` with diagonal `a`
when some `0 < r < n` has `A = K + A(div a_i - div a_j)` for all `i < r ≤ j`: this is its
constant term along `N_r` with the open subgroup `conjIntegralSubgroup n b r` and the
transversal `{0}`. -/
public theorem IsUnramifiedCuspFormGL.eq_zero_of_sup_eq_top {Λ : Type w} [AddCommMonoid Λ]
    {f : GL (Fin n) (AdeleRing K) → Λ} (hf : IsUnramifiedCuspFormGL n f)
    {b : GL (Fin n) (AdeleRing K)} {a : Fin n → (AdeleRing K)ˣ}
    (hb : IsUpperTriangularWith b a) {r : ℕ} (hr : 0 < r) (hrn : r < n)
    (hsup : ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) →
      principal k K ⊔ adeleLattice K (idelDiv k K (a i) - idelDiv k K (a j)) = ⊤) :
    f b = 0 := by
  have htop := principalUnipotent_sup_conjIntegralSubgroup_eq_top k hb hsup
  have hs : ∀ y : unipotentRadical (AdeleRing K) n r,
      ∃! z ∈ ({0} : Finset (unipotentRadical (AdeleRing K) n r)),
        y - z ∈ principalUnipotent K n r ⊔ conjIntegralSubgroup n b r := by
    intro y
    refine ⟨0, ⟨Finset.mem_singleton_self _, ?_⟩, fun z hz => Finset.mem_singleton.1 hz.1⟩
    rw [htop]
    exact AddSubgroup.mem_top _
  have := hf.vanishing_constant_term r hr hrn b (conjIntegralSubgroup n b r)
    (isOpen_conjIntegralSubgroup b r) (fun z _ hy =>
      IsUnramifiedCuspFormGL.apply_mul_unipotentGL_add hf hb z hy)
    {0} hs
  rwa [Finset.sum_singleton, unipotentGL_zero, mul_one] at this

variable (K) in
/-- **Vanishing of cusp forms near the cusps** (`Stacks.Adeles.GeneralLinear.CuspVanishing`):
there is `M` such that every unramified cusp form on `GL_n(A)` vanishes at every upper
triangular `b` with diagonal `a` for which some `0 < r < n` has `M ≤ N(div a_i - div a_j)` for
all `i < r ≤ j`. -/
public theorem cuspVanishing (n : ℕ) : CuspVanishing.{u, w} K n k := by
  obtain ⟨M, hM⟩ := exists_sup_adeleLattice_eq_top k (K := K)
  exact ⟨M, fun Λ _ f hf b a hb r hr hrn hgap =>
    IsUnramifiedCuspFormGL.eq_zero_of_sup_eq_top k hf hb hr hrn fun i j hi hj =>
      hM _ (hgap i j hi hj)⟩

end Stacks.Adeles.GeneralLinear

end
