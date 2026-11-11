module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

/-!
# Lifts of a basis of `Iʲ/Iʲ⁺¹` acting on a flat module

Let `A` be a commutative ring, `I ⊆ A` an ideal and `a₁, …, aᵣ ∈ Iʲ`. This file studies the map
`(P/IP)ʳ → IʲP/Iʲ⁺¹P`, `(xᵢ) ↦ ∑ aᵢ xᵢ`, for an `A`-module `P`, phrased without quotients:

* `Module.Flat.forall_mem_smul_top_of_sum_smul_mem`: if `P` is flat and the `aᵢ` are linearly
  independent modulo `I` in the sense that `∑ cᵢ aᵢ ∈ Iʲ⁺¹` forces every `cᵢ ∈ I`, then
  `∑ aᵢ xᵢ ∈ Iʲ⁺¹P` forces every `xᵢ ∈ IP` (injectivity);
* `Submodule.exists_sub_sum_smul_mem_pow_succ_smul_top`: if `Iʲ ⊆ (a₁, …, aᵣ) + Iʲ⁺¹`, then every
  element of `IʲP` is `∑ aᵢ xᵢ` modulo `Iʲ⁺¹P`, for any module `P` (surjectivity);
* `Ideal.exists_pow_basis_lift`: over a Noetherian ring with `I` maximal, such `aᵢ` exist for
  every `j`: lifts of a basis of the finite-dimensional `A/I`-vector space `Iʲ/Iʲ⁺¹`;
* `Submodule.restrictScalars_map_pow_smul_top`: for an `A`-algebra `R` and an `R`-module `P`, the
  submodule `(IR)ᵏP` of `P` is `IᵏP`, so the statements above apply to `R`-modules with the
  powers of the extended ideal.

The transfer of flatness along `A → R → P` needed to apply the first statement to a flat (for
instance projective) `R`-module over a flat `A`-algebra `R` is Mathlib's `Module.Flat.trans`
(together with the instance `Module.Flat.of_projective`).

## Implementation notes

Injectivity is proved with the equational criterion of flatness
(`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`): a relation `∑ aᵢ xᵢ = ∑ bₖ pₖ` with
`bₖ ∈ Iʲ⁺¹` is trivial, which writes every `xᵢ` as a combination `∑ cᵢₗ yₗ` with
`∑ᵢ cᵢₗ aᵢ ∈ Iʲ⁺¹`, so that every `cᵢₗ ∈ I`.
-/

open scoped Pointwise

namespace Submodule

variable {A : Type*} [CommRing A] {P : Type*} [AddCommGroup P] [Module A P]

/-- An element of `I • ⊤` is a finite sum `∑ bₖ pₖ` with every `bₖ ∈ I`. -/
theorem exists_fintype_sum_smul_of_mem_ideal_smul_top {I : Ideal A} {y : P}
    (hy : y ∈ I • (⊤ : Submodule A P)) :
    ∃ (s : Finset P) (b : P → A), (∀ p, b p ∈ I) ∧ ∑ p ∈ s, b p • p = y := by
  rw [← Submodule.span_univ, ← Set.range_id,
    Submodule.mem_ideal_smul_span_iff_exists_sum] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  exact ⟨g.support, g, hg, rfl⟩

/-- **Surjectivity onto `IʲP/Iʲ⁺¹P`.** If `Iʲ ⊆ (a₁, …, aᵣ) + Iʲ⁺¹`, then for every `A`-module
`P` every element of `IʲP` is congruent modulo `Iʲ⁺¹P` to some `∑ aᵢ xᵢ`. -/
theorem exists_sub_sum_smul_mem_pow_succ_smul_top {I : Ideal A} {j r : ℕ} {a : Fin r → A}
    (hspan : I ^ j ≤ Ideal.span (Set.range a) ⊔ I ^ (j + 1)) {y : P}
    (hy : y ∈ I ^ j • (⊤ : Submodule A P)) :
    ∃ x : Fin r → P, y - ∑ i, a i • x i ∈ I ^ (j + 1) • (⊤ : Submodule A P) := by
  let L : (Fin r → P) →ₗ[A] P := ∑ i, a i • LinearMap.proj i
  have hL : ∀ x, L x = ∑ i, a i • x i := fun x => by simp [L]
  have hle : Ideal.span (Set.range a) • (⊤ : Submodule A P) ≤ LinearMap.range L := by
    refine Submodule.smul_le.2 fun s hs p _ => ?_
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hs
    refine ⟨fun i => c i • p, ?_⟩
    simp [hL, Finset.sum_smul, smul_smul, mul_comm]
  have hy' := Submodule.smul_mono_left (N := (⊤ : Submodule A P)) hspan hy
  rw [Submodule.sup_smul, Submodule.mem_sup] at hy'
  obtain ⟨u, hu, v, hv, rfl⟩ := hy'
  obtain ⟨x, hx⟩ := hle hu
  refine ⟨x, ?_⟩
  rw [← hL, hx]
  simpa using hv

/-- For an `A`-algebra `R`, an `R`-module `P` and an ideal `J` of `A`, the submodule `(JR)P` of `P`
is `JP`. -/
theorem restrictScalars_map_smul_top {R : Type*} [CommRing R] [Algebra A R] [Module R P]
    [IsScalarTower A R P] (J : Ideal A) :
    ((J.map (algebraMap A R)) • (⊤ : Submodule R P)).restrictScalars A =
      J • (⊤ : Submodule A P) := by
  refine le_antisymm (fun y hy => ?_) (Submodule.smul_le.2 fun b hb p _ => ?_)
  · rw [Submodule.restrictScalars_mem] at hy
    refine Submodule.smul_induction_on hy (fun s hs p hp => ?_) fun y z hy hz => add_mem hy hz
    clear hp
    induction hs using Submodule.span_induction generalizing p with
    | mem s hs =>
      obtain ⟨b, hb, rfl⟩ := hs
      rw [algebraMap_smul]
      exact Submodule.smul_mem_smul hb trivial
    | zero => simp
    | add s t _ _ hs ht => rw [add_smul]; exact add_mem (hs p) (ht p)
    | smul t s _ hs => rw [smul_eq_mul, mul_comm, mul_smul]; exact hs _
  · rw [Submodule.restrictScalars_mem, ← algebraMap_smul R b p]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hb) trivial

/-- For an `A`-algebra `R`, an `R`-module `P` and an ideal `J` of `A`, the submodule `(JR)ᵏP` of
`P` is `JᵏP`. -/
theorem restrictScalars_map_pow_smul_top {R : Type*} [CommRing R] [Algebra A R] [Module R P]
    [IsScalarTower A R P] (J : Ideal A) (k : ℕ) :
    ((J.map (algebraMap A R)) ^ k • (⊤ : Submodule R P)).restrictScalars A =
      J ^ k • (⊤ : Submodule A P) := by
  rw [← Ideal.map_pow, restrictScalars_map_smul_top]

/-- Membership form of `Submodule.restrictScalars_map_pow_smul_top`. -/
theorem mem_map_pow_smul_top_iff {R : Type*} [CommRing R] [Algebra A R] [Module R P]
    [IsScalarTower A R P] (J : Ideal A) (k : ℕ) (y : P) :
    y ∈ (J.map (algebraMap A R)) ^ k • (⊤ : Submodule R P) ↔ y ∈ J ^ k • (⊤ : Submodule A P) := by
  rw [← restrictScalars_map_pow_smul_top (R := R) (P := P) J k]
  rfl

end Submodule

namespace Module.Flat

variable {A : Type*} [CommRing A] {P : Type*} [AddCommGroup P] [Module A P]

/-- **Injectivity into `IʲP/Iʲ⁺¹P` for a flat module.** Let `a₁, …, aᵣ ∈ A` be such that
`∑ cᵢ aᵢ ∈ Iʲ⁺¹` forces every `cᵢ ∈ I`. If `P` is flat, then `∑ aᵢ xᵢ ∈ Iʲ⁺¹P` forces every
`xᵢ ∈ IP`. -/
theorem forall_mem_smul_top_of_sum_smul_mem [Module.Flat A P] {I : Ideal A} {j r : ℕ}
    {a : Fin r → A} (hind : ∀ c : Fin r → A, ∑ i, c i * a i ∈ I ^ (j + 1) → ∀ i, c i ∈ I)
    {x : Fin r → P} (hx : ∑ i, a i • x i ∈ I ^ (j + 1) • (⊤ : Submodule A P)) (i : Fin r) :
    x i ∈ I • (⊤ : Submodule A P) := by
  obtain ⟨s, b, hb, hsum⟩ := Submodule.exists_fintype_sum_smul_of_mem_ideal_smul_top hx
  let f : Fin r ⊕ s → A := Sum.elim a fun p : s => -b p
  let z : Fin r ⊕ s → P := Sum.elim x fun p : s => (p : P)
  have hrel : ∑ k, f k • z k = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [f, z, Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib]
    rw [Finset.sum_coe_sort s fun p => b p • p, hsum, ← sub_eq_add_neg, sub_self]
  obtain ⟨n, c, y, hxy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  have hcI : ∀ l, c (Sum.inl i) l ∈ I := by
    intro l
    refine hind (fun i => c (Sum.inl i) l) ?_ i
    have hl := hc l
    rw [Fintype.sum_sum_type, add_eq_zero_iff_eq_neg, ← Finset.sum_neg_distrib] at hl
    simp only [f, Sum.elim_inl, Sum.elim_inr, neg_mul, neg_neg] at hl
    simp_rw [mul_comm (c _ l)]
    rw [hl]
    exact Ideal.sum_mem _ fun p _ => Ideal.mul_mem_right _ _ (hb p)
  have := hxy (Sum.inl i)
  simp only [z, Sum.elim_inl] at this
  rw [this]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem_smul (hcI l) trivial

end Module.Flat

namespace Ideal

variable {A : Type*} [CommRing A]

/-- **Lifts of a basis of `Iʲ/Iʲ⁺¹`.** Over a Noetherian ring with `I` maximal, for every `j` there
are `a₁, …, aᵣ ∈ Iʲ` with `Iʲ ⊆ (a₁, …, aᵣ) + Iʲ⁺¹` and such that `∑ cᵢ aᵢ ∈ Iʲ⁺¹` forces every
`cᵢ ∈ I`: lifts of a basis of the finite-dimensional `A/I`-vector space `Iʲ/Iʲ⁺¹`. -/
theorem exists_pow_basis_lift [IsNoetherianRing A] (I : Ideal A) [I.IsMaximal] (j : ℕ) :
    ∃ (r : ℕ) (a : Fin r → A), (∀ i, a i ∈ I ^ j) ∧
      I ^ j ≤ Ideal.span (Set.range a) ⊔ I ^ (j + 1) ∧
      ∀ c : Fin r → A, ∑ i, c i * a i ∈ I ^ (j + 1) → ∀ i, c i ∈ I := by
  classical
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  let V := ↥(I ^ j) ⧸ (I • (⊤ : Submodule A ↥(I ^ j)))
  have : Module.Finite A ↥(I ^ j) := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  have : Module.Finite (A ⧸ I) V := Module.Finite.of_restrictScalars_finite A _ _
  let bV := Module.finBasis (A ⧸ I) V
  choose x hx using fun i => Submodule.Quotient.mk_surjective _ (bV i)
  have hmem : ∀ w : ↥(I ^ j), w ∈ I • (⊤ : Submodule A ↥(I ^ j)) ↔ (w : A) ∈ I ^ (j + 1) := by
    intro w
    rw [Submodule.mem_smul_top_iff, smul_eq_mul, ← pow_succ']
  have hsmul : ∀ (c : A) (w : ↥(I ^ j)),
      (Ideal.Quotient.mk I c) • (Submodule.Quotient.mk w : V) = Submodule.Quotient.mk (c • w) :=
    fun _ _ => rfl
  have hmks : ∀ w : Fin (Module.finrank (A ⧸ I) V) → ↥(I ^ j),
      ∑ i, (Submodule.Quotient.mk (w i) : V) = Submodule.Quotient.mk (∑ i, w i) :=
    fun w => (map_sum (Submodule.mkQ _) w _).symm
  refine ⟨Module.finrank (A ⧸ I) V, fun i => x i, fun i => (x i).2, ?_, ?_⟩
  · intro z hz
    choose c hc using fun i => Ideal.Quotient.mk_surjective (bV.repr
      (Submodule.Quotient.mk ⟨z, hz⟩) i)
    have hq : (Submodule.Quotient.mk ⟨z, hz⟩ : V) = Submodule.Quotient.mk (∑ i, c i • x i) := by
      conv_lhs => rw [← bV.sum_repr (Submodule.Quotient.mk ⟨z, hz⟩)]
      simp only [← hc, ← hx, hsmul, hmks]
    rw [Submodule.Quotient.eq, hmem] at hq
    have hz' : z = ∑ i, c i * (x i : A) + (z - ∑ i, c i * (x i : A)) := by ring
    rw [hz']
    refine Submodule.add_mem_sup ?_ (by simpa using hq)
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · intro c hc
    have h0 : ∑ i, Ideal.Quotient.mk I (c i) • bV i = 0 := by
      simp only [← hx, hsmul, hmks]
      rw [Submodule.Quotient.mk_eq_zero, hmem]
      simpa using hc
    intro i
    exact Ideal.Quotient.eq_zero_iff_mem.1
      (Fintype.linearIndependent_iff.1 bV.linearIndependent _ h0 i)

end Ideal
