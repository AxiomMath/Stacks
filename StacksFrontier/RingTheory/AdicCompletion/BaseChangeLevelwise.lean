module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksFrontier.RingTheory.AdicCompletion.LevelwiseBijective

/-!
# Extending scalars to the completion changes nothing at any level

Let `I` be a finitely generated ideal of a commutative ring `R`, write `R̂` for the `I`-adic
completion of `R` and let `X` be any `R`-module.  The unit

`X ⟶ R̂ ⊗_R X`, `x ↦ 1 ⊗ x`

is bijective modulo `Iᵏ` for every `k`.  The reason is that `R̂` and `R` have the same reduction
modulo `Iᵏ`: evaluation at level `k` is a ring map `R̂ → R / Iᵏ` under which `R → R̂ → R / Iᵏ` is
the
quotient map, and its kernel is `Iᵏ R̂` because `I` is finitely generated
(`AdicCompletion.pow_smul_top_eq_ker_eval`).  Concretely, the evaluation gives a retraction

`R̂ ⊗_R X ⟶ X / Iᵏ X`, `c ⊗ x ↦ (eval c) · x`,

which inverts the unit modulo `Iᵏ`: it sends `1 ⊗ x` to the class of `x`, and it is injective on
the image of the unit because every `c : R̂` differs from a scalar in `R` by an element of `Iᵏ R̂`.

This is the step that lets a comparison between an `R`-module and an `R̂`-module be analysed with
tools that live over a single ring: the comparison factors through the unit, and the rest of it is
a map of `R̂`-modules.

A second, purely bookkeeping, result is also proved here: the level submodules `(m)ᵏ · X` do not
depend on which base ring the natural number `m` is read in, because `(m : R)ᵏ • x` is the
`ℕ`-scalar multiple `m ^ k • x`.  So levelwise bijectivity transfers between the two readings.

## Main results

* `Crystalline.bijective_reduceModIdeal_tensorUnit` — the unit `X ⟶ R̂ ⊗_R X` is bijective modulo
  `Iᵏ`.
* `Crystalline.mem_natCast_pow_smul_top_iff` — the level submodules of a natural number do not
  depend on the base ring.
* `Crystalline.reduceModIdeal_comp` and `Crystalline.bijective_reduceModIdeal_of_linearEquiv` —
  levelwise bijectivity is closed under composition and holds for a linear equivalence.
-/

@[expose] public section

open scoped TensorProduct

namespace Crystalline

universe u v w t

/-! ### Levelwise bijectivity under composition -/

section Comp

variable {S : Type u} [CommRing S] {X : Type v} [AddCommGroup X] [Module S X]
  {Y : Type w} [AddCommGroup Y] [Module S Y]

/-- The reduction modulo an ideal of a composite is the composite of the reductions. -/
theorem reduceModIdeal_comp (K : Ideal S) {Z : Type t} [AddCommGroup Z] [Module S Z]
    (f : X →ₗ[S] Y) (g : Y →ₗ[S] Z) :
    (g ∘ₗ f).reduceModIdeal K = (g.reduceModIdeal K) ∘ₗ (f.reduceModIdeal K) := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (K • (⊤ : Submodule S X)) q
  rw [Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.reduceModIdeal_apply, LinearMap.reduceModIdeal_apply]

/-- The reduction modulo an ideal of the identity is the identity. -/
theorem reduceModIdeal_id (K : Ideal S) :
    (LinearMap.id (R := S) (M := X)).reduceModIdeal K = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (K • (⊤ : Submodule S X)) q
  rw [Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply, LinearMap.id_apply,
    LinearMap.id_apply]

/-- A left inverse on the nose gives a left inverse modulo every ideal. -/
private theorem reduceModIdeal_comp_eq_id (K : Ideal S) {f : X →ₗ[S] Y} {g : Y →ₗ[S] X}
    (h : g ∘ₗ f = LinearMap.id) :
    (g.reduceModIdeal K) ∘ₗ (f.reduceModIdeal K) = LinearMap.id := by
  rw [← reduceModIdeal_comp, h, reduceModIdeal_id]

/-- A linear equivalence is bijective modulo every ideal. -/
theorem bijective_reduceModIdeal_of_linearEquiv (K : Ideal S) (e : X ≃ₗ[S] Y) :
    Function.Bijective (e.toLinearMap.reduceModIdeal K) := by
  have k1 := reduceModIdeal_comp_eq_id K
    (f := e.toLinearMap) (g := e.symm.toLinearMap) (by ext x; simp)
  have k2 := reduceModIdeal_comp_eq_id K
    (f := e.symm.toLinearMap) (g := e.toLinearMap) (by ext x; simp)
  exact ⟨Function.LeftInverse.injective (g := e.symm.toLinearMap.reduceModIdeal K)
      (LinearMap.congr_fun k1),
    Function.RightInverse.surjective (g := e.symm.toLinearMap.reduceModIdeal K)
      (LinearMap.congr_fun k2)⟩

end Comp

/-! ### The level submodules of a natural number -/

section NatCast

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] {X : Type w} [AddCommGroup X]
  [Module R X] [Module S X]

/-- **The level submodule `(m)ᵏ · X` does not depend on the base ring.**  Both are the set of
`m ^ k`-th multiples of elements of `X`, where the multiple is taken in the additive group. -/
theorem mem_natCast_pow_smul_top_iff (m k : ℕ) (x : X) :
    x ∈ (Ideal.span {(m : R)}) ^ k • (⊤ : Submodule R X) ↔
      x ∈ (Ideal.span {(m : S)}) ^ k • (⊤ : Submodule S X) := by
  simp only [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
    ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

end NatCast

/-! ### The unit of the base change to the completion -/

section Unit

variable {R : Type u} [CommRing R] (I : Ideal R) {X : Type v} [AddCommGroup X] [Module R X]

/-- The unit `X ⟶ R̂ ⊗_R X` of the base change to the `I`-adic completion. -/
noncomputable def tensorUnit : X →ₗ[R] AdicCompletion I R ⊗[R] X :=
  TensorProduct.mk R (AdicCompletion I R) X 1

/-- The unit map into the base change on an element. -/
@[simp]
theorem tensorUnit_apply (x : X) :
    tensorUnit I x = (1 : AdicCompletion I R) ⊗ₜ[R] x :=
  rfl

/-- Scalars act on a reduction through the reduced ring. -/
theorem smul_quotient_eq_mk_smul (k : ℕ) (a : R)
    (z : X ⧸ (I ^ k • (⊤ : Submodule R X))) :
    a • z = (Ideal.Quotient.mk (I ^ k) a) • z := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I ^ k • (⊤ : Submodule R X)) z
  rfl

/-- The retraction `R̂ ⊗_R X ⟶ X / Iᵏ X` given by evaluation at level `k` on the first factor. -/
noncomputable def tensorEvalRetraction (k : ℕ) :
    AdicCompletion I R ⊗[R] X →ₗ[R] X ⧸ (I ^ k • (⊤ : Submodule R X)) := by
  classical
  refine TensorProduct.lift (LinearMap.mk₂ R
    (fun (c : AdicCompletion I R) (x : X) ↦
      AdicCompletion.evalₐ I k c • Submodule.Quotient.mk
        (p := (I ^ k • ⊤ : Submodule R X)) x) ?_ ?_ ?_ ?_)
  · intro c c' x
    rw [map_add, add_smul]
  · intro a c x
    rw [map_smul, smul_quotient_eq_mk_smul I k a, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, mul_smul]
  · intro c x x'
    rw [Submodule.Quotient.mk_add, smul_add]
  · intro a c x
    rw [Submodule.Quotient.mk_smul, smul_quotient_eq_mk_smul I k a,
      smul_quotient_eq_mk_smul I k a, smul_comm]

/-- The evaluation retraction on a pure tensor. -/
@[simp]
theorem tensorEvalRetraction_tmul (k : ℕ) (c : AdicCompletion I R) (x : X) :
    tensorEvalRetraction I (X := X) k (c ⊗ₜ[R] x) =
      AdicCompletion.evalₐ I k c • Submodule.Quotient.mk
        (p := (I ^ k • ⊤ : Submodule R X)) x :=
  rfl

/-- Every element of the completion differs from a scalar by an element of the `k`-th level. -/
theorem exists_sub_algebraMap_mem (hI : I.FG) (k : ℕ) (c : AdicCompletion I R) :
    ∃ a : R, c - AdicCompletion.of I R a ∈ I ^ k • (⊤ : Submodule R (AdicCompletion I R)) := by
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective (I ^ k • (⊤ : Submodule R R))
    (AdicCompletion.eval I R k c)
  refine ⟨a, ?_⟩
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub,
    AdicCompletion.eval_of]
  rw [← ha]
  simp

/-- **Extending scalars to the completion is bijective at every level.**  The unit
`X ⟶ R̂ ⊗_R X` is bijective modulo `Iᵏ`. -/
theorem bijective_reduceModIdeal_tensorUnit (hI : I.FG) (k : ℕ) :
    Function.Bijective ((tensorUnit I (X := X)).reduceModIdeal (I ^ k)) := by
  classical
  have hkill : ∀ z : X ⧸ (I ^ k • (⊤ : Submodule R X)),
      z ∈ I ^ k • (⊤ : Submodule R (X ⧸ (I ^ k • (⊤ : Submodule R X)))) → z = 0 := by
    intro z hz
    have htor := Module.isTorsionBySet_quotient_ideal_smul X (I ^ k)
    refine Submodule.smul_induction_on hz (fun r hr y _ ↦ ?_) (fun y y' hy hy' ↦ ?_)
    · exact htor (x := y) (a := ⟨r, hr⟩)
    · rw [hy, hy', add_zero]
  rw [bijective_reduceModIdeal_iff]
  refine ⟨?_, ?_⟩
  · intro t
    induction t with
    | zero => exact ⟨0, by simp⟩
    | add t t' ht ht' =>
      obtain ⟨x, hx⟩ := ht
      obtain ⟨x', hx'⟩ := ht'
      refine ⟨x + x', ?_⟩
      have : t + t' - tensorUnit I (x + x') = (t - tensorUnit I x) + (t' - tensorUnit I x') := by
        rw [map_add]
        abel
      rw [this]
      exact Submodule.add_mem _ hx hx'
    | tmul c x =>
      obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem I hI k c
      refine ⟨a • x, ?_⟩
      have hof : AdicCompletion.of I R a = a • (1 : AdicCompletion I R) := by
        rw [← Algebra.algebraMap_eq_smul_one, AdicCompletion.algebraMap_apply (S := R)]
        simp
      have hcx : c ⊗ₜ[R] x - tensorUnit I (a • x) =
          (c - AdicCompletion.of I R a) ⊗ₜ[R] x := by
        rw [tensorUnit_apply, TensorProduct.sub_tmul, ← TensorProduct.smul_tmul, hof]
      rw [hcx]
      refine Submodule.smul_induction_on ha (fun r hr y _ ↦ ?_) (fun y y' hy hy' ↦ ?_)
      · rw [← TensorProduct.smul_tmul']
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      · rw [TensorProduct.add_tmul]
        exact Submodule.add_mem _ hy hy'
  · intro x hx
    have h0 : tensorEvalRetraction I (X := X) k (tensorUnit I x) = 0 := by
      have hmem := Submodule.mem_map_of_mem
        (f := tensorEvalRetraction I (X := X) k) hx
      rw [Submodule.map_smul''] at hmem
      refine hkill _ ?_
      exact (show I ^ k • Submodule.map (tensorEvalRetraction I (X := X) k) ⊤ ≤
        I ^ k • (⊤ : Submodule R (X ⧸ (I ^ k • (⊤ : Submodule R X)))) from
          smul_mono_right _ le_top) hmem
    rw [tensorUnit_apply, tensorEvalRetraction_tmul, map_one, one_smul] at h0
    exact (Submodule.Quotient.mk_eq_zero _).mp h0

end Unit

end Crystalline

end
