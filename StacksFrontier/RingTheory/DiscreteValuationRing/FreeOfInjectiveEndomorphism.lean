module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Filtration

/-!
# A module over a discrete valuation ring with an injective endomorphism into `𝔪 M` is free

Let `A` be a discrete valuation ring with maximal ideal `𝔪` and let `M` be a finitely generated
`A`-module carrying an injective `A`-linear endomorphism `φ` with `φ(M) ⊆ 𝔪 M`. Then `M` is free.

## Main results

* `IsDiscreteValuationRing.free_of_injective_of_range_le_maximalIdeal_smul`: the statement above.
-/

@[expose] public section

open IsLocalRing

namespace IsDiscreteValuationRing

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]

omit [Module.Finite A M] in
/-- The iterates of an endomorphism landing in `𝔪 M` land in `𝔪ⁿ M`. -/
theorem range_pow_le_pow_smul_top (φ : M →ₗ[A] M)
    (hrange : LinearMap.range φ ≤ maximalIdeal A • ⊤) (n : ℕ) :
    LinearMap.range (φ ^ n) ≤ (maximalIdeal A) ^ n • (⊤ : Submodule A M) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp, pow_succ]
    calc Submodule.map φ (LinearMap.range (φ ^ n))
        ≤ Submodule.map φ ((maximalIdeal A) ^ n • ⊤) := Submodule.map_mono ih
      _ = (maximalIdeal A) ^ n • Submodule.map φ ⊤ := Submodule.map_smul'' _ _ _
      _ ≤ (maximalIdeal A) ^ n • (maximalIdeal A • ⊤) :=
          smul_mono_right _ (by rw [Submodule.map_top]; exact hrange)
      _ = ((maximalIdeal A) ^ n * maximalIdeal A) • ⊤ := (Submodule.mul_smul _ _ _).symm

/-- A finitely generated module over a discrete valuation ring with an injective endomorphism
`φ` such that `φ(M) ⊆ 𝔪 M` is free. -/
theorem free_of_injective_of_range_le_maximalIdeal_smul (φ : M →ₗ[A] M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ ≤ maximalIdeal A • ⊤) :
    Module.Free A M := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible A
  let S : Submodule A M := LinearMap.ker (ϖ • LinearMap.id)
  have hmemS : ∀ m : M, m ∈ S ↔ ϖ • m = 0 := fun m ↦ by simp [S]
  have hφS : ∀ m ∈ S, φ m ∈ S := fun m hm ↦ by
    rw [hmemS] at hm ⊢
    rw [← map_smul, hm, map_zero]
  let ψ : S →ₗ[A] S := φ.restrict hφS
  have hψinj : Function.Injective ψ := fun a b hab ↦
    Subtype.ext (hinj (congrArg Subtype.val hab))
  have htors : Module.IsTorsionBySet A S (maximalIdeal A : Set A) := by
    intro m a
    have ha : (a : A) ∈ Ideal.span {ϖ} := (irreducible_iff_uniformizer ϖ).mp hϖ ▸ a.2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
    apply Subtype.ext
    change a.1 • m.1 = 0
    rw [← hc, mul_smul, (hmemS m.1).mp m.2, smul_zero]
  let : Module (A ⧸ maximalIdeal A) S := htors.module
  have : IsScalarTower A (A ⧸ maximalIdeal A) S := htors.isScalarTower
  have : Module.Finite A S := Module.Finite.of_injective S.subtype S.injective_subtype
  have : Module.Finite (A ⧸ maximalIdeal A) S :=
    Module.Finite.of_restrictScalars_finite A _ _
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  have : IsArtinian (A ⧸ maximalIdeal A) S := isArtinian_of_fg_of_artinian'
  have : IsArtinian A S := isArtinian_of_surjective_algebraMap (R := A ⧸ maximalIdeal A)
    (Ideal.Quotient.mk_surjective (I := maximalIdeal A))
  have hψsurj : Function.Surjective ψ := IsArtinian.surjective_of_injective_endomorphism ψ hψinj
  have hSle : ∀ n : ℕ, S ≤ (maximalIdeal A) ^ n • (⊤ : Submodule A M) := by
    intro n m hm
    have hsurj : Function.Surjective (ψ ^ n) := by
      rw [Module.End.coe_pow]; exact hψsurj.iterate n
    obtain ⟨y, hy⟩ := hsurj ⟨m, hm⟩
    have hval : ∀ (k : ℕ) (z : S), (((ψ ^ k) z : S) : M) = (φ ^ k) (z : M) := by
      intro k
      induction k with
      | zero => intro z; rfl
      | succ k ih =>
        intro z
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
        rfl
    have : m = (φ ^ n) (y : M) := by rw [← hval, hy]
    exact range_pow_le_pow_smul_top φ hrange n ⟨_, this.symm⟩
  have hSbot : S = ⊥ := by
    refine eq_bot_iff.mpr fun m hm ↦ ?_
    have := (Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) (maximalIdeal A)
      (maximalIdeal.isMaximal A).ne_top)
    rw [← this]
    exact Submodule.mem_iInf _ |>.mpr fun n ↦ hSle n hm
  have hpow : ∀ (n : ℕ) (m : M), ϖ ^ n • m = 0 → m = 0 := by
    intro n
    induction n with
    | zero => intro m hm; simpa using hm
    | succ n ih =>
      intro m hm
      refine ih m ?_
      have : ϖ ^ n • m ∈ S := by rwa [hmemS, ← mul_smul, ← pow_succ']
      rwa [hSbot] at this
  have : Module.IsTorsionFree A M := Module.IsTorsionFree.of_smul_eq_zero fun a m ham ↦ by
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      obtain ⟨n, u, hu⟩ := associated_pow_irreducible ha hϖ
      refine hpow n m ?_
      rw [← hu, mul_comm, mul_smul, ham, smul_zero]
  infer_instance

end IsDiscreteValuationRing
