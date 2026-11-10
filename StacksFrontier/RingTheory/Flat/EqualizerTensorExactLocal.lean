module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import StacksFrontier.RingTheory.Flat.EqualizerTensorExact

/-!
# The equalizer sequence over local rings

Let `A` be a ring, `p₁ p₂ : C → D` two maps of flat `A`-algebras, and let `A'` be a local
`A`-algebra with residue field `κ`. Suppose the equalizer sequence
`0 → κ → κ ⊗_A C → κ ⊗_A D` of `AlgHom.EqualizerTensorExact` is exact. This file shows:

* the sequence is then exact for every `A'`-module killed by a power of the maximal ideal
  (`AlgHom.EqualizerTensorExact.of_smul_eq_bot`), in particular for the Artinian quotients
  `A' ⧸ 𝔪ⁿ` (`AlgHom.EqualizerTensorExact.quotient_pow`).

For the chart algebras of an algebraic space `X` flat over `Spec A` the hypothesis is
`κ = H⁰(X_κ, 𝒪)`, and the conclusion says that `H⁰(X_{A'}, 𝒪) = A'` for every such `A'`.
-/

@[expose] public section

open TensorProduct IsLocalRing

namespace AlgHom

variable {A C D : Type*} [CommRing A] [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
  {p₁ p₂ : C →ₐ[A] D}

/-- The zero module satisfies the property. -/
theorem EqualizerTensorExact.of_subsingleton {N : Type*} [AddCommGroup N] [Module A N]
    [Subsingleton N] : EqualizerTensorExact p₁ p₂ N :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩,
    fun _ => Subsingleton.elim _ _⟩⟩

section Local

variable {A' : Type*} [CommRing A'] [IsLocalRing A'] [Algebra A A']

/-- An ideal `I` satisfies `I • ⊤ = ⊥` iff it kills every element of the module. -/
private theorem smul_top_eq_bot_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} : I • (⊤ : Submodule R M) = ⊥ ↔ ∀ r ∈ I, ∀ x : M, r • x = 0 := by
  rw [eq_bot_iff, Submodule.smul_le]
  simp only [Submodule.mem_top, forall_const, Submodule.mem_bot]

/-- A module killed by the maximal ideal of a local `A`-algebra `A'` satisfies the property as
soon as the residue field does. -/
theorem EqualizerTensorExact.of_smul_maximalIdeal_eq_bot {M : Type*} [AddCommGroup M]
    [Module A' M] [Module A M] [IsScalarTower A A' M]
    (hM : (maximalIdeal A') • (⊤ : Submodule A' M) = ⊥)
    (h : EqualizerTensorExact p₁ p₂ (ResidueField A')) : EqualizerTensorExact p₁ p₂ M := by
  have ht : Module.IsTorsionBySet A' M (maximalIdeal A') := fun m ⟨a, ha⟩ =>
    smul_top_eq_bot_iff.mp hM a ha m
  let : Module (ResidueField A') M := ht.module
  have : IsScalarTower A (ResidueField A') M := by
    refine ⟨fun a x m => ?_⟩
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    have e : a • residue A' y = residue A' (algebraMap A A' a * y) := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A A' (ResidueField A'),
        IsLocalRing.ResidueField.algebraMap_eq, ← map_mul]
    rw [e]
    change (algebraMap A A' a * y) • m = a • (y • m)
    rw [← smul_eq_mul, smul_assoc, algebraMap_smul]
  have : Module.Free (ResidueField A') M := Module.Free.of_divisionRing _ _
  exact h.of_flat

variable [Module.Flat A C] [Module.Flat A D]

/-- **Artinian thickenings.** If the residue field of a local `A`-algebra `A'` satisfies the
property, so does every `A'`-module killed by a power of the maximal ideal. -/
theorem EqualizerTensorExact.of_smul_eq_bot (h : EqualizerTensorExact p₁ p₂ (ResidueField A'))
    (n : ℕ) : ∀ (M : Type*) [AddCommGroup M] [Module A' M] [Module A M] [IsScalarTower A A' M],
      (maximalIdeal A') ^ n • (⊤ : Submodule A' M) = ⊥ → EqualizerTensorExact p₁ p₂ M := by
  induction n with
  | zero =>
    intro M _ _ _ _ hM
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hM
    have : Subsingleton M := subsingleton_of_forall_eq 0 fun m =>
      (Submodule.mem_bot A').mp (hM ▸ Submodule.mem_top)
    exact EqualizerTensorExact.of_subsingleton
  | succ n ih =>
    intro M _ _ _ _ hM
    set N : Submodule A' M := (maximalIdeal A') • ⊤
    have hN : (maximalIdeal A') ^ n • (⊤ : Submodule A' N) = ⊥ := by
      rw [smul_top_eq_bot_iff]
      intro r hr x
      apply Subtype.ext
      have : r • (x : M) ∈ ((maximalIdeal A') ^ n * maximalIdeal A') • (⊤ : Submodule A' M) := by
        rw [Submodule.mul_smul]
        exact Submodule.smul_mem_smul hr x.2
      rw [← pow_succ, hM, Submodule.mem_bot] at this
      exact this
    have hQ : (maximalIdeal A') • (⊤ : Submodule A' (M ⧸ N)) = ⊥ := by
      rw [smul_top_eq_bot_iff]
      intro r hr x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N x
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    exact EqualizerTensorExact.of_exact (f := (N.subtype.restrictScalars A))
      (g := (N.mkQ.restrictScalars A)) Subtype.val_injective
      (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)
      (ih N hN) (EqualizerTensorExact.of_smul_maximalIdeal_eq_bot hQ h)

/-- The quotient `A' ⧸ 𝔪ⁿ` is killed by `𝔪ⁿ`. -/
theorem maximalIdeal_pow_smul_top_quotient (n : ℕ) :
    (maximalIdeal A') ^ n • (⊤ : Submodule A' (A' ⧸ (maximalIdeal A') ^ n)) = ⊥ := by
  rw [smul_top_eq_bot_iff]
  intro r hr x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ hr

/-- The sequence is exact for every quotient `A' ⧸ 𝔪ⁿ` of a local `A`-algebra `A'` as soon as it
is exact for the residue field. -/
theorem EqualizerTensorExact.quotient_pow (h : EqualizerTensorExact p₁ p₂ (ResidueField A'))
    (n : ℕ) : EqualizerTensorExact p₁ p₂ (A' ⧸ (maximalIdeal A') ^ n) :=
  h.of_smul_eq_bot n _ (maximalIdeal_pow_smul_top_quotient n)

omit [Module.Flat A C] in
/-- A section vanishing on every `A' ⧸ 𝔪ⁿ ⊗_A C` lies in every power of the extension of the
maximal ideal to `A' ⊗_A C`. -/
theorem mem_map_pow_of_rTensor_eq_zero (n : ℕ) {y : A' ⊗[A] C}
    (hy : (Ideal.Quotient.mkₐ A ((maximalIdeal A') ^ n)).toLinearMap.rTensor C y = 0) :
    y ∈ ((maximalIdeal A').map (algebraMap A' (A' ⊗[A] C))) ^ n := by
  set I := (maximalIdeal A') ^ n
  have hex : Function.Exact ((I.restrictScalars A).subtype.rTensor C)
      ((Ideal.Quotient.mkₐ A I).toLinearMap.rTensor C) := by
    refine rTensor_exact C ?_ (Ideal.Quotient.mkₐ_surjective A I)
    intro x
    simp [Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨z, rfl⟩ := (hex y).mp hy
  clear hy
  rw [← Ideal.map_pow]
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => rw [map_add]; exact Ideal.add_mem _ hz hw
  | tmul i c =>
    have : ((I.restrictScalars A).subtype.rTensor C) (i ⊗ₜ c) =
        algebraMap A' (A' ⊗[A] C) (i : A') * ((1 : A') ⊗ₜ c) := by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ i.2)

end Local

end AlgHom
