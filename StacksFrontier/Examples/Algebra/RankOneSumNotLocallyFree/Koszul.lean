module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.PicardGroup
public import StacksFrontier.Examples.Algebra.RankOneSumNotLocallyFree.EulerClass

/-!
# The mod-two Euler class of a product of invertible ideals

Let `I 0, I 1, …` be invertible ideals of a commutative ring `B`, let `J j = I 0 ⊔ ⋯ ⊔ I (j - 1)`
and let `Q j = I 0 × ⋯ × I (j - 1)`. For a `ZMod 2`-valued invariant `φ` additive on short exact
sequences of finite modules, and assuming that each multiplication map
`I j ⊗ (B ⧸ J j) → B ⧸ J j` is injective (a Tor-independence condition), we show

  `∑ k, φ (⋀^k (Q j) ⊗ Y) = φ (Y ⊗ (B ⧸ J j))`

for every finite flat module `Y`. With `Y = B` the left side is the mod-two Euler class of `Q j`,
and the right side is the value of `φ` on `B ⧸ J j`. This is the Koszul complex of the sections
`1 ∈ (I i)⁻¹` read in `G₀` modulo two.

## Main results

* `Stacks.Examples.ModTwoInvariant.sum_exteriorPower_idealPi_tensor`: the identity above.
* `Stacks.Examples.ModTwoInvariant.subsingleton_exteriorPower_idealPi`: `⋀^k (Q j) = 0` for
  `j < k`.
-/

@[expose] public section

namespace Stacks.Examples

open Finset TensorProduct LinearMap

universe u

namespace ModTwoInvariant

variable {B : Type u} [CommRing B] (I : ℕ → Ideal B)

/-- `partialSup I j = I 0 ⊔ ⋯ ⊔ I (j - 1)`. -/
def partialSup : ℕ → Ideal B
  | 0 => ⊥
  | j + 1 => partialSup j ⊔ I j

/-- The product `I 0 × ⋯ × I (j - 1)` of the first `j` ideals, as a module. -/
abbrev idealPi (j : ℕ) : Type u := (i : Fin j) → ↥(I i)

/-- The multiplication map `I j ⊗ (B ⧸ partialSup I j) → B ⧸ partialSup I j`. -/
noncomputable def mulMap (j : ℕ) :
    ↥(I j) ⊗[B] (B ⧸ partialSup I j) →ₗ[B] B ⧸ partialSup I j :=
  TensorProduct.lift ((LinearMap.lsmul B (B ⧸ partialSup I j)).comp (I j).subtype)

/-- `I 0 × ⋯ × I j` is `(I 0 × ⋯ × I (j - 1)) × I j`. -/
def idealPiSuccEquiv (j : ℕ) : idealPi I (j + 1) ≃ₗ[B] idealPi I j × ↥(I j) where
  toFun x := (fun i => x i.castSucc, x (Fin.last j))
  invFun p := Fin.snoc (α := fun i : Fin (j + 1) => ↥(I i)) p.1 p.2
  left_inv x := Fin.snoc_init_self (α := fun i : Fin (j + 1) => ↥(I i)) x
  right_inv p := by
    obtain ⟨p₁, p₂⟩ := p
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The sequence `I j ⊗ (B ⧸ J j) → B ⧸ J j → B ⧸ J (j + 1) → 0` is exact. -/
theorem exact_mulMap_factor (j : ℕ) :
    Function.Exact (mulMap I j)
      (Submodule.factor (le_sup_left : partialSup I j ≤ partialSup I j ⊔ I j)) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro x hx
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [LinearMap.mem_ker, Submodule.factor_mk, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨(⟨z, hz⟩ : ↥(I j)) ⊗ₜ Submodule.mkQ (partialSup I j) 1, ?_⟩
    rw [mulMap, TensorProduct.lift.tmul, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.lsmul_apply, ← LinearMap.map_smul, smul_eq_mul, mul_one, map_add]
    have hy0 : Submodule.mkQ (partialSup I j) y = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hy
    rw [hy0, zero_add]
  · rw [LinearMap.range_le_ker_iff]
    apply TensorProduct.ext'
    intro a x
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [LinearMap.comp_apply, mulMap, TensorProduct.lift.tmul, LinearMap.comp_apply,
      Submodule.subtype_apply, LinearMap.lsmul_apply, ← LinearMap.map_smul, Submodule.factor_mk,
      Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mem_sup_right (Ideal.mul_mem_right b (I j) a.2)

variable [∀ i, Module.Invertible B (I i)]

/-- The exterior powers of `I 0 × ⋯ × I (j - 1)` vanish above degree `j`. -/
theorem subsingleton_exteriorPower_idealPi :
    ∀ j k : ℕ, j < k → Subsingleton (⋀[B]^k (idealPi I j)) := by
  intro j
  induction j with
  | zero =>
    intro k hk
    refine exteriorPower.subsingleton_of_span_eq_top_of_card_lt (R := B)
      (fun _ : Fin 0 => (0 : idealPi I 0)) ?_ k ?_
    · refine eq_top_iff.mpr fun x _ => ?_
      rw [Subsingleton.elim x 0]
      exact Submodule.zero_mem _
    · rw [Nat.card_fin]
      exact hk
  | succ j ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k' : ℕ, k = k' + 1 := ⟨k - 1, by omega⟩
    have := ih (k + 1) (by omega)
    have := ih k (by omega)
    exact (exteriorPowerCongr (k + 1) (idealPiSuccEquiv I j) ≪≫ₗ
      exteriorPower.prodEquivOfInvertible (M := idealPi I j) (L := ↥(I j)) k).toEquiv.subsingleton

variable (φ : ModTwoInvariant B)

/-- **The Koszul identity modulo two.** If the multiplication maps
`I j ⊗ (B ⧸ J j) → B ⧸ J j` are injective for `j < m`, then for every `j ≤ m` and every finite
flat module `Y`, `∑_{k ≤ j} φ (⋀^k (I 0 × ⋯ × I (j - 1)) ⊗ Y) = φ (Y ⊗ (B ⧸ J j))`. -/
theorem sum_exteriorPower_idealPi_tensor (m : ℕ)
    (hinj : ∀ j, j < m → Function.Injective (mulMap I j)) :
    ∀ (j : ℕ), j ≤ m → ∀ (Y : Type u) [AddCommGroup Y] [Module B Y] [Module.Finite B Y]
      [Module.Flat B Y], ∑ k ∈ range (j + 1), φ.toFun (⋀[B]^k (idealPi I j) ⊗[B] Y) =
        φ.toFun (Y ⊗[B] (B ⧸ partialSup I j)) := by
  intro j
  induction j with
  | zero =>
    intro _ Y _ _ _ _
    rw [sum_range_one]
    exact φ.congr' (TensorProduct.congr (exteriorPower.zeroEquiv B (idealPi I 0))
        (LinearEquiv.refl B Y) ≪≫ₗ TensorProduct.lid B Y ≪≫ₗ (TensorProduct.rid B Y).symm ≪≫ₗ
      TensorProduct.congr (LinearEquiv.refl B Y)
        (Submodule.quotEquivOfEqBot (partialSup I 0) rfl).symm)
  | succ j ih' =>
    intro hjm Y _ _ _ _
    have ih := ih' (by omega)
    have hsplit : ∀ k : ℕ, φ.toFun (⋀[B]^(k + 1) (idealPi I (j + 1)) ⊗[B] Y) =
        φ.toFun (⋀[B]^(k + 1) (idealPi I j) ⊗[B] Y) +
          φ.toFun (⋀[B]^k (idealPi I j) ⊗[B] (↥(I j) ⊗[B] Y)) := by
      intro k
      rw [φ.congr' (TensorProduct.congr (exteriorPowerCongr (k + 1) (idealPiSuccEquiv I j) ≪≫ₗ
          exteriorPower.prodEquivOfInvertible (M := idealPi I j) (L := ↥(I j)) k)
          (LinearEquiv.refl B Y) ≪≫ₗ TensorProduct.prodLeft B B _ _ Y),
        φ.prod' _ _ inferInstance inferInstance]
      congr 1
      exact φ.congr' (TensorProduct.assoc B _ _ Y)
    have h0 : φ.toFun (⋀[B]^0 (idealPi I (j + 1)) ⊗[B] Y) =
        φ.toFun (⋀[B]^0 (idealPi I j) ⊗[B] Y) :=
      φ.congr' (TensorProduct.congr ((exteriorPower.zeroEquiv B _).trans
        (exteriorPower.zeroEquiv B _).symm) (LinearEquiv.refl B Y))
    have htop : φ.toFun (⋀[B]^(j + 1) (idealPi I j) ⊗[B] Y) = 0 := by
      have := subsingleton_exteriorPower_idealPi I j (j + 1) (by omega)
      exact φ.eq_zero_of_subsingleton _
    have hsumY : ∑ k ∈ range (j + 1), φ.toFun (⋀[B]^(k + 1) (idealPi I j) ⊗[B] Y) +
        φ.toFun (⋀[B]^0 (idealPi I j) ⊗[B] Y) = φ.toFun (Y ⊗[B] (B ⧸ partialSup I j)) := by
      rw [← sum_range_succ' (fun k => φ.toFun (⋀[B]^k (idealPi I j) ⊗[B] Y)) (j + 1),
        sum_range_succ, htop, add_zero]
      exact ih Y
    have hC : φ.toFun ((↥(I j) ⊗[B] Y) ⊗[B] (B ⧸ partialSup I j)) =
        φ.toFun (Y ⊗[B] (↥(I j) ⊗[B] (B ⧸ partialSup I j))) :=
      φ.congr' (TensorProduct.congr (TensorProduct.comm B _ Y) (LinearEquiv.refl B _) ≪≫ₗ
        TensorProduct.assoc B Y _ _)
    have hses : φ.toFun (Y ⊗[B] (B ⧸ partialSup I j)) =
        φ.toFun (Y ⊗[B] (↥(I j) ⊗[B] (B ⧸ partialSup I j))) +
          φ.toFun (Y ⊗[B] (B ⧸ partialSup I (j + 1))) :=
      φ.shortExact' _ _ _ inferInstance inferInstance inferInstance
        ((mulMap I j).lTensor Y)
        ((Submodule.factor (le_sup_left : partialSup I j ≤ partialSup I j ⊔ I j)).lTensor Y)
        (Module.Flat.lTensor_preserves_injective_linearMap _ (hinj j (by omega)))
        (lTensor_exact Y (exact_mulMap_factor I j) (Submodule.factor_surjective _))
        (LinearMap.lTensor_surjective Y (Submodule.factor_surjective _))
    rw [sum_range_succ', h0]
    simp only [hsplit, sum_add_distrib]
    rw [ih (↥(I j) ⊗[B] Y), add_right_comm, hsumY, hC, hses, add_right_comm,
      CharTwo.add_self_eq_zero, zero_add]

end ModTwoInvariant

end Stacks.Examples
