/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Product

/-!
# Powers of a scheme over a base

For a scheme `C` over `S`, the `m`-th fibre power `C^m = C ×_S ⋯ ×_S C` is built recursively in
the cartesian monoidal category `Over S`: `C^0` is the terminal object `S` and
`C^(m+1) = C ⊗ C^m`, so that `(C^(m+1)).left = C ×_S C^m` on the nose: the new coordinate is
the first one, and `C^(m+1)` is the base change of `C` to `C^m`. A morphism `T ⟶ C^m` over `S` is
the same as an `m`-tuple of morphisms `T ⟶ C` (`Stacks.CurvePower.lift`,
`Stacks.CurvePower.lift_coord`, `Stacks.CurvePower.hom_ext`), and every map between powers given
by a reindexing of the coordinates is a `lift` (`Stacks.CurvePower.reindex`).

## Main definitions

* `Stacks.CurvePower.power C m`: the fibre power `C^m` in `Over S`.
* `Stacks.CurvePower.coord C m i`: the `i`-th coordinate `C^m ⟶ C`.
* `Stacks.CurvePower.lift C m x`: the morphism `T ⟶ C^m` with coordinates `x`.
* `Stacks.CurvePower.reindex C σ`: the morphism `C^m ⟶ C^n` with coordinates `c ↦ c_{σ j}`.

## Main results

* `Stacks.CurvePower.lift_coord`, `Stacks.CurvePower.hom_ext`: the universal property.
* `Stacks.CurvePower.isProper_power_hom`: `C^m` is proper over `S` when `C` is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open AlgebraicGeometry

universe u

namespace Stacks.CurvePower

variable {S : Scheme.{u}} (C : Over S)

/-- **The fibre power `C^m` of `C` over `S`**: `C^0 = S` and `C^(m+1) = C ⊗ C^m`. -/
def power : ℕ → Over S
  | 0 => 𝟙_ (Over S)
  | m + 1 => C ⊗ power m

/-- `C^0` is the terminal object `S`. -/
@[simp] theorem power_zero : power C 0 = 𝟙_ (Over S) := rfl

/-- `C^(m+1) = C ⊗ C^m`. -/
@[simp] theorem power_succ (m : ℕ) : power C (m + 1) = C ⊗ power C m := rfl

/-- **The `i`-th coordinate** `C^m ⟶ C`. -/
def coord : (m : ℕ) → Fin m → (power C m ⟶ C)
  | 0, i => i.elim0
  | m + 1, i => Fin.cases (fst C (power C m)) (fun j => snd C (power C m) ≫ coord m j) i

/-- The `0`-th coordinate of `C^(m+1)` is the first projection. -/
@[simp] theorem coord_zero (m : ℕ) : coord C (m + 1) 0 = fst C (power C m) := by
  simp [coord]

/-- The `(j+1)`-th coordinate of `C^(m+1)` is the `j`-th coordinate of the second factor `C^m`. -/
@[simp] theorem coord_succ (m : ℕ) (j : Fin m) :
    coord C (m + 1) j.succ = snd C (power C m) ≫ coord C m j := by
  simp [coord]

variable {C}

/-- **The morphism `T ⟶ C^m` with prescribed coordinates.** -/
def lift {T : Over S} : (m : ℕ) → (Fin m → (T ⟶ C)) → (T ⟶ power C m)
  | 0, _ => toUnit T
  | m + 1, x => CartesianMonoidalCategory.lift (x 0) (lift m fun j => x j.succ)

/-- The first projection of `lift x` is `x 0`. -/
@[simp] theorem lift_succ_fst {T : Over S} (m : ℕ) (x : Fin (m + 1) → (T ⟶ C)) :
    lift (m + 1) x ≫ fst C (power C m) = x 0 := by
  simp [lift]

/-- The second projection of `lift x` is the `lift` of the remaining coordinates. -/
@[simp] theorem lift_succ_snd {T : Over S} (m : ℕ) (x : Fin (m + 1) → (T ⟶ C)) :
    lift (m + 1) x ≫ snd C (power C m) = lift m fun j => x j.succ := by
  simp [lift]

/-- The coordinates of `lift x` are `x`. -/
@[reassoc (attr := simp)]
theorem lift_coord {T : Over S} : (m : ℕ) → (x : Fin m → (T ⟶ C)) → (i : Fin m) →
    lift m x ≫ coord C m i = x i
  | 0, _, i => i.elim0
  | m + 1, x, i => by
    induction i using Fin.cases with
    | zero => rw [coord_zero, lift_succ_fst]
    | succ j =>
      rw [coord_succ]
      refine (Category.assoc (lift (m + 1) x) (snd C (power C m)) (coord C m j)).symm.trans ?_
      rw [lift_succ_snd]
      exact lift_coord m (fun j => x j.succ) j

/-- **Morphisms into `C^m` are determined by their coordinates.** -/
theorem hom_ext {T : Over S} : (m : ℕ) → {a b : T ⟶ power C m} →
    (∀ i, a ≫ coord C m i = b ≫ coord C m i) → a = b
  | 0, a, b, _ => toUnit_unique a b
  | m + 1, a, b, h => by
    apply CartesianMonoidalCategory.hom_ext
    · have := h 0
      rw [coord_zero] at this
      exact this
    · exact hom_ext m fun j => by
        have := h j.succ
        rw [coord_succ] at this
        exact (Category.assoc _ _ _).trans (this.trans (Category.assoc _ _ _).symm)

/-- Every morphism into `C^m` is the `lift` of its coordinates. -/
theorem eq_lift {T : Over S} (m : ℕ) (a : T ⟶ power C m) :
    a = lift m fun i => a ≫ coord C m i :=
  hom_ext m fun i => by rw [lift_coord]

/-- Precomposing `lift x` with `g` is the `lift` of the precomposed coordinates. -/
@[reassoc]
theorem comp_lift {T T' : Over S} (g : T' ⟶ T) (m : ℕ) (x : Fin m → (T ⟶ C)) :
    g ≫ lift m x = lift m fun i => g ≫ x i :=
  hom_ext m fun i => by simp

variable (C) in
/-- **Reindexing**: the morphism `C^m ⟶ C^n`, `(c_i)_i ↦ (c_{σ j})_j`, for `σ : Fin n → Fin m`. -/
def reindex {m n : ℕ} (σ : Fin n → Fin m) : power C m ⟶ power C n :=
  lift n fun j => coord C m (σ j)

/-- The `j`-th coordinate of `reindex C σ` is the `σ j`-th coordinate. -/
@[reassoc (attr := simp)]
theorem reindex_coord {m n : ℕ} (σ : Fin n → Fin m) (j : Fin n) :
    reindex C σ ≫ coord C n j = coord C m (σ j) := by
  simp [reindex]

/-- Reindexing `lift x` along `σ` is `lift (x ∘ σ)`. -/
@[reassoc (attr := simp)]
theorem lift_reindex {T : Over S} {m n : ℕ} (x : Fin m → (T ⟶ C)) (σ : Fin n → Fin m) :
    lift m x ≫ reindex C σ = lift n (x ∘ σ) :=
  hom_ext n fun j => by simp

/-- Reindexing along the identity is the identity. -/
theorem reindex_id (m : ℕ) : reindex C (id : Fin m → Fin m) = 𝟙 _ :=
  hom_ext m fun j => by simp

/-- Reindexing along `σ` and then `τ` is reindexing along `σ ∘ τ`. -/
theorem reindex_comp {m n p : ℕ} (σ : Fin n → Fin m) (τ : Fin p → Fin n) :
    reindex C σ ≫ reindex C τ = reindex C (σ ∘ τ) :=
  hom_ext p fun j => by simp

/-! ### Properness -/

/-- **`C^m` is proper over `S` when `C` is.** -/
instance isProper_power_hom [IsProper C.hom] : (m : ℕ) → IsProper (power C m).hom
  | 0 => by
    change IsProper (𝟙 S)
    infer_instance
  | m + 1 => by
    have := isProper_power_hom m
    change IsProper (pullback.fst C.hom (power C m).hom ≫ C.hom)
    infer_instance

/-! ### Powers of a variety over an algebraically closed field -/

section Variety

variable {k : Type u} [Field k] [IsAlgClosed k] (C : Over (Spec (.of k))) [IsVariety k C.hom]

/-- **The powers of a variety over an algebraically closed field are varieties**, of dimension
`m · dim C` ([Stacks, Tag 0AZM]). -/
theorem isVariety_power_and_topologicalKrullDim : (m : ℕ) →
    IsVariety k (power C m).hom ∧
      topologicalKrullDim (power C m).left = m * topologicalKrullDim C.left
  | 0 => by
    refine ⟨?_, ?_⟩
    · change IsVariety k (𝟙 (Spec (.of k)))
      constructor
    · change topologicalKrullDim (PrimeSpectrum k) = _
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
      simp
  | m + 1 => by
    obtain ⟨hv, hd⟩ := isVariety_power_and_topologicalKrullDim m
    obtain ⟨hv', hd'⟩ := isVariety_and_topologicalKrullDim_pullback k C.hom (power C m).hom
    refine ⟨hv', ?_⟩
    change topologicalKrullDim ↑(Limits.pullback C.hom (power C m).hom) = _
    rw [hd', hd]
    push_cast
    rw [add_mul, one_mul, add_comm]

/-- The powers of a variety over an algebraically closed field are varieties. -/
instance isVariety_power (m : ℕ) : IsVariety k (power C m).hom :=
  (isVariety_power_and_topologicalKrullDim C m).1

end Variety

end Stacks.CurvePower
