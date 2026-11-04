module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.ZMod

/-!
# Unipotent block representations attached to a sequence of cocycles

Let `ρ₀ : π → GLₙ(𝐅_ℓ)` be a continuous representation of a topological group and let
`c₀, c₁, …` be continuous maps `π → Mₙ(𝐅_ℓ)` with `cₖ(gh) = ρ₀(g) cₖ(h) + cₖ(g) ρ₀(h)`, that is
continuous `1`-cocycles with values in `Mₙ(𝐅_ℓ)` for the action `g · M = ρ₀(g) M ρ₀(g)⁻¹`, written
as `cₖ(g) ρ₀(g)⁻¹`. The power series `b = ∑ₖ cₖ Xᵏ` satisfies the same identity over `𝐅_ℓ⟦X⟧`,
so `g ↦ [[ρ₀ g, b g], [0, ρ₀ g]]` is a continuous representation `π → GL₂ₙ(𝐅_ℓ⟦X⟧)`. If its
image on a set `N` is finite, then two distinct members of the sequence agree on `N`.

## Main definitions

* `Deformation.cocycleSeries` — the power series `∑ₖ cₖ Xᵏ`.
* `Deformation.blockRepresentation` — the block representation.

## Main results

* `Deformation.exists_ne_eqOn_of_finite_image_blockRepresentation` — if the block
  representation has finite image on `N`, two distinct cocycles of the sequence agree on `N`.
-/

@[expose] public noncomputable section

open scoped PowerSeries.WithPiTopology

namespace PowerSeries.WithPiTopology

/-- A map into a power series ring with the coefficientwise topology is continuous as soon as
each of its coefficients is. -/
theorem continuous_of_forall_continuous_coeff {R X : Type*} [Semiring R] [TopologicalSpace R]
    [TopologicalSpace X] {f : X → PowerSeries R}
    (h : ∀ k, Continuous fun x => PowerSeries.coeff k (f x)) : Continuous f := by
  refine continuous_pi fun d => ?_
  have hd : d = Finsupp.single () (d ()) := by ext; simp
  have := h (d ())
  rw [hd]
  exact this

end PowerSeries.WithPiTopology

namespace Deformation

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} {π : Type*} [Group π] [TopologicalSpace π]

/-- A map `c : π → Mₙ(𝐅_ℓ)` with `c(gh) = ρ₀(g) c(h) + c(g) ρ₀(h)`: the upper right corner of a
representation `g ↦ [[ρ₀ g, c g], [0, ρ₀ g]]`. -/
def IsUpperBlockCocycle (ρ₀ : π →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (c : π → Matrix (Fin n) (Fin n) (ZMod ℓ)) : Prop :=
  ∀ g h, c (g * h) = (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) * c h +
    c g * (ρ₀ h : Matrix (Fin n) (Fin n) (ZMod ℓ))

/-- The power series `∑ₖ cₖ(g) Xᵏ` attached to a sequence of cochains. -/
def cocycleSeries (c : ℕ → π → Matrix (Fin n) (Fin n) (ZMod ℓ)) (g : π) :
    Matrix (Fin n) (Fin n) (PowerSeries (ZMod ℓ)) :=
  Matrix.of fun a b => PowerSeries.mk fun k => c k g a b

omit [Fact (Nat.Prime ℓ)] [Group π] [TopologicalSpace π] in
/-- The `k`-th coefficient of the `(a, b)` entry of `cocycleSeries c g` is `c k g a b`. -/
@[simp]
theorem coeff_cocycleSeries (c : ℕ → π → Matrix (Fin n) (Fin n) (ZMod ℓ)) (g : π) (a b : Fin n)
    (k : ℕ) : PowerSeries.coeff k (cocycleSeries c g a b) = c k g a b := by
  simp [cocycleSeries]

/-- The constant matrix `ρ₀ g` over the power series ring. -/
abbrev constMatrix (ρ₀ : π →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)) (g : π) :
    Matrix (Fin n) (Fin n) (PowerSeries (ZMod ℓ)) :=
  (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)).map (PowerSeries.C)

omit [Fact (Nat.Prime ℓ)] [TopologicalSpace π] in
/-- `constMatrix ρ₀` is multiplicative. -/
theorem constMatrix_mul (ρ₀ : π →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)) (g h : π) :
    constMatrix ρ₀ (g * h) = constMatrix ρ₀ g * constMatrix ρ₀ h := by
  simp only [constMatrix, map_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact Matrix.map_mul

omit [Fact (Nat.Prime ℓ)] [TopologicalSpace π] in
/-- `constMatrix ρ₀` sends the identity of `π` to the identity matrix. -/
theorem constMatrix_one (ρ₀ : π →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)) :
    constMatrix ρ₀ 1 = 1 := by
  simp [constMatrix]

omit [Fact (Nat.Prime ℓ)] [TopologicalSpace π] in
/-- If each `c k` is an upper block cocycle for `ρ₀`, then so is the power series
`cocycleSeries c`: `b(gh) = ρ₀(g) b(h) + b(g) ρ₀(h)`. -/
theorem cocycleSeries_mul (ρ₀ : π →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (c : ℕ → π → Matrix (Fin n) (Fin n) (ZMod ℓ)) (hc : ∀ k, IsUpperBlockCocycle ρ₀ (c k))
    (g h : π) :
    cocycleSeries c (g * h) = constMatrix ρ₀ g * cocycleSeries c h +
      cocycleSeries c g * constMatrix ρ₀ h := by
  ext a b k
  rw [Matrix.add_apply, map_add, coeff_cocycleSeries, hc k g h, Matrix.add_apply]
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_C, coeff_cocycleSeries, constMatrix]

/-- The block matrix `[[ρ₀ g, b g], [0, ρ₀ g]]`. -/
def blockMatrix (ρ₀ : π →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (c : ℕ → π → Matrix (Fin n) (Fin n) (ZMod ℓ)) (g : π) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (PowerSeries (ZMod ℓ)) :=
  Matrix.fromBlocks (constMatrix ρ₀ g) (cocycleSeries c g) 0 (constMatrix ρ₀ g)

omit [Fact (Nat.Prime ℓ)] [TopologicalSpace π] in
/-- For a sequence of upper block cocycles, `blockMatrix ρ₀ c` is multiplicative. -/
theorem blockMatrix_mul (ρ₀ : π →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (c : ℕ → π → Matrix (Fin n) (Fin n) (ZMod ℓ)) (hc : ∀ k, IsUpperBlockCocycle ρ₀ (c k))
    (g h : π) :
    blockMatrix ρ₀ c (g * h) = blockMatrix ρ₀ c g * blockMatrix ρ₀ c h := by
  rw [blockMatrix, blockMatrix, blockMatrix, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, constMatrix_mul,
    cocycleSeries_mul ρ₀ c hc]

omit [Fact (Nat.Prime ℓ)] [TopologicalSpace π] in
/-- For a sequence of upper block cocycles, `blockMatrix ρ₀ c` sends the identity of `π` to the
identity matrix. -/
theorem blockMatrix_one (ρ₀ : π →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (c : ℕ → π → Matrix (Fin n) (Fin n) (ZMod ℓ)) (hc : ∀ k, IsUpperBlockCocycle ρ₀ (c k)) :
    blockMatrix ρ₀ c 1 = 1 := by
  have h1 : ∀ k, c k 1 = 0 := fun k => by
    have := hc k 1 1
    simp only [mul_one, map_one, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul] at this
    exact left_eq_add.1 this
  have hb : cocycleSeries c 1 = 0 := by ext a b k; simp [h1]
  rw [blockMatrix, hb, constMatrix_one, Matrix.fromBlocks_one]

/-- The block matrices, as a monoid homomorphism. -/
def blockMatrixHom (ρ₀ : π →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (c : ℕ → π → Matrix (Fin n) (Fin n) (ZMod ℓ)) (hc : ∀ k, IsUpperBlockCocycle ρ₀ (c k)) :
    π →* Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (PowerSeries (ZMod ℓ)) where
  toFun := blockMatrix ρ₀ c
  map_one' := blockMatrix_one ρ₀ c hc
  map_mul' := blockMatrix_mul ρ₀ c hc

/-- The block representation `π → GL₂ₙ(𝐅_ℓ⟦X⟧)`, as a monoid homomorphism. -/
def blockRepresentationHom (ρ₀ : π →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (c : ℕ → π → Matrix (Fin n) (Fin n) (ZMod ℓ)) (hc : ∀ k, IsUpperBlockCocycle ρ₀ (c k)) :
    π →* Matrix.GeneralLinearGroup (Fin (n + n)) (PowerSeries (ZMod ℓ)) :=
  MonoidHom.toHomUnits
    ((Matrix.reindexRingEquiv (PowerSeries (ZMod ℓ)) finSumFinEquiv).toMonoidHom.comp
      (blockMatrixHom ρ₀ c hc))

omit [Fact (Nat.Prime ℓ)] [TopologicalSpace π] in
/-- The underlying matrix of `blockRepresentationHom ρ₀ c hc g` is `blockMatrix ρ₀ c g`, reindexed
along `finSumFinEquiv`. -/
theorem coe_blockRepresentationHom (ρ₀ : π →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (c : ℕ → π → Matrix (Fin n) (Fin n) (ZMod ℓ)) (hc : ∀ k, IsUpperBlockCocycle ρ₀ (c k)) (g : π) :
    (blockRepresentationHom ρ₀ c hc g : Matrix (Fin (n + n)) (Fin (n + n)) _) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (blockMatrix ρ₀ c g) := rfl

omit [Fact (Nat.Prime ℓ)] in
/-- If `ρ₀` and every `c k` are continuous, then `g ↦ blockMatrix ρ₀ c g` is continuous for the
coefficientwise topology on `𝐅_ℓ⟦X⟧`. -/
theorem continuous_blockMatrix (ρ₀ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (c : ℕ → π → Matrix (Fin n) (Fin n) (ZMod ℓ)) (hcont : ∀ k, Continuous (c k)) :
    Continuous (blockMatrix ρ₀.toMonoidHom c) := by
  have hρ : Continuous fun g => (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) :=
    Units.continuous_val.comp ρ₀.continuous_toFun
  have hA : Continuous (constMatrix ρ₀.toMonoidHom) :=
    hρ.matrix_map PowerSeries.WithPiTopology.continuous_C
  have hB : Continuous (cocycleSeries c) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    refine PowerSeries.WithPiTopology.continuous_of_forall_continuous_coeff fun k => ?_
    simp only [coeff_cocycleSeries]
    exact ((continuous_apply b).comp (continuous_apply a)).comp (hcont k)
  exact Continuous.matrix_fromBlocks hA hB continuous_const hA

/-- The block representation `π → GL₂ₙ(𝐅_ℓ⟦X⟧)`, as a continuous homomorphism. -/
def blockRepresentation [IsTopologicalGroup π]
    (ρ₀ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (c : ℕ → π → Matrix (Fin n) (Fin n) (ZMod ℓ))
    (hc : ∀ k, IsUpperBlockCocycle ρ₀.toMonoidHom (c k))
    (hcont : ∀ k, Continuous (c k)) :
    π →ₜ* Matrix.GeneralLinearGroup (Fin (n + n)) (PowerSeries (ZMod ℓ)) :=
  { toMonoidHom := blockRepresentationHom ρ₀.toMonoidHom c hc
    continuous_toFun := by
      have hM : Continuous fun g => Matrix.reindex finSumFinEquiv finSumFinEquiv
          (blockMatrix ρ₀.toMonoidHom c g) :=
        (continuous_blockMatrix ρ₀ c hcont).matrix_reindex _ _
      refine Units.continuous_iff.2 ⟨hM, ?_⟩
      have : (fun g => ((blockRepresentationHom ρ₀.toMonoidHom c hc g)⁻¹ :
          Matrix.GeneralLinearGroup (Fin (n + n)) (PowerSeries (ZMod ℓ))).val) =
          (fun g => Matrix.reindex finSumFinEquiv finSumFinEquiv
            (blockMatrix ρ₀.toMonoidHom c g)) ∘ fun g => g⁻¹ := by
        funext g
        rw [Function.comp_apply, ← coe_blockRepresentationHom, ← map_inv]
      exact this ▸ hM.comp continuous_inv }

/-- The `k`-th coefficient of the upper right block of a block matrix. -/
def blockCoeff (k : ℕ) (X : Matrix (Fin (n + n)) (Fin (n + n)) (PowerSeries (ZMod ℓ))) :
    Matrix (Fin n) (Fin n) (ZMod ℓ) :=
  (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm X).toBlocks₁₂.map (PowerSeries.coeff k)

omit [Fact (Nat.Prime ℓ)] [TopologicalSpace π] in
/-- The `k`-th coefficient of the upper right block of the reindexed `blockMatrix ρ₀ c g` is
`c k g`. -/
theorem blockCoeff_blockMatrix (ρ₀ : π →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (c : ℕ → π → Matrix (Fin n) (Fin n) (ZMod ℓ)) (k : ℕ) (g : π) :
    blockCoeff k (Matrix.reindex finSumFinEquiv finSumFinEquiv (blockMatrix ρ₀ c g)) = c k g := by
  have hY : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      (Matrix.reindex finSumFinEquiv finSumFinEquiv (blockMatrix ρ₀ c g)) = blockMatrix ρ₀ c g := by
    ext i j; simp
  simp only [blockCoeff]
  rw [hY, blockMatrix, Matrix.toBlocks_fromBlocks₁₂]
  ext a b
  simp

/-- **Finite image of the block representation.** If the block representation attached to a
sequence of cocycles has finite image on a set `N`, then two distinct cocycles of the sequence
agree on `N`. -/
theorem exists_ne_eqOn_of_finite_image_blockRepresentation [IsTopologicalGroup π]
    (ρ₀ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (c : ℕ → π → Matrix (Fin n) (Fin n) (ZMod ℓ))
    (hc : ∀ k, IsUpperBlockCocycle ρ₀.toMonoidHom (c k))
    (hcont : ∀ k, Continuous (c k)) (N : Set π)
    (hfin : (blockRepresentation ρ₀ c hc hcont '' N).Finite) :
    ∃ k₁ k₂, k₁ ≠ k₂ ∧ ∀ g ∈ N, c k₁ g = c k₂ g := by
  classical
  set F := blockRepresentation ρ₀ c hc hcont '' N
  have : Finite F := hfin.to_subtype
  let Ψ : ℕ → F → Matrix (Fin n) (Fin n) (ZMod ℓ) := fun k X =>
    blockCoeff k (X.1 : Matrix (Fin (n + n)) (Fin (n + n)) (PowerSeries (ZMod ℓ)))
  obtain ⟨k₁, k₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite Ψ
  refine ⟨k₁, k₂, hne, fun g hg => ?_⟩
  have hk : ∀ k, c k g = Ψ k ⟨_, Set.mem_image_of_mem _ hg⟩ := fun k =>
    (blockCoeff_blockMatrix ρ₀.toMonoidHom c k g).symm
  rw [hk, hk, heq]

end Deformation
