module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ContinuousModuleScalarAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules

/-!
# The finite levels of a continuous `ℤ_ℓ`-representation

Let `ρ : G → GL_r(ℤ_ℓ)` be a continuous representation of a topological group.  Reducing the
entries of `ρ` modulo `ℓ ^ k` gives a representation of `G` on `(ℤ/ℓ^kℤ)^r` which is continuous
for the discrete topology on `(ℤ/ℓ^kℤ)^r`: the stabiliser of a vector contains the preimage of
an open subgroup of `GL_r(ℤ_ℓ)`.  These are the finite continuous `π₁(X, x̄)`-modules whose
locally constant sheaves are the levels of the lisse sheaf `ℱ_ρ` of the notation preceding
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); reduction from `ℓ ^ (k + 1)` to `ℓ ^ k`
is `G`-equivariant and is the transition map of that system.

## Main definitions

* `Stacks.EtaleCohomology.levelRepresentation`: the representation of `G` on `(ℤ/ℓ^kℤ)^r`
  obtained by reducing `ρ` modulo `ℓ ^ k`.
* `Stacks.EtaleCohomology.levelModule`: the finite `ℤ/ℓ^kℤ`-module with continuous `G`-action
  it defines, as an object of `Stacks.GroupCohomology.FiniteTypeContinuousModule`.
* `Stacks.EtaleCohomology.levelReduction`: reduction `(ℤ/ℓ^{k+1}ℤ)^r → (ℤ/ℓ^kℤ)^r`, a
  `G`-equivariant map.

## Main results

* `Stacks.EtaleCohomology.isOpen_setOf_levelRepresentation_apply_eq`: the stabilisers of the
  level representation are open, i.e. the action is continuous on the discrete module.
* `Stacks.EtaleCohomology.levelReduction_levelRepresentation`: reduction is equivariant.
* `Stacks.EtaleCohomology.levelReduction_surjective` and
  `Stacks.EtaleCohomology.levelReduction_eq_zero_iff`: reduction is surjective with kernel
  `ℓ ^ k (ℤ/ℓ^{k+1}ℤ)^r`.
-/

@[expose] public noncomputable section

open CategoryTheory Matrix

universe v w

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}

/-! ### Reduction of `ℓ`-adic integers modulo powers of `ℓ` is locally constant -/

/-- Two `ℓ`-adic integers have the same reduction modulo `ℓ ^ k` exactly when they are at
distance at most `ℓ ^ (-k)`. -/
public theorem toZModPow_eq_iff_norm_sub_le (k : ℕ) (x y : ℤ_[ℓ]) :
    PadicInt.toZModPow k x = PadicInt.toZModPow k y ↔ ‖x - y‖ ≤ (ℓ : ℝ) ^ (-(k : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    sub_eq_zero]

/-- The fibres of reduction modulo `ℓ ^ k` are open in `ℤ_ℓ`. -/
public theorem isOpen_setOf_toZModPow_eq (k : ℕ) (a : ZMod (ℓ ^ k)) :
    IsOpen {x : ℤ_[ℓ] | PadicInt.toZModPow k x = a} := by
  rw [Metric.isOpen_iff]
  intro x hx
  refine ⟨(ℓ : ℝ) ^ (-(k : ℤ)), zpow_pos (by exact_mod_cast (Fact.out : ℓ.Prime).pos) _,
    fun y hy => ?_⟩
  show PadicInt.toZModPow k y = a
  rw [← (show PadicInt.toZModPow k x = a from hx), toZModPow_eq_iff_norm_sub_le]
  rw [Metric.mem_ball, dist_eq_norm] at hy
  exact hy.le

/-! ### The level representations -/

variable {G : Type v} [Group G] [TopologicalSpace G] (ρ : G →* GL (Fin r) ℤ_[ℓ])

/-- The reduction of `ρ` modulo `ℓ ^ k`, as a representation into `GL_r(ℤ/ℓ^kℤ)`. -/
public abbrev levelMatrixRepresentation (k : ℕ) : G →* GL (Fin r) (ZMod (ℓ ^ k)) :=
  (GeneralLinearGroup.map (PadicInt.toZModPow k)).comp ρ

/-- **The level representation**: `G` acting on `(ℤ/ℓ^kℤ)^r` through the reduction of `ρ`
modulo `ℓ ^ k`. -/
public def levelRepresentation (k : ℕ) :
    Representation (ZMod (ℓ ^ k)) G (Fin r → ZMod (ℓ ^ k)) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) (ZMod (ℓ ^ k)) ≃ₐ[ZMod (ℓ ^ k)]
      Module.End (ZMod (ℓ ^ k)) (Fin r → ZMod (ℓ ^ k))).toMonoidHom.comp
    ((Units.coeHom _).comp (levelMatrixRepresentation ρ k))

/-- The level representation acts by the reduced matrices. -/
public theorem levelRepresentation_apply (k : ℕ) (g : G) (x : Fin r → ZMod (ℓ ^ k)) :
    levelRepresentation ρ k g x =
      ((ρ g).val.map (PadicInt.toZModPow k)) *ᵥ x :=
  rfl

/-- The reduced matrix of `ρ g` is a locally constant function of `g`. -/
public theorem isOpen_setOf_map_toZModPow_eq (hρ : Continuous ρ) (k : ℕ)
    (A : Matrix (Fin r) (Fin r) (ZMod (ℓ ^ k))) :
    IsOpen {g : G | (ρ g).val.map (PadicInt.toZModPow k) = A} := by
  have : {g : G | (ρ g).val.map (PadicInt.toZModPow k) = A} =
      ⋂ i, ⋂ j, (fun g => (ρ g).val i j) ⁻¹' {x | PadicInt.toZModPow k x = A i j} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h i j => congrFun (congrFun h i) j, fun h => Matrix.ext h⟩
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_setOf_toZModPow_eq k (A i j)).preimage
      ((Units.continuous_val.comp hρ).matrix_elem i j)

/-- **The level representation is continuous**: the stabiliser of every vector is open. -/
public theorem isOpen_setOf_levelRepresentation_apply_eq (hρ : Continuous ρ) (k : ℕ)
    (x : Fin r → ZMod (ℓ ^ k)) : IsOpen {g : G | levelRepresentation ρ k g x = x} := by
  have : {g : G | levelRepresentation ρ k g x = x} =
      ⋃ A ∈ {A : Matrix (Fin r) (Fin r) (ZMod (ℓ ^ k)) | A *ᵥ x = x},
        {g : G | (ρ g).val.map (PadicInt.toZModPow k) = A} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, levelRepresentation_apply, exists_prop]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨A, hA, hg⟩ => hg ▸ hA⟩
  rw [this]
  exact isOpen_biUnion fun A _ => isOpen_setOf_map_toZModPow_eq ρ hρ k A

/-! ### Reduction between consecutive levels -/

/-- Reduction `ℤ/ℓ^{k+1}ℤ → ℤ/ℓ^kℤ`. -/
public abbrev levelRingHom (k : ℕ) : ZMod (ℓ ^ (k + 1)) →+* ZMod (ℓ ^ k) :=
  ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ k)) _

/-- Reduction of `ℓ`-adic integers modulo `ℓ ^ (k + 1)` and then modulo `ℓ ^ k` is reduction
modulo `ℓ ^ k`. -/
public theorem levelRingHom_toZModPow (k : ℕ) (x : ℤ_[ℓ]) :
    levelRingHom k (PadicInt.toZModPow (k + 1) x) = PadicInt.toZModPow k x :=
  PadicInt.cast_toZModPow k (k + 1) (Nat.le_succ k) x

/-- **Reduction** `(ℤ/ℓ^{k+1}ℤ)^r → (ℤ/ℓ^kℤ)^r`, coordinatewise. -/
public def levelReduction (k : ℕ) :
    (Fin r → ZMod (ℓ ^ (k + 1))) →+ (Fin r → ZMod (ℓ ^ k)) :=
  (levelRingHom k).toAddMonoidHom.compLeft (Fin r)

/-- The `i`-th coordinate of the reduction of `x` is the reduction of the `i`-th coordinate of
`x`. -/
@[simp]
public theorem levelReduction_apply (k : ℕ) (x : Fin r → ZMod (ℓ ^ (k + 1))) (i : Fin r) :
    levelReduction k x i = levelRingHom k (x i) :=
  rfl

/-- Reduction is semilinear along `ℤ/ℓ^{k+1}ℤ → ℤ/ℓ^kℤ`. -/
public theorem levelReduction_smul (k : ℕ) (a : ZMod (ℓ ^ (k + 1)))
    (x : Fin r → ZMod (ℓ ^ (k + 1))) :
    levelReduction k (a • x) = levelRingHom k a • levelReduction k x := by
  ext i
  simp only [levelReduction_apply, Pi.smul_apply, smul_eq_mul, map_mul]

/-- **Reduction is `G`-equivariant.** -/
public theorem levelReduction_levelRepresentation (k : ℕ) (g : G)
    (x : Fin r → ZMod (ℓ ^ (k + 1))) :
    levelReduction k (levelRepresentation ρ (k + 1) g x) =
      levelRepresentation ρ k g (levelReduction k x) := by
  ext i
  simp only [levelReduction_apply, levelRepresentation_apply, Matrix.mulVec, dotProduct,
    map_sum, map_mul, Matrix.map_apply, levelRingHom_toZModPow]

/-- Reduction is surjective. -/
public theorem levelReduction_surjective (k : ℕ) :
    Function.Surjective (levelReduction (ℓ := ℓ) (r := r) k) := by
  intro y
  refine ⟨fun i => ((y i).val : ZMod (ℓ ^ (k + 1))), funext fun i => ?_⟩
  rw [levelReduction_apply, map_natCast, ZMod.natCast_zmod_val]

/-- The kernel of reduction is `ℓ ^ k (ℤ/ℓ^{k+1}ℤ)^r`. -/
public theorem levelReduction_eq_zero_iff (k : ℕ) (x : Fin r → ZMod (ℓ ^ (k + 1))) :
    levelReduction k x = 0 ↔ ∃ y : Fin r → ZMod (ℓ ^ (k + 1)), x = (ℓ ^ k : ℕ) • y := by
  constructor
  · intro h
    have hi : ∀ i, ∃ c : ZMod (ℓ ^ (k + 1)), x i = (ℓ ^ k : ℕ) • c := by
      intro i
      have h0 : levelRingHom k (x i) = 0 := congrFun h i
      rw [← ZMod.natCast_zmod_val (x i), map_natCast, ZMod.natCast_eq_zero_iff] at h0
      obtain ⟨c, hc⟩ := h0
      exact ⟨c, by rw [nsmul_eq_mul, ← Nat.cast_mul, ← hc, ZMod.natCast_zmod_val]⟩
    choose c hc using hi
    exact ⟨c, funext hc⟩
  · rintro ⟨y, rfl⟩
    ext i
    rw [levelReduction_apply, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast,
      ZMod.natCast_self, zero_mul, Pi.zero_apply]

/-! ### The level modules as finite continuous `G`-modules -/

section Modules

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

open Stacks.GroupCohomology

variable [IsTopologicalGroup G]

/-- The identification of `(ℤ/ℓ^kℤ)^r` with its lift to the universe `w`. -/
public abbrev levelULiftEquiv (k : ℕ) :
    ULift.{w} (Fin r → ZMod (ℓ ^ k)) ≃ₗ[ZMod (ℓ ^ k)] (Fin r → ZMod (ℓ ^ k)) :=
  ULift.moduleEquiv

/-- The level representation on `(ℤ/ℓ^kℤ)^r`, transported to a carrier in the universe `w`. -/
public def levelULiftRepresentation (k : ℕ) :
    Representation (ZMod (ℓ ^ k)) G (ULift.{w} (Fin r → ZMod (ℓ ^ k))) :=
  { toFun := fun g => (levelULiftEquiv.{w} (ℓ := ℓ) (r := r) k).symm.toLinearMap ∘ₗ
      levelRepresentation ρ k g ∘ₗ (levelULiftEquiv.{w} k).toLinearMap
    map_one' := by
      ext x : 1
      exact ULift.ext (by simp)
    map_mul' := fun g h => by
      ext x : 1
      exact ULift.ext (by simp [Module.End.mul_apply]) }

/-- On underlying vectors, the lifted level representation acts as the level representation. -/
@[simp]
public theorem levelULiftRepresentation_apply_down (k : ℕ) (g : G)
    (x : ULift.{w} (Fin r → ZMod (ℓ ^ k))) :
    (levelULiftRepresentation.{v, w} ρ k g x).down = levelRepresentation ρ k g x.down :=
  rfl

/-- The action of `G` on the discrete module `(ℤ/ℓ^kℤ)^r` is continuous. -/
public theorem isContinuous_levelULiftRepresentation (hρ : Continuous ρ) (k : ℕ) :
    (actionOfRepresentation (ZMod (ℓ ^ k)) G _
      (levelULiftRepresentation.{v, w} ρ k)).IsContinuous :=
  (isContinuous_actionOfRepresentation_iff _).2 fun x => by
    have : {g : G | levelULiftRepresentation.{v, w} ρ k g x = x} =
        {g : G | levelRepresentation ρ k g x.down = x.down} := by
      ext g
      exact ⟨fun h => congrArg ULift.down h, fun h => ULift.ext h⟩
    rw [this]
    exact isOpen_setOf_levelRepresentation_apply_eq ρ hρ k x.down

/-- **The level module**: `(ℤ/ℓ^kℤ)^r` with the continuous action of `G` through the reduction
of `ρ` modulo `ℓ ^ k`, a finite `ℤ/ℓ^kℤ`-module with continuous `G`-action. -/
public def levelModule (hρ : Continuous ρ) (k : ℕ) :
    FiniteTypeContinuousModule.{0, v, w} (ZMod (ℓ ^ k)) G :=
  ⟨ofRepresentation (levelULiftRepresentation.{v, w} ρ k)
      (isContinuous_levelULiftRepresentation ρ hρ k),
    (ModuleCat.isFG_iff _).2 (Module.Finite.equiv (levelULiftEquiv.{w} (ℓ := ℓ) (r := r) k).symm)⟩

end Modules

end Stacks.EtaleCohomology

end
