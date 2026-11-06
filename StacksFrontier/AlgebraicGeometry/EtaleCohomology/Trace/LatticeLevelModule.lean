module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GroupRingSheafClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LatticeModuleConstituents
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationLevels

/-!
# The level modules of a representation are the reductions of its lattice

Let `ρ : G → GL_r(ℤ_ℓ)`. Reduction modulo `ℓᵏ` of the coordinates identifies the quotient
`L / ℓᵏ L` of the lattice `L = ℤ_ℓ^r` of `ρ` (`Stacks.EtaleCohomology.LatticeModule`) with
`(ℤ/ℓᵏ)^r`, `G`-equivariantly (`Stacks.EtaleCohomology.latticeLevelEquiv`): the kernel of
`ℤ_ℓ → ℤ/ℓᵏ` is `ℓᵏ ℤ_ℓ`. For `ρ` continuous this identifies the level module of `ρ`
(`Stacks.EtaleCohomology.levelModule`) with the continuous module of the finite `ℤ[G]`-module
`L / ℓᵏ L` (`Stacks.EtaleCohomology.levelModuleLatticeIso`). So the levels of the sheaf of an
integral representation are the sheaves of the reductions of its lattice.

## Main definitions

* `Stacks.EtaleCohomology.latticeLevelMap`, `Stacks.EtaleCohomology.latticeLevelEquiv`.
* `Stacks.EtaleCohomology.levelModuleLatticeIso`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidAlgebra Stacks.GroupCohomology

universe v w

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ} {G : Type v} [Group G] [TopologicalSpace G]
  (ρ : G →* GL (Fin r) ℤ_[ℓ])

/-- `ℓᵏ L` for the lattice `L` of `ρ`. -/
abbrev latticeLevelSubmodule (k : ℕ) : Submodule (MonoidAlgebra ℤ G) (LatticeModule ρ) :=
  powSMulRange (MonoidAlgebra ℤ G) ℓ (LatticeModule ρ) k

/-- **Reduction of the lattice of `ρ` modulo `ℓᵏ`**, coordinatewise. -/
def latticeLevelMap (k : ℕ) : LatticeModule ρ →+ (Fin r → ZMod (ℓ ^ k)) :=
  ((PadicInt.toZModPow k).toAddMonoidHom.compLeft (Fin r)).comp
    (latticeModuleEquiv ρ).toLinearMap.toAddMonoidHom

omit [TopologicalSpace G] in
/-- The `i`-th coordinate of the reduction of `v` is the reduction of the `i`-th coordinate of
`v`. -/
theorem latticeLevelMap_apply (k : ℕ) (v : LatticeModule ρ) (i : Fin r) :
    latticeLevelMap ρ k v i = PadicInt.toZModPow k (latticeModuleEquiv ρ v i) :=
  rfl

/-- **Reduction is `G`-equivariant.** -/
theorem latticeLevelMap_of_smul (k : ℕ) (g : G) (v : LatticeModule ρ) :
    latticeLevelMap ρ k (of ℤ G g • v) = levelRepresentation ρ k g (latticeLevelMap ρ k v) := by
  funext i
  rw [latticeLevelMap_apply, latticeModule_of_smul, levelRepresentation_apply,
    RingHom.map_mulVec]
  rfl

omit [TopologicalSpace G] in
/-- Reduction of the lattice of `ρ` modulo `ℓᵏ` is surjective. -/
theorem latticeLevelMap_surjective (k : ℕ) : Function.Surjective (latticeLevelMap ρ k) := by
  intro w
  choose y hy using fun i => ZMod.ringHom_surjective (PadicInt.toZModPow (p := ℓ) k) (w i)
  refine ⟨(latticeModuleEquiv ρ).symm y, funext fun i => ?_⟩
  rw [latticeLevelMap_apply, LinearEquiv.apply_symm_apply, hy]

omit [TopologicalSpace G] in
/-- **The kernel of reduction is `ℓᵏ L`.** -/
theorem latticeLevelMap_eq_zero_iff (k : ℕ) (v : LatticeModule ρ) :
    latticeLevelMap ρ k v = 0 ↔ v ∈ latticeLevelSubmodule ρ k := by
  rw [mem_powSMulRange]
  constructor
  · intro h
    have hi : ∀ i, ∃ y : ℤ_[ℓ], y * (ℓ : ℤ_[ℓ]) ^ k = latticeModuleEquiv ρ v i := fun i => by
      have h' : latticeModuleEquiv ρ v i ∈ RingHom.ker (PadicInt.toZModPow (p := ℓ) k) := by
        rw [RingHom.mem_ker, ← latticeLevelMap_apply, h, Pi.zero_apply]
      rw [PadicInt.ker_toZModPow] at h'
      exact Ideal.mem_span_singleton'.1 h'
    choose y hy using hi
    refine ⟨(latticeModuleEquiv ρ).symm y, (latticeModuleEquiv ρ).injective ?_⟩
    rw [map_nsmul, LinearEquiv.apply_symm_apply]
    funext i
    rw [Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, mul_comm, hy]
  · rintro ⟨y, rfl⟩
    funext i
    rw [latticeLevelMap_apply, map_nsmul, Pi.smul_apply, map_nsmul, Pi.zero_apply, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul]

omit [TopologicalSpace G] in
/-- The kernel of reduction, as a submodule over `ℤ`. -/
theorem ker_latticeLevelMap (k : ℕ) :
    LinearMap.ker (latticeLevelMap ρ k).toIntLinearMap =
      (latticeLevelSubmodule ρ k).restrictScalars ℤ := by
  ext v
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
  exact latticeLevelMap_eq_zero_iff ρ k v

/-- **`L / ℓᵏ L ≅ (ℤ/ℓᵏ)^r`**, by reduction of the coordinates. -/
def latticeLevelEquiv (k : ℕ) :
    (LatticeModule ρ ⧸ latticeLevelSubmodule ρ k) ≃ₗ[ℤ] (Fin r → ZMod (ℓ ^ k)) :=
  (Submodule.Quotient.restrictScalarsEquiv ℤ (latticeLevelSubmodule ρ k)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_latticeLevelMap ρ k).symm).trans
      ((latticeLevelMap ρ k).toIntLinearMap.quotKerEquivOfSurjective
        (latticeLevelMap_surjective ρ k)))

omit [TopologicalSpace G] in
/-- `latticeLevelEquiv` sends the class of `v` to the reduction of `v`. -/
theorem latticeLevelEquiv_mk (k : ℕ) (v : LatticeModule ρ) :
    latticeLevelEquiv ρ k (Submodule.Quotient.mk v) = latticeLevelMap ρ k v :=
  rfl

/-- `latticeLevelEquiv` is `G`-equivariant. -/
theorem latticeLevelEquiv_of_smul (k : ℕ) (g : G)
    (x : LatticeModule ρ ⧸ latticeLevelSubmodule ρ k) :
    latticeLevelEquiv ρ k (of ℤ G g • x) = levelRepresentation ρ k g (latticeLevelEquiv ρ k x) := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [← Submodule.Quotient.mk_smul, latticeLevelEquiv_mk, latticeLevelEquiv_mk,
      latticeLevelMap_of_smul]

omit [TopologicalSpace G] in
/-- `L / ℓᵏ L` is killed by `ℓᵏ`. -/
theorem latticeLevel_nsmul_eq_zero (k : ℕ)
    (x : ULift.{w} (LatticeModule ρ ⧸ latticeLevelSubmodule ρ k)) :
    ℓ ^ k • x = 0 := by
  refine ULift.ext ((latticeLevelEquiv ρ k).injective ?_)
  show latticeLevelEquiv ρ k (ℓ ^ k • x.down) = latticeLevelEquiv ρ k 0
  rw [map_nsmul, map_zero]
  funext i
  rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, Pi.zero_apply, zero_mul]

/-- The `ℤ/ℓᵏ`-module structure of `L / ℓᵏ L`. -/
abbrev latticeLevelZModModule (k : ℕ) :
    Module (ZMod (ℓ ^ k)) (ULift.{w} (LatticeModule ρ ⧸ latticeLevelSubmodule ρ k)) :=
  AddCommGroup.zmodModule (latticeLevel_nsmul_eq_zero ρ k)

omit [TopologicalSpace G] in
/-- `L / ℓᵏ L` is finite. -/
theorem finite_latticeLevel (k : ℕ) [NeZero (ℓ ^ k)] :
    Finite (ULift.{w} (LatticeModule ρ ⧸ latticeLevelSubmodule ρ k)) :=
  Finite.of_equiv _ (Equiv.ulift.trans (latticeLevelEquiv ρ k).toEquiv).symm

/-- **`L / ℓᵏ L` has open stabilizers** for `ρ` continuous: they are those of `(ℤ/ℓᵏ)^r`. -/
theorem groupRingIsContinuous_latticeLevel (hρ : Continuous ρ) (k : ℕ) :
    GroupRingIsContinuous G (ULift.{w} (LatticeModule ρ ⧸ latticeLevelSubmodule ρ k)) := fun m => by
  have : {g : G | of ℤ G g • m = m} =
      {g : G | levelRepresentation ρ k g (latticeLevelEquiv ρ k m.down) =
        latticeLevelEquiv ρ k m.down} := by
    ext g
    simp only [Set.mem_setOf_eq, ← latticeLevelEquiv_of_smul]
    exact ⟨fun h => by rw [← ULift.smul_down, h], fun h => ULift.ext
      ((latticeLevelEquiv ρ k).injective (by rw [ULift.smul_down]; exact h))⟩
  rw [this]
  exact isOpen_setOf_levelRepresentation_apply_eq ρ hρ k _

variable [IsTopologicalGroup G]

attribute [local instance] discreteForget₂AddCommGrpCat

/-- **The level module of `ρ` is the continuous module of `L / ℓᵏ L`.** -/
def levelModuleLatticeIso (hρ : Continuous ρ) (k : ℕ) [NeZero (ℓ ^ k)] :
    letI := latticeLevelZModModule.{v, w} ρ k
    haveI := finite_latticeLevel.{v, w} ρ k
    levelModule.{v, w} ρ hρ k ≅
      groupRingContinuousModule (ℓ ^ k) (ULift.{w} (LatticeModule ρ ⧸ latticeLevelSubmodule ρ k))
        (groupRingIsContinuous_latticeLevel ρ hρ k) :=
  letI := latticeLevelZModModule.{v, w} ρ k
  haveI := finite_latticeLevel.{v, w} ρ k
  { hom := ObjectProperty.homMk ((homEquiv (ZMod (ℓ ^ k)) G _ _).symm
      ⟨(AddEquiv.ulift.symm.toAddMonoidHom.comp
          ((latticeLevelEquiv ρ k).symm.toLinearMap.toAddMonoidHom.comp
            AddEquiv.ulift.toAddMonoidHom)).toZModLinearMap (ℓ ^ k), fun g x =>
        ULift.ext ((latticeLevelEquiv ρ k).injective (by
          change latticeLevelEquiv ρ k ((latticeLevelEquiv ρ k).symm
              (levelRepresentation ρ k g x.down)) =
            latticeLevelEquiv ρ k (of ℤ G g • (latticeLevelEquiv ρ k).symm x.down)
          rw [latticeLevelEquiv_of_smul, LinearEquiv.apply_symm_apply,
            LinearEquiv.apply_symm_apply]))⟩)
    inv := ObjectProperty.homMk ((homEquiv (ZMod (ℓ ^ k)) G _ _).symm
      ⟨(AddEquiv.ulift.symm.toAddMonoidHom.comp
          ((latticeLevelEquiv ρ k).toLinearMap.toAddMonoidHom.comp
            AddEquiv.ulift.toAddMonoidHom)).toZModLinearMap (ℓ ^ k), fun g x =>
        ULift.ext (by
          change latticeLevelEquiv ρ k (of ℤ G g • x.down) =
            levelRepresentation ρ k g (latticeLevelEquiv ρ k x.down)
          rw [latticeLevelEquiv_of_smul])⟩)
    hom_inv_id := continuousModule_hom_ext (ℓ ^ k) fun x =>
      ULift.ext (by exact (latticeLevelEquiv ρ k).apply_symm_apply x.down)
    inv_hom_id := continuousModule_hom_ext (ℓ ^ k) fun x =>
      ULift.ext (by exact (latticeLevelEquiv ρ k).symm_apply_apply x.down) }

end Stacks.EtaleCohomology

end
