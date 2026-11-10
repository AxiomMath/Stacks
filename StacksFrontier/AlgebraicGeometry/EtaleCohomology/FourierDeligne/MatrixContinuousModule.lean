module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationLevels

/-!
# The finite continuous module of a matrix representation over a finite ring

For a finite commutative ring `Λ` and a representation `σ : G → GL_m(Λ)` of a topological group
with open kernel, `Λ^m` with `G` acting through `σ` is a finite `Λ`-module with continuous
`G`-action (for the discrete topology on `Λ^m`). These are the monodromy modules of the lisse
sheaves of `Λ`-modules with a chosen basis, e.g. the reductions modulo `ℓ^{N+1}` of an integral
model of a representation over the integers of a finite extension of `ℚ_ℓ`.

## Main definitions

* `Stacks.EtaleCohomology.matrixULiftRepresentation`: the representation on `ULift (Fin m → Λ)`.
* `Stacks.EtaleCohomology.matrixContinuousModule`: the finite continuous `Λ`-`G`-module.
-/

@[expose] public noncomputable section

open CategoryTheory Matrix

universe v w

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ] {G : Type v} [Group G] [TopologicalSpace G] {m : ℕ}

/-- The representation of `G` on `Λ^m` through `σ`, transported to a carrier in the universe
`w`. -/
public def matrixULiftRepresentation (σ : G →* GL (Fin m) Λ) :
    Representation Λ G (ULift.{w} (Fin m → Λ)) :=
  { toFun := fun g => (ULift.moduleEquiv (R := Λ)).symm.toLinearMap ∘ₗ
      Matrix.toLin' (σ g).val ∘ₗ (ULift.moduleEquiv (R := Λ)).toLinearMap
    map_one' := by
      ext x : 1
      exact ULift.ext (by simp)
    map_mul' := fun g h => by
      ext x : 1
      exact ULift.ext (by simp [Module.End.mul_apply, Matrix.mulVec_mulVec]) }

omit [TopologicalSpace G] in
/-- The representation `matrixULiftRepresentation Λ σ` acts on the underlying vector of
`x : ULift (Fin m → Λ)` by multiplication by the matrix `σ g`. -/
@[simp]
public theorem matrixULiftRepresentation_apply_down (σ : G →* GL (Fin m) Λ) (g : G)
    (x : ULift.{w} (Fin m → Λ)) :
    (matrixULiftRepresentation.{v, w} Λ σ g x).down = (σ g).val *ᵥ x.down :=
  rfl

section Modules

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

open Stacks.GroupCohomology

variable [IsTopologicalGroup G]

/-- The action of `G` on the discrete module `Λ^m` through `σ` is continuous when `σ` has open
kernel: the stabiliser of every vector contains `ker σ`. -/
public theorem isContinuous_matrixULiftRepresentation (σ : G →* GL (Fin m) Λ)
    (hσ : IsOpen (σ.ker : Set G)) :
    (actionOfRepresentation Λ G _ (matrixULiftRepresentation.{v, w} Λ σ)).IsContinuous :=
  (isContinuous_actionOfRepresentation_iff _).2 fun x => by
    refine isOpen_iff_forall_mem_open.2 fun g hg =>
      ⟨(g * ·) '' (σ.ker : Set G), ?_, isOpenMap_mul_left g _ hσ, ⟨1, one_mem _, mul_one g⟩⟩
    rintro _ ⟨k, hk, rfl⟩
    have hk' : σ k = 1 := hk
    refine ULift.ext ?_
    change (σ (g * k)).val *ᵥ x.down = x.down
    rw [map_mul, hk', mul_one]
    exact congrArg ULift.down hg

/-- **The matrix module**: `Λ^m` with the continuous action of `G` through `σ`, a finite
`Λ`-module with continuous `G`-action. -/
public def matrixContinuousModule (σ : G →* GL (Fin m) Λ) (hσ : IsOpen (σ.ker : Set G)) :
    FiniteTypeContinuousModule.{0, v, w} Λ G :=
  ⟨ofRepresentation (matrixULiftRepresentation.{v, w} Λ σ)
      (isContinuous_matrixULiftRepresentation Λ σ hσ),
    (ModuleCat.isFG_iff _).2 (Module.Finite.equiv (ULift.moduleEquiv (R := Λ)).symm)⟩

end Modules

end Stacks.EtaleCohomology

end
