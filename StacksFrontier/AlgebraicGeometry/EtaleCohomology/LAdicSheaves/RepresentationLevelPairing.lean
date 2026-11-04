module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationLevels
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DeligneConjectureConclusions

/-!
# The evaluation pairing between the levels of `ρ` and of its contragredient

Let `ρ : G → GL_r(ℤ_ℓ)` be a representation. At level `k` the module `(ℤ/ℓ^kℤ)^r` of `ρ` and the
module `(ℤ/ℓ^kℤ)^r` of the contragredient `ρ^∨ = (ρᵀ)⁻¹` are dual to each other: the standard
pairing `⟨x, y⟩ = Σ xᵢ yᵢ` satisfies `⟨ρ(g) x, ρ^∨(g) y⟩ = ⟨x, y⟩`.

## Main results

* `Stacks.EtaleCohomology.levelRepresentation_dotProduct_contragredient`: the pairing is
  invariant.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  (ρ : G →* GL (Fin r) ℤ_[ℓ])

/-- **The evaluation pairing is invariant**: `⟨ρ(g) x, ρ^∨(g) y⟩ = ⟨x, y⟩` at every level. -/
public theorem levelRepresentation_dotProduct_contragredient (k : ℕ) (g : G)
    (x y : Fin r → ZMod (ℓ ^ k)) :
    levelRepresentation ρ k g x ⬝ᵥ levelRepresentation (contragredient ρ) k g y = x ⬝ᵥ y := by
  rw [levelRepresentation_apply, levelRepresentation_apply, contragredient_val,
    dotProduct_mulVec, vecMul_mulVec, ← Matrix.transpose_map, ← mulVec_transpose,
    transpose_mul, transpose_map, transpose_map, transpose_transpose, transpose_transpose,
    ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _), one_mulVec]

end Stacks.EtaleCohomology

end
