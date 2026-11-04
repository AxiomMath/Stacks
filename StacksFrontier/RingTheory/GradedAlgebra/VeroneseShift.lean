module

public import StacksFrontier.AlgebraicGeometry.ProjTwists.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseGrading
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Veronese parts of shifted modules

Let `S` be a graded ring, `d` a natural number and `M` a `ℤ`-graded `S`-module, with Veronese
part `M⁽ᵈ⁾ = ⨁ₖ M_{kd}` over the Veronese subring `S⁽ᵈ⁾`. The Veronese part of the shift `M(nd)`
and the shift `M⁽ᵈ⁾(n)` of the Veronese part are the same graded `S⁽ᵈ⁾`-module: both are the
elements of `M` lying in degrees divisible by `d`, and in degree `k` both are `M_{(k+n)d}`. This
is `veroneseModuleShiftEquiv`, the identity of underlying elements.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 00JL](https://stacks.math.columbia.edu/tag/00JL)
-/

@[expose] public noncomputable section

namespace Stacks.Veronese

open Stacks.GradedModule (shiftedGrading)

variable {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {M : Type*} [AddCommGroup M] [Module A M]
variable (ℳ : ℤ → AddSubgroup M)

section Shift

/-- The generating set of the Veronese part of `M(nd)` is that of `M⁽ᵈ⁾`: the homogeneous
pieces of `M(nd)` in degrees divisible by `d` are those of `M`, reindexed by `n`. -/
public theorem veroneseModuleSet_shiftedGrading (d : ℕ) (n : ℤ) :
    veroneseModuleSet (shiftedGrading ℳ (n * d)) d = veroneseModuleSet ℳ d := by
  ext x
  rw [mem_veroneseModuleSet_iff, mem_veroneseModuleSet_iff]
  exact ⟨fun ⟨k, hk⟩ => ⟨k + n, by rwa [add_mul]⟩,
    fun ⟨j, hj⟩ => ⟨j - n, by rwa [← sub_add_cancel j n, add_mul] at hj⟩⟩

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The Veronese part of `M(nd)` and that of `M` are the same submodule of `M`. -/
public theorem veroneseSubmodule_shiftedGrading (d : ℕ) (n : ℤ) :
    veroneseSubmodule 𝒜 (shiftedGrading ℳ (n * d)) d = veroneseSubmodule 𝒜 ℳ d := by
  rw [veroneseSubmodule, veroneseSubmodule, veroneseModuleSet_shiftedGrading]

/-- **The Veronese part of `M(nd)` is the shift `M⁽ᵈ⁾(n)`**: the identity of underlying
elements, as a linear equivalence over `S⁽ᵈ⁾`. That it matches the gradings is
`veroneseModuleShiftEquiv_mem` and `veroneseModuleShiftEquiv_symm_mem`. -/
public noncomputable def veroneseModuleShiftEquiv (d : ℕ) (n : ℤ) :
    veroneseSubmodule 𝒜 (shiftedGrading ℳ (n * d)) d ≃ₗ[veroneseSubring 𝒜 d]
      veroneseSubmodule 𝒜 ℳ d :=
  LinearEquiv.ofEq _ _ (veroneseSubmodule_shiftedGrading 𝒜 ℳ d n)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- `veroneseModuleShiftEquiv` is the identity on underlying elements of `M`. -/
@[simp]
public theorem coe_veroneseModuleShiftEquiv (d : ℕ) (n : ℤ)
    (x : veroneseSubmodule 𝒜 (shiftedGrading ℳ (n * d)) d) :
    ((veroneseModuleShiftEquiv 𝒜 ℳ d n x : veroneseSubmodule 𝒜 ℳ d) : M) = (x : M) :=
  rfl

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The inverse of `veroneseModuleShiftEquiv` is the identity on underlying elements of `M`. -/
@[simp]
public theorem coe_veroneseModuleShiftEquiv_symm (d : ℕ) (n : ℤ)
    (x : veroneseSubmodule 𝒜 ℳ d) :
    (((veroneseModuleShiftEquiv 𝒜 ℳ d n).symm x :
        veroneseSubmodule 𝒜 (shiftedGrading ℳ (n * d)) d) : M) = (x : M) :=
  rfl

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- `veroneseModuleShiftEquiv` carries the degree-`k` piece of `M(nd)⁽ᵈ⁾` into that of
`M⁽ᵈ⁾(n)`: both are `M_{(k+n)d}`. -/
@[ega "II 2.5.16" "(d)"]
public theorem veroneseModuleShiftEquiv_mem (d : ℕ) (n : ℤ) (k : ℤ)
    (x : veroneseSubmodule 𝒜 (shiftedGrading ℳ (n * d)) d)
    (hx : x ∈ veroneseModuleGrading 𝒜 (shiftedGrading ℳ (n * d)) d k) :
    veroneseModuleShiftEquiv 𝒜 ℳ d n x ∈
      shiftedGrading (veroneseModuleGrading 𝒜 ℳ d) n k := by
  change (x : M) ∈ ℳ ((k + n) * (d : ℤ))
  rwa [add_mul]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The inverse of `veroneseModuleShiftEquiv` preserves the gradings. -/
@[ega "II 2.5.16" "(d)"]
public theorem veroneseModuleShiftEquiv_symm_mem (d : ℕ) (n : ℤ) (k : ℤ)
    (x : veroneseSubmodule 𝒜 ℳ d)
    (hx : x ∈ shiftedGrading (veroneseModuleGrading 𝒜 ℳ d) n k) :
    (veroneseModuleShiftEquiv 𝒜 ℳ d n).symm x ∈
      veroneseModuleGrading 𝒜 (shiftedGrading ℳ (n * d)) d k := by
  change (x : M) ∈ ℳ (k * (d : ℤ) + n * d)
  rwa [← add_mul]

end Shift

end Stacks.Veronese

end
