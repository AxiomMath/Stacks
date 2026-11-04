module

public import Mathlib.FieldTheory.Galois.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.TwoCocycleInflation

/-!
# The trivialization of an inflated `2`-cocycle is locally constant

`Stacks.GaloisCohomology.isMulCoboundary₂_of_forall_finiteGalois` reduces the statement that a
locally constant `2`-cocycle of `Gal(Ω/K)` with values in `Ωˣ` is a coboundary to the same
statement at the finite Galois levels. Its conclusion is Mathlib's `IsMulCoboundary₂`, which
asks for a `1`-cochain `x : Gal(Ω/K) → Ωˣ` with `g • x h / x (gh) * x g = f (g, h)` and demands
**no continuity of `x`**. That is strictly weaker than what the derived-functor group
`H ²(Gal(Ω/K), Ωˣ)` sees, which is the vanishing of a class of *continuous* cochains.

This file closes that gap. The reduction produces `x` by inflating a `1`-cochain from a *finite*
Galois level `L/K`, i.e. `x = ι ∘ x₀ ∘ restrictNormalHom L`, so `x` factors through the finite
group `Gal(L/K)` along a homomorphism with open kernel and is therefore locally constant. The
observation costs nothing and is recorded here rather than by changing the statement of the
reduction, whose `IsMulCoboundary₂` form is what the Brauer-group clients consume.

## Main results

* `Stacks.GaloisCohomology.isLocallyConstant_of_isOpen_ker`: a group homomorphism out of a
  topological group whose kernel is open is locally constant.
* `Stacks.GaloisCohomology.exists_isLocallyConstant_isMulCoboundary₂_of_forall_finiteGalois`:
  **the reduction to the finite levels with a locally constant trivialization.** If every
  `2`-cocycle `Gal(L/K) × Gal(L/K) → Lˣ` is a coboundary at every finite Galois subextension
  `L/K` of `Ω/K`, then every locally constant `2`-cocycle of `Gal(Ω/K)` with values in `Ωˣ` is
  the coboundary of a *locally constant* `1`-cochain.

## Implementation notes

The kernel of `AlgEquiv.restrictNormalHom ↥L` is the fixing subgroup of `L`
(`IntermediateField.restrictNormalHom_ker`), which is open because `L/K` is finite
(`IntermediateField.fixingSubgroup_isOpen`). Local constancy of a homomorphism with open kernel
is proved directly from the fact that each fibre is a coset of the kernel, rather than through
continuity and discreteness of the target, so that no topology on `Gal(L/K)` is needed.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8), whose degree-two case
  this makes available to the derived-functor groups.
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR): the derived-functor
  groups, whose cochains are the continuous ones.
-/

@[expose] public noncomputable section

open IntermediateField groupCohomology

namespace Stacks.GaloisCohomology

/-- **A group homomorphism with open kernel is locally constant.** Each fibre is a union of
cosets of the kernel: if `g⁻¹ h` lies in the kernel then `φ h = φ g`, so the open set
`g · ker φ` is contained in the fibre of `φ` through `g`. No topology on the target is used. -/
theorem isLocallyConstant_of_isOpen_ker {G H : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] (φ : G →* H)
    (hker : IsOpen ((φ.ker : Subgroup G) : Set G)) : IsLocallyConstant φ := by
  intro s
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun h : G ↦ g⁻¹ * h) ⁻¹' ((φ.ker : Subgroup G) : Set G), fun h hh ↦ ?_,
    hker.preimage (by fun_prop), ?_⟩
  · simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv] at hh
    have hφ : φ h = φ g := (inv_mul_eq_one.mp hh).symm
    simp only [Set.mem_preimage] at hg ⊢
    rw [hφ]
    exact hg
  · simp

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

end Stacks.GaloisCohomology

end
