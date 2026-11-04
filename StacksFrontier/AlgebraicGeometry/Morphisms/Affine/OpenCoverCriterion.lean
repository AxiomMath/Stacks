module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute

/-!
# Checking affineness of a morphism on an affine open covering

A morphism of schemes is affine as soon as every point of its target has one affine open
neighbourhood with affine inverse image; conversely an affine morphism has affine inverse
images of all affine opens, and the affine opens form a basis of the target. So affineness
is equivalent to the existence of such a neighbourhood at every point.

## Main results

* `AlgebraicGeometry.isAffineHom_iff_forall_exists_isAffineOpen` characterizes affine
  morphisms by an affine open covering of the target with affine inverse images.

## Implementation notes

The covering is expressed pointwise: at every point of the target there is an affine open
neighbourhood whose inverse image is affine. The implication from such a covering to
affineness is Mathlib's `AlgebraicGeometry.isAffineHom_of_forall_exists_isAffineOpen`; the
converse uses that the affine opens form a basis of the topology of the target.

## References

* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 01S8, equivalence of (1) and (2).** A morphism of schemes
`f : X ⟶ S` is affine if and only if every point of `S` has an affine open neighbourhood
whose inverse image under `f` is affine. -/
@[stacks 01S8 "equivalence of (1) and (2)"]
lemma isAffineHom_iff_forall_exists_isAffineOpen {X S : Scheme.{u}} (f : X ⟶ S) :
    IsAffineHom f ↔
      ∀ x : S, ∃ U : S.Opens, x ∈ U ∧ IsAffineOpen U ∧ IsAffineOpen (f ⁻¹ᵁ U) := by
  refine ⟨fun hf x ↦ ?_, isAffineHom_of_forall_exists_isAffineOpen f⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (⊤ : S.Opens) by simp) isOpen_univ
  exact ⟨U, hxU, hU, hf.isAffine_preimage U hU⟩

end AlgebraicGeometry
