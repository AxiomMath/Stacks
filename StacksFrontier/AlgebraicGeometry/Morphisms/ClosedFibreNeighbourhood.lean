module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Open neighbourhoods of a fibre of a closed morphism

Let `f : X ⟶ S` be a universally closed morphism to an affine scheme and let `V` be an open of
`X` containing the whole fibre of `f` over a point `x`. Since `f` is closed, the image of the
complement of `V` is a closed subset of `S` not containing `x`, so some standard open `D(r)`
around `x` has its whole preimage inside `V`. This is the step "the locus where given sections
generate is open on the base" in the proof that a family of curves has a Weierstrass equation
Zariski locally on its base.

## Main results

* `AlgebraicGeometry.exists_mem_basicOpen_preimage_le`: the statement above.

## References

* [Stacks Project, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- If `f : X ⟶ S` is universally closed with `S` affine and the open `V ⊆ X` contains the fibre
of `f` over `x`, then a standard open `D(r)` of `S` containing `x` has its preimage in `V`. -/
theorem exists_mem_basicOpen_preimage_le {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f]
    [IsAffine S] (V : X.Opens) (x : S) (hx : ∀ y : X, f.base y = x → y ∈ V) :
    ∃ r : Γ(S, ⊤), x ∈ S.basicOpen r ∧ f ⁻¹ᵁ S.basicOpen r ≤ V := by
  have hclosed : IsClosed (f.base '' (V : Set X)ᶜ) :=
    f.isClosedMap _ V.isOpen.isClosed_compl
  have hxZ : x ∉ f.base '' (V : Set X)ᶜ := by
    rintro ⟨y, hy, rfl⟩
    exact hy (hx y rfl)
  have hxU : x ∈ (⟨_, hclosed.isOpen_compl⟩ : S.Opens) := hxZ
  obtain ⟨_, ⟨r, rfl⟩, hxr, hr⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (isBasis_basicOpen S) hxU
  refine ⟨r, hxr, fun y hy => ?_⟩
  by_contra hyV
  exact hr hy ⟨y, hyV, rfl⟩

end AlgebraicGeometry
