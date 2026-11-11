module

public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The size of an étale lift across a thickening

Let `q : L ⟶ U` be étale and let `j : L₀ ⟶ L` be a surjective closed immersion. Then the size of
`L` is bounded by the sizes of `L₀` and of `U`: the affine opens of `L` inject into those of `L₀`
by taking preimages, and an affine open of `L` is of finite type and quasi-compact over `U`.

This is the bound that keeps the étale lift of an object of a big fppf site across a thickening
inside the site, uniformly over the affine opens of a test object.

## Main results

* `AlgebraicGeometry.Scheme.size_le_of_etale_of_isClosedImmersion`: the bound.

## References

* [Stacks Project, Section 000H](https://stacks.math.columbia.edu/tag/000H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-- **The size of an étale lift across a thickening.** If `q : L ⟶ U` is étale and
`j : L₀ ⟶ L` is a closed immersion surjective on points, then `size L ≤ max (size L₀) (size U)`.
-/
theorem Scheme.size_le_of_etale_of_isClosedImmersion {L U L₀ : Scheme.{u}} (q : L ⟶ U)
    [Etale q] (j : L₀ ⟶ L) [IsClosedImmersion j] (hj : Function.Surjective j.base) :
    L.size ≤ max L₀.size U.size := by
  refine Scheme.size_le_of_bounds ((Scheme.aleph0_le_size L₀).trans (le_max_left _ _)) ?_ ?_
  · -- the affine opens of `L` inject into those of `L₀`
    refine (mk_le_of_injective (f := fun W : L.affineOpens ↦
      (⟨j ⁻¹ᵁ W.1, W.2.preimage j⟩ : L₀.affineOpens)) ?_).trans
      ((Scheme.mk_affineOpens_le_size L₀).trans (le_max_left _ _))
    intro W W' h
    have h' : j ⁻¹ᵁ W.1 = j ⁻¹ᵁ W'.1 := congrArg Subtype.val h
    refine Subtype.ext (TopologicalSpace.Opens.ext (Set.ext fun x ↦ ?_))
    obtain ⟨y, rfl⟩ := hj x
    exact Iff.of_eq (congrArg (y ∈ ·) h')
  · -- an affine open of `L` is of finite type and quasi-compact over `U`
    intro W
    have : IsAffine (W.1 : Scheme.{u}) := W.2
    rw [← Scheme.mk_sections_coe_opens L W.1]
    refine ((Scheme.mk_sections_le_size (W.1 : Scheme.{u})
      ⟨⊤, isAffineOpen_top _⟩).trans ?_).trans (le_max_right _ _)
    exact Scheme.size_le_of_locallyOfFiniteType (W.1.ι ≫ q)

end AlgebraicGeometry

end
