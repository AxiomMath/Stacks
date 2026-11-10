module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeFamily
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingInverse
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FiniteFibre

/-!
# Coefficients of the cycle of a closed subscheme in a zero-dimensional fibre

The fibre of a locally quasi-finite morphism locally of finite type with finite fibres is a
discrete space, and so is the inverse image in it of a closed subscheme of the source. In a
discrete space every point is the generic point of an irreducible component, so the coefficient
formula `Stacks.Chow.familyAssociatedToClosedSubscheme_apply_coeff`, which is stated at a generic
point, is available at *every* point of such a fibre.

## Main results

* `Stacks.Chow.mem_genericPoints_of_discreteTopology` — in a discrete space every point is a
  generic point.
* `Stacks.Chow.discreteTopology_pullback_fiberι` — the inverse image of a closed subscheme in a
  fibre with finite preimage is discrete.
* `Stacks.Chow.familyAssociatedToClosedSubscheme_apply_coeff_of_locallyQuasiFinite` — the
  coefficient of `[Z/X/S]_0` at an arbitrary point of the fibre of `Z`, as the multiplicity of
  that point.

## Implementation notes

`Stacks.Chow.genericPoints` of a topological space is the set of points whose closure is an
irreducible component. In a discrete space the closure of a point is the point itself, and a
singleton is a maximal irreducible subset, so the condition is vacuous. Discreteness of the
inverse image is discreteness of a subspace, the inverse image being embedded in the fibre by
`Stacks.Chow.fiberClosedImmersion`, which is a closed immersion.

## References

* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
* [Stacks Project, Tag 02NG](https://stacks.math.columbia.edu/tag/02NG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- In a discrete topological space every point is the generic point of an irreducible
component, namely of its own singleton. -/
theorem mem_genericPoints_of_discreteTopology {α : Type*} [TopologicalSpace α]
    [DiscreteTopology α] (x : α) : x ∈ genericPoints α := by
  have hcl : closure ({x} : Set α) = {x} := closure_singleton
  change closure ({x} : Set α) ∈ irreducibleComponents α
  rw [hcl]
  refine ⟨isIrreducible_singleton, fun t ht hsub ↦ ?_⟩
  intro z hz
  have hxt : x ∈ t := hsub rfl
  by_contra hne
  obtain ⟨w, -, hw1, hw2⟩ :=
    ht.2 {x} {x}ᶜ (isOpen_discrete _) (isOpen_discrete _) ⟨x, hxt, rfl⟩ ⟨z, hz, hne⟩
  exact hw2 hw1

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]

/-- The inverse image in the fibre over `s` of a closed subscheme of the source is a discrete
space, as a subspace of the discrete fibre. -/
theorem discreteTopology_pullback_fiberι {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (s : S) (hfin : (f ⁻¹' {s}).Finite) :
    DiscreteTopology ↥(pullback i (f.fiberι s)) := by
  have : DiscreteTopology (f.fiber s) := discreteTopology_fiber_of_finite_preimage f s hfin
  exact (IsClosedImmersion.isClosedEmbedding
    (fiberClosedImmersion f i s)).isEmbedding.discreteTopology

/-- The coefficient of `[Z/X/S]_0` at an arbitrary point of the inverse image of `Z` in a
zero-dimensional fibre is the multiplicity of that point. The hypotheses are those of a locally
quasi-finite morphism with finite fibres, which make the fibre discrete so that every point is a
generic point. -/
theorem familyAssociatedToClosedSubscheme_apply_coeff_of_locallyQuasiFinite
    [LocallyQuasiFinite f] {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (s : S)
    (hfin : (f ⁻¹' {s}).Finite) (ξ : ↥(pullback i (f.fiberι s))) :
    (familyAssociatedToClosedSubscheme f i 0 s).1 (fiberClosedImmersion f i s ξ) =
      componentMultiplicity (fiberClosedImmersion f i s)
        ⟨ξ, by
          have := discreteTopology_pullback_fiberι f i s hfin
          exact mem_genericPoints_of_discreteTopology ξ⟩ := by
  have := discreteTopology_pullback_fiberι f i s hfin
  exact familyAssociatedToClosedSubscheme_apply_coeff f i 0 s
    ⟨ξ, mem_genericPoints_of_discreteTopology ξ⟩
    (relativeDimension_fiber_eq_zero_of_locallyQuasiFinite f s _)

end Stacks.Chow

end
