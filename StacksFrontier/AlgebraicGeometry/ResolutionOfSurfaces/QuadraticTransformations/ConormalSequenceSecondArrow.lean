module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.DifferentialsVanishing
public import StacksFrontier.AlgebraicGeometry.Thickenings.UnramifiedPairSplitConormalSequence

/-!
# The second arrow of the conormal sequence of two immersions

For immersions `i : Z ⟶ X` and `j : Z ⟶ Y` in a commutative triangle `i ≫ p = j` the conormal
sequence

`𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^* Ω_{X/Y} ⟶ 0`

has an epimorphic second arrow, and the composite of its two arrows vanishes.

## Main results

* `Stacks.ResolutionOfSurfaces.conormalSequenceSecondArrow` — the proposition
  `Stacks.ResolutionOfSurfaces.ConormalSequenceSecondArrow` holds: the conormal differential of
  `i` over `p`, read through the identification of the two presentations of `𝒞_{Z/X}`, is an
  epimorphism which the comparison map `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` composes to zero with.

## References

* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace Stacks.ResolutionOfSurfaces

/-- **The second arrow of the conormal sequence of two immersions is an epimorphism killed by
the first arrow.** For immersions `i : Z ⟶ X` and `j : Z ⟶ Y` in a commutative triangle
`i ≫ p = j`, the conormal differential of `i` over `p` read through the identification of the
two presentations of `𝒞_{Z/X}` is an epimorphism, and the comparison map `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}`
composes with it to zero. -/
public theorem conormalSequenceSecondArrow : ConormalSequenceSecondArrow.{u} := by
  intro Z X Y i j p _ _ h
  refine ⟨Stacks.ConormalSequenceTwoImmersions.conormalDifferentialModules i p, ?_,
    Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMapModules_comp_eq_zero i j p h⟩
  exact epi_comp'
    (IsIso.epi_of_iso (Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso i).inv)
    (Stacks.ConormalSequenceTwoImmersions.epi_conormalDifferential i j p h)

end Stacks.ResolutionOfSurfaces

end
