module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointNeighborhoodLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.StalkTorsionOfSupportedComplex

/-!
# The stalk of the ideal of an inverse image

Let `f : Y ⟶ X` be a morphism of algebraic spaces, `Z ⊆ X` a closed subspace and `ȳ` a geometric
point of `Y` with image `x̄`. The proof of Stacks 0AEU uses that the stalk `I_ȳ` of the ideal of
`f^{-1}Z` contains `I_x̄ 𝒪_{Y,ȳ}`, so that an `I_ȳ`-power torsion module is
`I_x̄ 𝒪_{Y,ȳ}`-power torsion. This file proves that inclusion.

## Main results

* `AlgebraicGeometry.Space.map_closedSubspaceStalkIdeal_le`: the image of `I_x̄` under the
  homomorphism `𝒪_{X,x̄} ⟶ 𝒪_{Y,ȳ}` of Stacks 04NG lies in `I_ȳ`. A generator of `I_x̄` is the germ
  of a section of the defining ideal of `Z` on a pointed chart of `X`; its image is the germ of
  the pullback of that section to a pointed chart of `Y` over it
  (`AlgebraicGeometry.Space.etaleLocalRingMap_germ`), which lies in the defining ideal of
  `f^{-1}Z` (`AlgebraicGeometry.Space.mem_definingIdealAt_chartDiagramPullback`).

## References

* [Stacks Project, Tag 0AEU](https://stacks.math.columbia.edu/tag/0AEU)
* [Stacks Project, Tag 0AET](https://stacks.math.columbia.edu/tag/0AET)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`I_x̄ 𝒪_{Y,ȳ} ⊆ I_ȳ`.** The image under `𝒪_{X,x̄} ⟶ 𝒪_{Y,ȳ}` of the stalk of the ideal of a
closed subspace `Z ⊆ X` lies in the stalk of the ideal of `f^{-1}Z`. -/
theorem map_closedSubspaceStalkIdeal_le {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) (y : GeometricPoint B S hS Y.1) :
    (closedSubspaceStalkIdeal B S hS X Z (geometricPointMap f.hom y)).map
        (etaleLocalRingMap Y.2 f.hom y) ≤
      closedSubspaceStalkIdeal B S hS Y (preimageSubspace B S hS f Z) y := by
  rw [closedSubspaceStalkIdeal, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨N, a, ha, rfl⟩, rfl⟩
  obtain ⟨N₀⟩ := nonempty_smallEtaleNeighborhood Y.2 y
  obtain ⟨U, -, g, hcomm, hpt⟩ := exists_smallEtaleNeighborhood_lift f.hom N₀ N
  show etaleLocalRingMap Y.2 f.hom y (etaleLocalRingGerm B S hS X.1 _ (op N) a) ∈ _
  rw [etaleLocalRingMap_germ Y.2 f.hom U N g hcomm hpt a]
  refine Ideal.subset_span ⟨U, _, ?_, rfl⟩
  have hsq : subspaceInclusion B S hS Y (preimageSubspace B S hS f Z) ≫ f =
      preimageProjection B S hS f Z ≫ subspaceInclusion B S hS X Z := by
    ext1
    exact (Subfunctor.fromPreimage_ι Z.1 f.hom).symm
  exact mem_definingIdealAt_chartDiagramPullback B S hS (preimageSubspace B S hS f Z) Z f
    (preimageProjection B S hS f Z) hsq ⟨U.chart, N.chart, g, hcomm⟩ a ha

end AlgebraicGeometry.Space

end
