module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecInvertibleLocus
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleZeroSectionComparison

/-!
# Proj and Spec over the invertible locus: the zero section is the vector-bundle zero section

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `P = Proj A`, `π : L ⟶ P` the cone with zero section
`0 : P ⟶ L`, and `W ⊆ P` the open of [Stacks, Tag 01MU] for `d = 1`, over which
`L|_W ≅ 𝐕(𝒪_P(1)|_W)` (`coneRestrictIsoVectorBundle`; the names here are in the namespace
`Stacks.AlgebraicGeometry.ProjAndSpecInvertibleLocus`). The theorem
`zeroSectionRestrict_comp_coneRestrictIsoVectorBundle_hom` identifies `0|_W` under this
isomorphism with the point of `𝐕(𝒪_P(1)|_W)` whose module morphism is zero. This file restates it
with the zero section of the vector bundle in its Stacks/EGA form,
`AlgebraicGeometry.Scheme.Modules.vectorBundleZeroSection`, the section cut out by the
augmentation `Sym(𝒪_P(1)|_W) ⟶ 𝒪_W`; the two agree by
`AlgebraicGeometry.Scheme.Modules.vectorBundleOverZeroSection_left`.

## Main results

* `zeroSectionRestrict_comp_coneRestrictIsoVectorBundle_hom_eq_vectorBundleZeroSection`:
  **under `L|_W ≅ 𝐕(𝒪_P(1)|_W)` the zero section `0|_W` is the zero section of the vector
  bundle.**

## References

* [Stacks Project, Tag 0EKF](https://stacks.math.columbia.edu/tag/0EKF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

namespace Stacks.AlgebraicGeometry.ProjAndSpecInvertibleLocus

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Under `L|_W ≅ 𝐕(𝒪_P(1)|_W)` the zero section `0|_W` is the zero section of the vector
bundle**, the section of `𝐕(𝒪_P(1)|_W) ⟶ W` cut out by the augmentation
`Sym(𝒪_P(1)|_W) ⟶ 𝒪_W`. -/
@[stacks 0EKF "under L|_W = V(O_P(1)|_W) the zero section 0|_W is the zero section of the \
vector bundle, the section cut out by the augmentation Sym → O_W"]
theorem zeroSectionRestrict_comp_coneRestrictIsoVectorBundle_hom_eq_vectorBundleZeroSection :
    zeroSectionRestrict 𝒜 ≫ (coneRestrictIsoVectorBundle 𝒜).hom =
      vectorBundleZeroSection (locus 𝒜).toScheme (twistOneRestrict 𝒜) :=
  (zeroSectionRestrict_comp_coneRestrictIsoVectorBundle_hom 𝒜).trans
    (vectorBundleOverZeroSection_left (twistOneRestrict 𝒜))

end Stacks.AlgebraicGeometry.ProjAndSpecInvertibleLocus

end
