module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhCoveringRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.Refinement

/-!
# Ph coverings are inherited along refinements

A family of morphisms locally of finite type which is refined by a ph covering, in the sense of
a morphism of `CategoryTheory.PreZeroHypercover`s, is itself a ph covering: the standard ph
coverings refining the base changes of the refining family to the affine opens of the target
refine those of the original family as well.

## Main results

* `AlgebraicGeometry.IsPHCovering.of_hom` — being a ph covering is inherited along refinements.

## References

* [Stacks Project, Tag 0ET9](https://stacks.math.columbia.edu/tag/0ET9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- **Being a ph covering is inherited along refinements.** If `E` is a ph covering refining the
family `F`, and every member of `F` is locally of finite type, then `F` is a ph covering: the
standard ph coverings refining the base changes of `E` to the affine opens of the target refine
those of `F` as well. -/
public theorem IsPHCovering.of_hom {T : Scheme.{u}} {E : PreZeroHypercover.{v} T}
    {F : PreZeroHypercover.{w} T} (hE : IsPHCovering E.X E.f) (φ : E.Hom F)
    (hF : ∀ i, LocallyOfFiniteType (F.f i)) : IsPHCovering F.X F.f := by
  refine ⟨hF, fun U hU => ?_⟩
  obtain ⟨𝒰, h𝒰, ⟨ψ⟩⟩ := hE.2 U hU
  exact ⟨𝒰, h𝒰, ⟨ψ.comp (φ.pullback₂ U.ι)⟩⟩

end AlgebraicGeometry
