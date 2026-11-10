module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SchemeImageDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableClosedSubspaceIdeal

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The scheme-theoretic image of a morphism of the site

For a morphism `h : A ⟶ Y` of the big fppf site over `S`, the scheme-theoretic image of Stacks
082X of the represented morphism `h_A ⟶ h_Y` is represented by the scheme-theoretic image of the
underlying morphism of schemes: it is the range of any represented closed immersion `j : R ⟶ Y`
with the same kernel ideal sheaf as `h`.

## Main results

* `AlgebraicGeometry.Space.range_yoneda_map_le_iff_ker_le` (of
  `StacksFrontier.AlgebraicGeometry.Spaces.RepresentableClosedSubspaceIdeal`): a represented
  morphism factors
  through a represented closed immersion exactly when the kernel ideal sheaf of the closed
  immersion is contained in that of the morphism.
* `AlgebraicGeometry.Space.C1573.schemeTheoreticImageSubfunctor_yoneda_map_eq_range`: the statement
  above.

## References

* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 01R7](https://stacks.math.columbia.edu/tag/01R7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The scheme-theoretic image of a represented morphism is the range of any represented
closed immersion with the same kernel ideal sheaf.** -/
theorem C1573.schemeTheoreticImageSubfunctor_yoneda_map_eq_range {A Y R : BigFppfOver B S hS}
    (h : A ⟶ Y) (j : R ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (hker : ((BigFppfOver.toScheme B S hS).map j).ker =
      ((BigFppfOver.toScheme B S hS).map h).ker) :
    schemeTheoreticImageSubfunctor B S hS (yoneda.map h) = Subfunctor.range (yoneda.map j) := by
  refine le_antisymm (schemeTheoreticImageSubfunctor_le B S hS (yoneda.map h)
    (isClosedSubspace_range_yoneda_map B S hS j inferInstance)
    ((range_yoneda_map_le_iff_ker_le _ _ _ j h inferInstance).2 hker.le)) ?_
  obtain ⟨R', j', hj', heq⟩ := exists_closedImmersion_range B S hS
    (schemeTheoreticImageSubfunctor B S hS (yoneda.map h))
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS (yoneda.map h)
      (isAlgebraicSpace_yoneda B S hS Y))
  have := hj'
  have hle : ((BigFppfOver.toScheme B S hS).map j').ker ≤
      ((BigFppfOver.toScheme B S hS).map h).ker := by
    refine (range_yoneda_map_le_iff_ker_le _ _ _ j' h inferInstance).1 ?_
    rw [← heq]
    exact range_le_schemeTheoreticImageSubfunctor B S hS (yoneda.map h)
  rw [heq]
  exact (range_yoneda_map_le_iff_ker_le _ _ _ j' j inferInstance).2 (hker ▸ hle)

end AlgebraicGeometry.Space

end
