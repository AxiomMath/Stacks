module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateSectionsShortExact

/-!
# Closure under extensions and the weak Serre property at every value universe

`Stacks.Adequate.adequate_isClosedUnderExtensions` (in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/Abelian.lean`) and
`Stacks.Adequate.adequate_isWeakSerreClass` (in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/TopologyIndependence.lean`) are stated,
with no hypothesis, for `𝒪`-modules with values in the universe of the site. This module states
the same two closure properties at every value universe `max u m`, given the affine-side closure
`Stacks.Adequate.AffineAdequateExtensions` at that universe, using
`Stacks.Adequate.adequateSectionsShortExact` for the exactness of the affine-section functors.

## Main results

* `Stacks.Adequate.adequate_isClosedUnderExtensions'` — adequacy is closed under extensions,
  given only the affine-side closure `Stacks.Adequate.AffineAdequateExtensions`.
* `Stacks.Adequate.adequate_isWeakSerreClass'` — the adequate `𝒪`-modules are a weak Serre
  subcategory, given only `Stacks.Adequate.AffineAdequateExtensions`. Its instance binders and
  its `Stacks.Adequate.AffineAdequateSheafTopology` binder are kept from the earlier form of the
  statement; all three are theorems (`Stacks.Adequate.BigSite.hasSheafify_addCommGrpCat`,
  `Stacks.Adequate.BigSite.wEqualsLocallyBijective_addCommGrpCat`,
  `Stacks.Adequate.affineAdequateSheafTopology`).

## Implementation notes

No `@[stacks]` attribute is placed here: [Stacks, Tag 06VQ] is registered in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/Abelian.lean` and
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AbelianUnconditional.lean`.
`Stacks.Adequate.AffineAdequateExtensions` is itself a theorem at every value universe,
`Stacks.Adequate.affineAdequateExtensions`.

## References

* [Stacks Project, Tag 06VQ](https://stacks.math.columbia.edu/tag/06VQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe d u m

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-- **Adequacy of sheaves of modules is closed under extensions**, given only the affine-side
closure property, at every value universe `max u m`. Over every affine scheme of the site the
sequence of affine-section functors is short exact, by
`Stacks.Adequate.adequateSectionsShortExact`; its outer terms are adequate by
[Stacks, Tag 06VI], so its middle term is adequate by `hext`. -/
public theorem adequate_isClosedUnderExtensions'
    (hext : AffineAdequateExtensions.{u, m} B) :
    ObjectProperty.IsClosedUnderExtensions (adequate.{u, max u m} B) where
  prop_X₂_of_shortExact {T} hT h₁ h₃ :=
    isAdequate_of_forall_affineSectionFunctor B T.X₂ fun A f hA =>
      hext A hA _ (adequateSectionsShortExact.{u, m} B T hT h₁ h₃ A f hA)
        (affineLocalAdequacy.{u, m} B T.X₁ h₁ A f hA)
        (affineLocalAdequacy.{u, m} B T.X₃ h₃ A f hA)

/-- **The adequate `𝒪`-modules are a weak Serre subcategory**, given only the affine-side
closure property under extensions, at every value universe `max u m`: closure under kernels and
cokernels holds at every value universe (`Stacks.Adequate.adequate_isClosedUnderKernels` and
`Stacks.Adequate.adequate_isClosedUnderCokernels`), and closure under extensions is
`Stacks.Adequate.adequate_isClosedUnderExtensions'`. The hypothesis `_hVP` of [Stacks, Tag 06VP]
is not used: it is the theorem `Stacks.Adequate.affineAdequateSheafTopology`, which the
cokernel closure applies. -/
public theorem adequate_isWeakSerreClass'
    [HasSheafify B.topology AddCommGrpCat.{max u m}]
    [B.topology.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    (_hVP : AffineAdequateSheafTopology.{u, m} B)
    (hext : AffineAdequateExtensions.{u, m} B) :
    (adequate.{u, max u m} B).IsWeakSerreClass :=
  let := adequate_isClosedUnderKernels.{u, m} B
  let := adequate_isClosedUnderCokernels.{u, m} B
  let := adequate_isClosedUnderExtensions'.{u, m} B hext
  { }

end Stacks.Adequate

end
