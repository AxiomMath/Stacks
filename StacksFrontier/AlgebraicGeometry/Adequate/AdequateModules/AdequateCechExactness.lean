module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateCechVanishing

/-!
# Čech exactness for adequate modules on affine flat surjections

For an adequate `𝒪`-module on a chosen big `τ`-site over `S` and a flat surjective morphism
between affine objects of the site, the Čech cohomology of the one-member family of that morphism
vanishes in every positive degree. This is the positive-degree part of [Stacks, Tag 06VL].

## Main results

* `Stacks.Adequate.affineCechExactness_of_isAdequate`: the predicate
  `Stacks.Adequate.BigSite.AffineCechExactness` holds for every sheaf of modules on every chosen
  big site.

## Implementation notes

The predicate is phrased with `Stacks.CechSite.cechCohomology` of
`CategoryTheory.PreZeroHypercover.singleton`, while
`Stacks.Adequate.isZero_cechHomology_singleton_of_isAdequate` proves the vanishing for the
alternating coface map complex of the Čech nerve of `Over.mk f`. The two complexes are identified
by `Stacks.Adequate.singletonCechComplexIso`, and the vanishing is transported along this
isomorphism.

## References

* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u m

namespace Stacks.Adequate

/-- For an adequate `𝒪`-module `F` on a chosen big `τ`-site over `S` and a flat surjective morphism
`f` between affine objects of the site, the Čech cohomology of the one-member family `{f}` with
coefficients in the underlying abelian sheaf of `F` vanishes in every positive degree; that is,
`Stacks.Adequate.BigSite.AffineCechExactness` holds for `F`. -/
public theorem affineCechExactness_of_isAdequate {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf) :
    B.AffineCechExactness.{u, m} F := by
  intro hF X Y f hX hY hflat hsurj n hn
  let : HasFiniteLimits B.category := B.hasFiniteLimits_category
  let := hflat
  let := hsurj
  exact IsZero.of_iso
    (isZero_cechHomology_singleton_of_isAdequate.{u, m} B F hF f hY hX n hn)
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso
      (singletonCechComplexIso f ((SheafOfModules.toSheaf B.structureSheaf).obj F).obj))

end Stacks.Adequate

end
