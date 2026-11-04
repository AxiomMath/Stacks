module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization

/-!
# Étale local rings and henselizations of schemes

At a geometric point of a scheme, the étale local ring is the stalk of the structure sheaf on
the small étale site. The ordinary henselization is formed from the local ring at an ordinary
point. Taking spectra gives the corresponding local schemes.

This file re-exports those constructions and nothing else.

* The étale local ring `AlgebraicGeometry.etaleLocalRing`, the chosen henselization
  `AlgebraicGeometry.henselizationRing` of an ordinary local ring and its spectrum
  `AlgebraicGeometry.henselization`, together with
  `AlgebraicGeometry.localHenselizationTower` and `AlgebraicGeometry.henselizationToBase`,
  are defined in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SchemeLocalRings`.
* The commutative ring and algebra structures on the étale local ring
  (`AlgebraicGeometry.etaleLocalRingCommRing`, `AlgebraicGeometry.etaleLocalRingAlgebra`), the
  strict henselization `AlgebraicGeometry.strictHenselization` of a scheme at a geometric point
  and its structure morphism `AlgebraicGeometry.strictHenselizationToBase` are defined in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization`, which
  reads them off the canonical identification of the étale local ring with the strict
  henselization of the ordinary local ring (Tag 04HX) and which also supplies the local ring
  structure, the ind-étaleness over the ordinary local ring, and the canonical lift of the
  geometric point.

## References

* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/
