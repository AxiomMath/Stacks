module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.HenselizationTower

/-!
# Henselizations and strict henselizations

For a local ring `R` and a chosen separable closure `κsep` of its residue field, there is a
chosen tower of canonical flat local maps `R → Rʰ → Rˢʰ`. The two rings are ind-étale over
`R`, are respectively henselian and strictly henselian, and have the prescribed residue fields.

The mathematics lives in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.HenselizationTower`, which this
module re-exports; `IsLocalRing.HenselizationTower`, `IsLocalRing.henselizationTower` and the
eighteen accompanying instances are declared there, with `@[stacks 03QL]`.

## References

* [Stacks Project, Tag 03QL](https://stacks.math.columbia.edu/tag/03QL)
-/
