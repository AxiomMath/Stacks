module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedSchematicLocus

/-!
# The schematic locus of an algebraic space

Every algebraic space has a largest open subspace which is a scheme, and for a quasi-separated
algebraic space this open subspace is dense.

## Implementation notes

The largest open subspace is `AlgebraicGeometry.Space.schematicLocus`, and that it is the
greatest representable open subspace is
`AlgebraicGeometry.Space.exists_isGreatest_isOpenSubspace_isRepresentable` (Tag 03JH). Density is
`AlgebraicGeometry.Space.denseRange_schematicLocus_of_isZariskiLocallyQuasiSeparatedOver`
(Tag 06NH), proved for Zariski locally quasi-separated algebraic spaces, a class containing the
quasi-separated ones. The section tag is registered on these declarations. The section's
illustration that the schematic locus may be empty (for `𝔸¹_ℚ/ℤ`) is an example, not an
assertion about all algebraic spaces, and is not formalized here.

## References

* [Stacks Project, Tag 03JG](https://stacks.math.columbia.edu/tag/03JG)
-/

@[expose] public section

add_to_stacks 03JG "the schematic locus" AlgebraicGeometry.Space.schematicLocus
add_to_stacks 03JG "a largest open subspace which is a scheme"
  AlgebraicGeometry.Space.exists_isGreatest_isOpenSubspace_isRepresentable
add_to_stacks 03JG "density of the schematic locus for quasi-separated spaces"
  AlgebraicGeometry.Space.denseRange_schematicLocus_of_isZariskiLocallyQuasiSeparatedOver
