module

public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism.SchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism.ChartFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism.IsBirational

/-!
# Birational morphisms of algebraic spaces

A morphism `f : X ⟶ Y` of algebraic spaces over `S` with finitely many irreducible
components is *birational* when it restricts to a bijection between the generic points of
the irreducible components of `|X|` and those of `|Y|`, and induces an isomorphism of local
rings at every one of them.

The local ring of an algebraic space at a generic point is not the stalk of a structure
sheaf on `|X|`: it is computed on the schematic locus of Stacks 03JH, the largest
representable open subspace, which contains every generic point because its point set is
dense and open. The resulting ring is independent of the schematic chart used to compute it,
and the morphism between two such rings is characterized by its expression on any pair of
compatible charts; those two facts are what make the definition well posed, and they are the
bulk of this file.

## Main definitions

* `AlgebraicGeometry.Space.HasDenseRepresentableOpenSubspace` is the conclusion of
  Stacks 086U for an algebraic space: it has a representable open subspace with dense point
  set.
* `AlgebraicGeometry.Space.schematicScheme` and `AlgebraicGeometry.Space.schematicChart` are
  the scheme representing the schematic locus and its open immersion into the space.
* `AlgebraicGeometry.Space.GenericChart` is a schematic open chart around a point, with
  `AlgebraicGeometry.Space.GenericChart.localRing` its local ring there.
* `AlgebraicGeometry.Space.genericLocalRing` is the local ring of an algebraic space at a
  generic point, and `AlgebraicGeometry.Space.chartStalkIso` identifies it with the local
  ring of any schematic chart at that point.
* `AlgebraicGeometry.Space.genericLocalRingMap` is the map of local rings at a generic point
  induced by a morphism.
* `AlgebraicGeometry.Space.IsBirational` is birationality of a morphism.

## Main results

* `AlgebraicGeometry.Space.hasDenseRepresentableOpenSubspace_of_isDecentSpace`: a decent algebraic
  space has a representable open subspace with dense point set, by Stacks 086U.
* `AlgebraicGeometry.Space.exists_schematicRepresentative`: a generic point is represented by
  a field-valued point of the schematic locus.
* `AlgebraicGeometry.Space.exists_coherentChartStalkIso` and
  `AlgebraicGeometry.Space.chartStalkIso_naturality`: the identifications of the charts'
  stalks with the local ring form a coherent family, compatible with every refinement.
* `AlgebraicGeometry.Space.exists_genericLocalRingMap`: the induced map of local rings is
  the unique one expressed by the stalk map of every pair of compatible charts.
* `AlgebraicGeometry.Space.isBirational_iff`, `AlgebraicGeometry.Space.IsBirational.bijOn`
  and `AlgebraicGeometry.Space.IsBirational.isIso_genericLocalRingMap` unpack the
  definition.

## Implementation notes

The source states the definition for *decent* algebraic spaces with finitely many irreducible
components. Decency is used there for exactly one thing: it supplies Stacks 086U, that the space
has a representable open subspace with dense point set, which is what puts the generic points
inside the schematic locus. Birationality is accordingly stated for decent spaces, with
`AlgebraicGeometry.Space.hasDenseRepresentableOpenSubspace_of_isDecentSpace` extracting that dense
representable open subspace from decency. The intermediate constructions are parameterised by the
dense representable open subspace itself, which is all of decency that they consume.

The finiteness of the set of irreducible components is used through
`genericPoints_mem_dense_open_of_finiteComponents`: with finitely many components, a generic
point lies in every dense open set, since the complement of the union of the other
components is a nonempty open set with closure that component.

Well-definedness of the local ring is handled by comparison rather than by a choice-free
construction. `genericLocalRing` is the stalk at the chosen representative on the schematic
locus; every other schematic chart at the point factors through the schematic locus by
maximality of the latter, and the factorization is an open immersion, so its stalk map is an
isomorphism. `exists_coherentChartStalkIso` assembles those isomorphisms into a family which
is the identity on the distinguished chart and compatible with refinements, and
`exists_genericLocalRingMap` is the same analysis for a morphism.

## References

* [Stacks Project, Tag 0ACV](https://stacks.math.columbia.edu/tag/0ACV)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
-/
