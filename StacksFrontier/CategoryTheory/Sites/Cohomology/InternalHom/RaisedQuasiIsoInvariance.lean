module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.QuasiIsoInvariance

/-! # Stacks 0A95 over a ringed site with large objects

Stacks 0A95 — the quasi-isomorphism invariance of the internal Hom complex — is proved over a
`AlgebraicGeometry.RingedSite.{c, u, u}` whose underlying category is essentially `u`-small, by
`AlgebraicGeometry.RingedSite.homMap_quasiIso` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.QuasiIsoInvariance`. Objects in an
arbitrary universe `c`, morphisms, structure sheaf and modules in `u`.

Nothing is declared here. The statement is proved at this generality in
`QuasiIsoInvariance.lean`, which this does not make circular — the inputs it needs, Stacks 08FI
over a site with large objects and the locality of quasi-isomorphy, both sit below it — and the
names in the namespace `AlgebraicGeometry.RingedSite.Raised` are kept resolvable here as
aliases of the canonical declarations, so that a simp lemma or a rewrite about one applies to
the other. An `export`
introduces no new constant: `AlgebraicGeometry.RingedSite.Raised.homMap_quasiIso` and
`AlgebraicGeometry.RingedSite.homMap_quasiIso` denote one declaration.

## Main results

* `AlgebraicGeometry.RingedSite.Raised.homMap_quasiIso`: an alias of
  `AlgebraicGeometry.RingedSite.homMap_quasiIso`, Stacks 0A95 over a ringed site with large
  objects.
* `AlgebraicGeometry.RingedSite.Raised.homMap_quasiIso_of_collapsed`: an alias of
  `AlgebraicGeometry.RingedSite.homMap_quasiIso_of_collapsed`, the specialisation of that
  statement to a ringed site whose three universes coincide, which shows that nothing was
  weakened in freeing the universes.

## References

* [Stacks Project, Tag 0A95](https://stacks.math.columbia.edu/tag/0A95)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public section

namespace AlgebraicGeometry.RingedSite.Raised

export AlgebraicGeometry.RingedSite (quasiIso_of_sheafification_quasiIso homMap_quasiIso
  homMap_quasiIso_of_collapsed)

end AlgebraicGeometry.RingedSite.Raised

end
