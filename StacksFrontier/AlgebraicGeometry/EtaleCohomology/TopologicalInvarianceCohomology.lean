module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.UniversalHomeomorphismInvariance

/-!
# Topological invariance of étale cohomology

Let `f : X ⟶ Y` be a universal homeomorphism of schemes — for instance the closed immersion cut
out by a nilpotent sheaf of ideals. Then the small étale topoi of `X` and `Y` are equivalent, and
étale cohomology agrees in every degree: for every abelian sheaf `F` on the small étale site of
`Y`, restriction along `f` is bijective on `H^q` for all `q`.

Both statements hold with no hypothesis beyond `UniversalHomeomorphism f`. The inverse-image
functor is an equivalence as soon as base change is a dense subsite inclusion, and for a universal
homeomorphism it is: of the four conditions for a dense subsite, cover-density is Stacks 04DW and
the other three hold for any universal homeomorphism. This is a different route from the one the
Stacks Project takes, which deduces the same conclusions from the equivalence of étale categories.

## Main results

* `Stacks.EtaleCohomology.smallEtaleInverseImage_isEquivalence_of_universalHomeomorphism` —
  **the small étale topoi of `X` and `Y` are equivalent**, part (2) of Stacks 03SI.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_universalHomeomorphism` —
  **étale cohomology agrees in every degree**, part (3) of Stacks 03SI.
* `Stacks.EtaleCohomology.etaleAbelianInverseImage_isEquivalence_of_universalHomeomorphism` — the
  same equivalence on abelian sheaves, which is what carries part (3).

## Implementation notes

Part (1) of Stacks 03SI, that the two étale *sites* are isomorphic, is not formalized here. It
asserts that base change is an equivalence of the étale categories, which is Stacks 04DZ. A dense
subsite inclusion is strictly weaker than an isomorphism of sites, so the dense subsite statement
is not part (1); it is however all that parts (2) and (3) require.

The results `Stacks.EtaleCohomology.smallEtaleInverseImage_isEquivalence_of_isDenseSubsite`,
`Stacks.EtaleCohomology.etaleAbelianInverseImage_isEquivalence_of_isDenseSubsite` and
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_isDenseSubsite` carry the dense
subsite inclusion as an instance hypothesis. The declarations here supply it from
`Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism`, and so need only
`UniversalHomeomorphism f`.

## References

* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f]

/-- **Stacks 03SI, part (2).** For a universal homeomorphism `f : X ⟶ Y` the small étale topoi of
`X` and `Y` are equivalent: the canonical inverse-image functor on sheaves of types is an
equivalence of categories. -/
@[stacks 03SI "part (2), equivalence of the small étale topoi"]
theorem smallEtaleInverseImage_isEquivalence_of_universalHomeomorphism :
    (smallEtaleInverseImage.{u, v} f).IsEquivalence :=
  have := isDenseSubsite_of_universalHomeomorphism f
  smallEtaleInverseImage_isEquivalence_of_isDenseSubsite.{u, v} f

/-- For a universal homeomorphism the inverse image on abelian sheaves of the small étale sites is
an equivalence. This is the form in which part (3) of Stacks 03SI is proved. -/
theorem etaleAbelianInverseImage_isEquivalence_of_universalHomeomorphism
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] :
    (etaleAbelianInverseImage.{u, v} f).IsEquivalence :=
  have := isDenseSubsite_of_universalHomeomorphism f
  etaleAbelianInverseImage_isEquivalence_of_isDenseSubsite.{u, v} f

/-- **Stacks 03SI, part (3).** For a universal homeomorphism `f : X ⟶ Y` étale cohomology agrees
in every degree: restriction along `f` is bijective on `H^q` of every abelian sheaf on the small
étale site of `Y`. -/
@[stacks 03SI "part (3), agreement of étale cohomology"]
theorem etaleCohomologyRestrictionMap_bijective_of_universalHomeomorphism
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f F q) :=
  have := isDenseSubsite_of_universalHomeomorphism f
  etaleCohomologyRestrictionMap_bijective_of_isDenseSubsite.{u, v, w} f F q

end Stacks.EtaleCohomology

end
