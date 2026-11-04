module

public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Topologies.Zariski.SmallSiteExtension
import StacksCore.Tactic.StacksAttribute

/-!
# Čech complexes of disjoint-union refinements for a sheaf on the small Zariski site

An abelian sheaf on the small Zariski site of a scheme `S` extends to the big Zariski site of
`S` along the inclusion of the open subschemes, and the Čech comparison of Stacks 03FI part (3)
holds for that extension: replacing a finite family of morphisms over `S` by the single
morphism from the coproduct of its members does not change the Čech complex.

## Main results

* `AlgebraicGeometry.isIso_cechComplexMap_coproductRefinement_smallZariski` is Stacks 03FI
  part (3) in case (c), the small Zariski site.

## Implementation notes

A finite disjoint union of opens of `S` is not an open of `S`, so the one-member family
`{∐ Uᵢ → U}` of part (1) has no object in the small Zariski site, and the statement in case (c)
has to be read on the big Zariski site through
`AlgebraicGeometry.SmallZariski.extension`, which
`AlgebraicGeometry.SmallZariski.isIso_extension_unit` pins as an extension of the given sheaf.

## References

* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 020T](https://stacks.math.columbia.edu/tag/020T)
* [Stacks Project, Tag 020Z](https://stacks.math.columbia.edu/tag/020Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 03FI part (3), case (c).** For an abelian sheaf on the small Zariski
site of a scheme, read on the big Zariski site through its extension, the refinement of a finite
family of morphisms by the single morphism from the coproduct of its members induces an
isomorphism of Čech complexes. -/
@[stacks 03FI "part (3), case (c)"]
theorem isIso_cechComplexMap_coproductRefinement_smallZariski (S : Scheme.{u})
    (F : Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{max (u + 1) v})
    {T : Over S} (E : PreZeroHypercover.{w} T) [Finite E.I₀] :
    IsIso (Stacks.CechSite.cechComplexMap E
      (PreZeroHypercover.singleton.{w} (Sigma.desc E.f))
      (Stacks.CechSite.coproductRefinement E)
      ((SmallZariski.extension.{u, v} S F).obj ⋙
        AddCommGrpCat.uliftFunctor.{w, max (u + 1) v})) :=
  isIso_cechComplexMap_coproductRefinement_over S (Scheme.zariskiTopology.over S) le_rfl E
    (SmallZariski.extension.{u, v} S F).obj (SmallZariski.extension.{u, v} S F).property

end AlgebraicGeometry
