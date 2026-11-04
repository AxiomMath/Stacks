module

public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInjective
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentExact

/-!
# Restriction to a simplicial component preserves K-injectivity (Stacks 09WH)

Stacks 09WH says that a K-injective complex of abelian sheaves on the total site of a
simplicial site restricts to a K-injective complex on every component site. The proof is the
adjoint criterion `CochainComplex.isKInjective_mapHomologicalComplex_of_exact` (Stacks 08BJ):
restriction to the component is right adjoint to lower shriek, and lower shriek is exact by
Stacks 09WG (7), so restriction carries K-injective complexes to K-injective complexes.

Exactness of lower shriek is therefore the only input, and it is available for an arbitrary
simplicial-site situation as
`CategoryTheory.SimplicialSiteSituation.componentLowerShriek_exactFunctor`, so the statement
below holds for an arbitrary situation unconditionally and makes no case distinction.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isKInjective_componentRestriction`: **Stacks 09WH**,
  second assertion, for an arbitrary simplicial-site situation.
* `CategoryTheory.CocontinuousSimplicialSite.isKInjective_componentRestriction`: its case-(B)
  instance, retained under that name.

## Implementation notes

The coefficients are the abelian groups of the site's own universe, as for the sibling assertion
`CategoryTheory.SimplicialSiteSituation.injective_componentRestriction`. That is no restriction
for this assertion, whose source statement is itself about sheaves of abelian groups of the
site's universe; only the first assertion of the tag is stated at an independent coefficient
universe.

Additivity of the restriction functor is `rfl` on addition of sheaf morphisms, so it is proved
here rather than synthesized. The `HasSheafify` instances for `Ab`-valued sheaves on the
component and total topologies are already available from the imports and are not restated.

## References

* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory.SimplicialSiteSituation

universe u

/-- **Stacks 09WH**, second assertion: restriction of a K-injective complex of abelian sheaves
on the total site of a simplicial-site situation to a component is K-injective.

Restriction to the component is right adjoint to lower shriek, which is exact by
`CategoryTheory.SimplicialSiteSituation.componentLowerShriek_exactFunctor`, and
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact` is the Stacks 08BJ step. Exactness
is available for an arbitrary situation, so no case distinction is made.

Coefficients sit at the site universe, as in the first assertion and for the same reason. -/
@[stacks 09WH "component_k_injective"]
theorem isKInjective_componentRestriction (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory)
    (I : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((S.restrictAb n).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) := by
  have hex := componentLowerShriek_exactFunctor S n
  let v := sheafPullbackConstruction.sheafPullback (componentFunctor S n) Ab.{u}
    (S.componentTopology n) S.totalTopology
  let adj := sheafPullbackConstruction.sheafAdjunctionContinuous (componentFunctor S n) Ab.{u}
    (S.componentTopology n) S.totalTopology
  have : PreservesFiniteLimits v := hex.1
  have : PreservesFiniteColimits v := hex.2
  have : v.Additive := Functor.additive_of_preserves_binary_products v
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ v adj I

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.CocontinuousSimplicialSite

open CategoryTheory.SimplicialSiteSituation

universe u

/-- **Stacks 09WH**, second assertion, in case (B): the case-(B) instance of
`CategoryTheory.SimplicialSiteSituation.isKInjective_componentRestriction`, retained under this
name. -/
theorem isKInjective_componentRestriction (C : CocontinuousSimplicialSite.{u})
    (n : SimplexCategory)
    (I : CochainComplex
      (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((((componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u})
        n).sheafPushforwardContinuous Ab.{u}
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
  SimplicialSiteSituation.isKInjective_componentRestriction _ n I

end CategoryTheory.CocontinuousSimplicialSite

end
