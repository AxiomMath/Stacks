module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleLowerShriekProjectionFormula

/-!
# The map of Stacks 08JF along an étale morphism of algebraic spaces is invertible

For an étale morphism `a : X' ⟶ X` of algebraic spaces and `M`, `K` in `D(𝒪_X)`, the map
`La^*R𝓗om(M, K) ⟶ R𝓗om(La^*M, La^*K)` of Stacks 08JF is an isomorphism: extension by zero
`a_!` is left adjoint to `a^*` and satisfies the projection formula
(`AlgebraicGeometry.Space.isIso_etaleModuleLowerShriekProjectionMap`), so the map is the
comparison of internal Homs along `a^*` of
`isIso_smallEtaleDerivedPullbackSheafHomMap_of_isIso_etaleModuleLowerShriekProjectionMap`.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_of_isEtale`.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/- The standard model of the derived category: the derived functors this file uses (derived
pullback, pushforward, tensor product and internal Hom on ringed sites and topoi) are stated
on it, so the statements here must be too. -/
attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The map of Stacks 08JF along an étale morphism is invertible.** For `a : X' ⟶ X` étale
and `M`, `K` in `D(𝒪_X)`, `La^*R𝓗om(M, K) ⟶ R𝓗om(La^*M, La^*K)` is an isomorphism. -/
theorem isIso_smallEtaleDerivedPullbackSheafHomMap_of_isEtale {X X' : AlgebraicSpaces B S hS}
    (a : X' ⟶ X) (ha : IsEtale B S hS a.hom)
    (M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    IsIso (smallEtaleDerivedPullbackSheafHomMap a M K) :=
  isIso_smallEtaleDerivedPullbackSheafHomMap_of_isIso_etaleModuleLowerShriekProjectionMap a ha
    (fun A M => isIso_etaleModuleLowerShriekProjectionMap a ha A M) M K

end AlgebraicGeometry.Space

end
