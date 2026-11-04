module

public import StacksFrontier.CategoryTheory.Sites.AbelianPullbackExact.SimplicialComponent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentLowerShriekMono
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumNaturality.SumNaturalIso

/-!
# Exactness of the abelian lower shriek of a component inclusion, in both cases

Stacks 09WG (7) says that the lower shriek of abelian sheaves along the inclusion of a simplicial
component into the total site is exact. This file proves the monomorphism-preservation half for a
simplicial-site situation of Stacks 09WE held abstractly.

In case (B) the comma categories of the component inclusion have weakly initial objects, and the
statement is
`Stacks.Sites.AbelianPullback.preservesMonomorphisms_sheafPullback_componentFunctor_cocontinuous`.
In case (A) the sum formula of Stacks 09WG (6), given by
`Stacks.Sites.ComponentSumFormula.lanSumInclusion` and
`Stacks.Sites.ComponentSumFormula.isIso_sigmaDesc_lanSumInclusion`, reduces the statement to the
exactness of the pullback along each transition functor, which is a morphism of sites.

## Main results

* `preservesMonomorphisms_sheafPullback_componentFunctor_simplicialSite`: Stacks 09WG (7) in
  case (A).
* `preservesMonomorphisms_sheafPullback_componentFunctor`: Stacks 09WG (7) for a simplicial-site
  situation held abstractly.

## Implementation notes

The general statement is an `instance` while the case statement is a theorem: its subject is a
`CategoryTheory.SimplicialSiteSituation` whose case field is a specific constructor application,
so as an instance it would not fire for a situation held abstractly.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite

universe u

namespace Stacks.Sites.ComponentSumFormula

/-- **Stacks 09WG (7) in case (A).** The pullback of abelian sheaves along the inclusion of a
simplicial component into the total site preserves monomorphisms, when the simplicial-site
situation is the one whose transitions are morphisms of sites. -/
theorem preservesMonomorphisms_sheafPullback_componentFunctor_simplicialSite
    (Cs : SimplicialSite.{u}) (n : SimplexCategory) :
    ((SimplicialSiteSituation.componentFunctor
        (⟨Sum.inl Cs⟩ : SimplicialSiteSituation.{u}) n).sheafPullback AddCommGrpCat.{u}
      ((⟨Sum.inl Cs⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      (⟨Sum.inl Cs⟩ : SimplicialSiteSituation.{u}).totalTopology).PreservesMonomorphisms :=
  ComponentLowerShriek.preservesMonomorphisms_sheafPullback_componentFunctor_of_lanSum Cs n
    (fun m ψ => lanSumInclusion (A := AddCommGrpCat.{u}) (Cs := Cs) (m := m) (n := n) ψ)
    fun m P => isIso_sigmaDesc_lanSumInclusion (A := AddCommGrpCat.{u}) (Cs := Cs) (m := m)
      (n := n) P

/-- **Stacks 09WG (7), both cases.** The pullback of abelian sheaves along the inclusion of a
simplicial component into the total site preserves monomorphisms, for a simplicial-site situation
of Stacks 09WE held abstractly. -/
instance preservesMonomorphisms_sheafPullback_componentFunctor
    (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    ((SimplicialSiteSituation.componentFunctor S n).sheafPullback AddCommGrpCat.{u}
      (S.componentTopology n) S.totalTopology).PreservesMonomorphisms := by
  obtain ⟨Cs | Cs⟩ := S
  · exact preservesMonomorphisms_sheafPullback_componentFunctor_simplicialSite Cs n
  · exact AbelianPullback.preservesMonomorphisms_sheafPullback_componentFunctor_cocontinuous
      Cs n AddCommGrpCat.{u}

end Stacks.Sites.ComponentSumFormula

end
