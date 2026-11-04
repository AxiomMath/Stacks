module

public import StacksFrontier.CategoryTheory.Sites.AbelianPullbackExact.FibreInclusion
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInclusion

/-!
# Exactness of extension from a simplicial component, in case (B)

In case (B) of the simplicial-site situation of Stacks 09WE the total category is the covariant
Grothendieck construction of the simplicial diagram of categories, and the component inclusion is
the fibre inclusion `CategoryTheory.Grothendieck.ι` in the degree concerned. So
`Stacks.Sites.AbelianPullback.weaklyInitial_structuredArrow_fibreInclusion` applies and the
pullback of abelian sheaves along the component inclusion is left exact, with no hypothesis
beyond those carried by `CategoryTheory.CocontinuousSimplicialSite`.

This is case (B) of the exactness clause of Stacks 09WG, and the argument does not extend to
case (A): there the total category is the contravariant Grothendieck construction, the summand of
the comma category over a simplex map `ψ` is `StructuredArrow W u_ψ` for the transition functor
`u_ψ`, and that has no initial object unless `u_ψ` has a left adjoint.

## Main results

* `Stacks.Sites.AbelianPullback.preservesFiniteLimits_sheafPullback_componentFunctor_cocontinuous`
  and `.preservesMonomorphisms_sheafPullback_componentFunctor_cocontinuous`: in case (B) the
  pullback of abelian sheaves along the component inclusion is left exact.

## Implementation notes

The statements are not instances. Their subject is the component inclusion of a
`CategoryTheory.SimplicialSiteSituation` whose case field is `Sum.inr`, so an instance would not
fire for a situation held abstractly, and declaring one would make goals stated for such a
situation fail with the instance apparently present.

The general fibre-inclusion statement
`Stacks.Sites.AbelianPullback.preservesMonomorphisms_sheafPullback_fibreInclusion` is not used,
and the criterion is applied to the comma lemma again here, because that statement has the base
of the diagram of categories in the same universe as the fibres, while the base here is
`SimplexCategoryᵒᵖ`, which lives in `Type 0`. The Grothendieck construction of a diagram indexed
by `SimplexCategoryᵒᵖ` with values in `Cat.{u, u}` is a small category of universe `u`, but the
general statement cannot say so without a universe inequality.

In case (A) the component inclusion is not a morphism of sites, so
`Stacks.Sites.AbelianPullback.preservesMonomorphisms_sheafPullback_of_isMorphismOfSites` does not
apply to it either: `Functor.IsMorphismOfSites` requires the set-valued pullback to preserve
finite limits, and `g_{n!}` does not preserve the terminal object, since
`g_{n!}(*)(m, W) = {ψ : n ⟶ m}`; Stacks 09WG(4) likewise claims only finite **connected** limits
for `g_{n!}`. Case (A) goes through the direct-sum formula of Stacks 09WG(6) instead, and is
proved, with coefficients in `Ab.{u}`, as
`CategoryTheory.SimplicialSiteSituation.componentLowerShriek_exactFunctor`.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe uA u

namespace Stacks.Sites.AbelianPullback

variable (Cs : CocontinuousSimplicialSite.{u}) (n : SimplexCategory)
  (A : Type uA) [Category.{u} A] [Abelian A] [HasColimitsOfSize.{u, u} A] [AB5OfSize.{u, u} A]
  [HasSheafify (⟨Sum.inr Cs⟩ : SimplicialSiteSituation.{u}).totalTopology A]

/-- The comma categories of the component inclusion in case (B) satisfy the two conditions of
Stacks 002X after passing to opposites: each is a disjoint union, over the morphisms of the
simplex category concerned, of categories with an initial object. -/
theorem spanAndCoequalizerOp_componentFunctor_cocontinuous :
    SpanAndCoequalizerOp (SimplicialSiteSituation.componentFunctor
      (⟨Sum.inr Cs⟩ : SimplicialSiteSituation.{u}) n) :=
  forall_and.1 fun _ => span_and_coequalizer_op_of_weaklyInitial fun x =>
    weaklyInitial_structuredArrow_fibreInclusion (F := Cs.underlying) (b := op n) x

/-- **Stacks 09WG, exactness clause, case (B).** The pullback of sheaves with values in an
abelian category with exact filtered colimits along the inclusion of a simplicial component into
the total site preserves finite limits, when the simplicial-site situation is the cocontinuous
one. -/
theorem preservesFiniteLimits_sheafPullback_componentFunctor_cocontinuous :
    PreservesFiniteLimits
      ((SimplicialSiteSituation.componentFunctor
            (⟨Sum.inr Cs⟩ : SimplicialSiteSituation.{u}) n).sheafPullback A
        ((⟨Sum.inr Cs⟩ : SimplicialSiteSituation.{u}).componentTopology n)
        (⟨Sum.inr Cs⟩ : SimplicialSiteSituation.{u}).totalTopology) :=
  preservesFiniteLimits_sheafPullback_of_span_and_coequalizer _ A _ _
    (spanAndCoequalizerOp_componentFunctor_cocontinuous Cs n)

/-- **Stacks 09WG, exactness clause, case (B).** The pullback of abelian sheaves along the
inclusion of a simplicial component into the total site preserves monomorphisms, when the
simplicial-site situation is the cocontinuous one. -/
theorem preservesMonomorphisms_sheafPullback_componentFunctor_cocontinuous :
    ((SimplicialSiteSituation.componentFunctor
          (⟨Sum.inr Cs⟩ : SimplicialSiteSituation.{u}) n).sheafPullback A
        ((⟨Sum.inr Cs⟩ : SimplicialSiteSituation.{u}).componentTopology n)
        (⟨Sum.inr Cs⟩ : SimplicialSiteSituation.{u}).totalTopology).PreservesMonomorphisms := by
  have := preservesFiniteLimits_sheafPullback_componentFunctor_cocontinuous Cs n A
  infer_instance

end Stacks.Sites.AbelianPullback

end
