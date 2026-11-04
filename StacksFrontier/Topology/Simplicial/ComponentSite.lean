module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.Topology.Simplicial.Sheaves

/-!
# Restriction of sheaves to a component of a simplicial space

For a simplicial topological space `X` and a degree `n`, the open subsets of `X_n` form the
level-`n` part of the site of simplicial opens. The resulting inclusion of sites is both
continuous and cocontinuous, and inverse image from sheaves on the total site to sheaves on the
component is restriction to that component. The identification is natural in the sheaf.

## Main definitions

* `Stacks.Topology.Simplicial.inverseImageIsoComponent`: the natural isomorphism identifying
  inverse image along the component inclusion with the component functor of the sheaf-system
  description.

## Main results

* `Stacks.Topology.Simplicial.levelFunctor_isContinuous_mk` and
  `levelFunctor_isCocontinuous_mk`: continuity and cocontinuity of the component inclusion.

## Implementation notes

The inverse image is the cocontinuous sheaf pullback of the level inclusion. Its comparison
with the component functor is a natural isomorphism rather than literal equality, since the
sheaf-system equivalence and sheafification choose categorical representatives. The statement
uses sheaves of sets in the site's universe, as in the associated morphism of topoi.

The continuity and cocontinuity statements here are the degrees `op ⦋n⦌` of the general
`Stacks.Topology.Simplicial.levelFunctor_isContinuous` and `levelFunctor_isCocontinuous`; they
are the forms in which the source states them, and they are the instances used downstream.

## References

* [Stacks Project, Tag 09W0](https://stacks.math.columbia.edu/tag/09W0)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Topology.Simplicial

/-- **Stacks 09W0.** The inclusion of the open-set site of one component into the site of
simplicial opens is continuous. -/
@[stacks 09W0 "component_site_inclusion", instance]
theorem levelFunctor_isContinuous_mk (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    (levelFunctor X (op (SimplexCategory.mk n))).IsContinuous
      (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
      (SimplicialOpen.grothendieckTopology X) :=
  levelFunctor_isContinuous X (op (SimplexCategory.mk n))

/-- **Stacks 09W0.** The inclusion of the open-set site of one component into the site of
simplicial opens is cocontinuous. -/
@[stacks 09W0 "component_site_inclusion", instance]
theorem levelFunctor_isCocontinuous_mk (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    (levelFunctor X (op (SimplexCategory.mk n))).IsCocontinuous
      (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
      (SimplicialOpen.grothendieckTopology X) :=
  levelFunctor_isCocontinuous X (op (SimplexCategory.mk n))

/-- **Stacks 09W0.** Pulling a sheaf back to a simplicial component is, naturally in that
sheaf, its component in the sheaf-system description. -/
@[stacks 09W0 "inverse_image_is_restriction"]
noncomputable def inverseImageIsoComponent
    (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    (levelFunctor X (op (SimplexCategory.mk n))).sheafPullbackCocontinuous
        (Type u) (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
        (SimplicialOpen.grothendieckTopology X) ≅
      (sheafEquivalenceSimplicialSheafSystem X (Type u)).toEquivalence.functor ⋙
        SimplicialSheafSystem.componentFunctor X (Type u)
          (op (SimplexCategory.mk n)) := by
  let v := levelFunctor X (op (SimplexCategory.mk n))
  let J := Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n)))
  let H := sheafToPresheaf J (Type u)
  letI := (fullyFaithfulSheafToPresheaf J (Type u)).full
  letI := (fullyFaithfulSheafToPresheaf J (Type u)).faithful
  exact (v.sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type u) J
      (SimplicialOpen.grothendieckTopology X)) ≪≫
    Functor.fullyFaithfulCancelRight H (by
      let K := SimplicialOpen.grothendieckTopology X
      let E := sheafEquivalenceSimplicialSheafSystem X (Type u)
      let Q := componentPresheafFunctor X (Type u)
        (op (SimplexCategory.mk n))
      exact (v.sheafPushforwardContinuousCompSheafToPresheafIso (Type u) J K) ≪≫
        (Functor.isoWhiskerRight E.underlyingPresheafIso Q).symm ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft E.toEquivalence.functor
          (E.componentIso (op (SimplexCategory.mk n))) ≪≫
        (Functor.associator _ _ _).symm)

end Stacks.Topology.Simplicial

end
