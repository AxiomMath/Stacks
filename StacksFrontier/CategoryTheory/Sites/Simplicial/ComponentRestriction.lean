module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInclusion

/-!
# Restriction of a total-site sheaf to a simplicial component

In the simplicial-site situation of Stacks 09WE, the inclusion of the component in simplicial
degree `n` into the total category is continuous, so precomposition with it restricts a sheaf on
the total site to a sheaf on that component.

This module sits downstream of the component inclusion, because restriction is precomposition
with `CategoryTheory.SimplicialSiteSituation.componentFunctor`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.inclusion`: the component inclusion, named for use as
  the functor that restriction precomposes with.
* `CategoryTheory.SimplicialSiteSituation.restrict`: restriction of a total-site sheaf to the
  component in a given simplicial degree.

## Main results

* `CategoryTheory.SimplicialSiteSituation.restrict_obj_obj`: restriction does not change
  sections.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Limits

universe u w

namespace CategoryTheory

namespace SimplicialSiteSituation

/-- The inclusion of a component in the total category. -/
abbrev inclusion (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    S.component n ⥤ S.totalCategory :=
  componentFunctor S n

/-- Restriction of a total-site sheaf to a component, by precomposition. -/
def restrict (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    Sheaf S.totalTopology (Type w) ⥤ Sheaf (S.componentTopology n) (Type w) :=
  (inclusion S n).sheafPushforwardContinuous (Type w) (S.componentTopology n) S.totalTopology

/-- Restriction of a total-site sheaf of sets to a component preserves finite limits: it is the
direct image along a continuous functor, hence a right adjoint. -/
instance restrict_preservesFiniteLimits (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) : PreservesFiniteLimits (S.restrict.{u, u} n) := by
  have : PreservesLimits (S.restrict.{u, u} n) :=
    Functor.preservesLimits_sheafPushforwardContinuous (S.inclusion n)
      (Type u) (S.componentTopology n) S.totalTopology
  infer_instance

/-- Restriction does not change sections. -/
@[simp] theorem restrict_obj_obj (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)
    (F : Sheaf S.totalTopology (Type w)) (U : (S.component n)ᵒᵖ) :
    ((S.restrict n).obj F).obj.obj U = F.obj.obj ((S.inclusion n).op.obj U) := rfl

end SimplicialSiteSituation

end CategoryTheory

add_to_stacks 09WF "restriction to a simplicial degree"
  CategoryTheory.SimplicialSiteSituation.restrict

end
