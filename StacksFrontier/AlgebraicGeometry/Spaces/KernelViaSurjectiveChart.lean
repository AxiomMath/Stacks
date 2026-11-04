module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleCounitFork

/-!
# The kernel of the structure map, computed on one surjective chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and let `V` be an étale scheme chart of `Y`.  The structure map
`f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8 sends a regular function on `V` to the family of its
pullbacks to the étale scheme charts of `X` above the base-changed chart `X ×_Y V` of
Stacks 03G2, part (4), so by `AlgebraicGeometry.Space.mem_ker_structureSharp_iff` its kernel
over `V` is the intersection of the kernels of those chartwise pullbacks, one for each chart.

This file shows that a *single* chart suffices, as soon as that chart covers `X ×_Y V`: if
`j₀` is an étale scheme chart of `X` over `X ×_Y V` whose morphism to `X ×_Y V` is surjective
on points, the kernel of the structure map over `V` is already the kernel of the pullback to
`j₀`.  No representability of `f` is needed.

## Main results

* `AlgebraicGeometry.Space.injective_ran_map_of_isSurjective`: restriction of the right Kan
  extension of the structure sheaf of `X` along a surjective morphism from an étale scheme chart
  is injective on sections.
* `AlgebraicGeometry.Space.injective_chartProjection_of_isSurjective`: the chart projection of
  the sections of the direct image to an étale scheme chart of `X` that is surjective over
  `X ×_Y V` is injective.
* `AlgebraicGeometry.Space.ker_structureSharp_eq_of_isSurjective`: the kernel of
  `f♯ : 𝒪_Y ⟶ f_*𝒪_X` on sections over an étale scheme chart `V` of `Y` is the kernel of
  pullback of regular functions to any single étale scheme chart of `X` that is surjective over
  `X ×_Y V`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] comparisonFunctor_full comparisonFunctor_faithful

/-! ### Restriction along a surjective chart -/

section Restriction

/-- The right Kan extension of the structure sheaf of `X` along the comparison functor of
Stacks 03G1 is a sheaf on the spaces-étale site of `X`. -/
theorem isSheaf_ran_structureSetSheaf (X : AlgebraicSpaces B S hS) :
    Presheaf.IsSheaf (SpacesEtale.topology B S hS X)
      ((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj) :=
  ran_isSheaf_of_isCocontinuous (comparisonFunctor B S hS X)
    (SpacesEtale.topology B S hS X) (structureSetSheaf B S hS X)

/-- Restriction of the right Kan extension of the structure sheaf along a morphism from an
étale scheme chart that is surjective on points is injective. -/
theorem injective_ran_map_of_isSurjective (X : AlgebraicSpaces B S hS)
    {W : SpacesEtale B S hS X} {V : SmallEtale B S hS X.1}
    (g : (comparisonFunctor B S hS X).obj V ⟶ W)
    (hg : IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map g).hom) :
    Function.Injective
      (((comparisonFunctor B S hS X).op.ran.obj
        (structureSetSheaf B S hS X).obj).map g.op) := by
  obtain ⟨_, p, q, hpb⟩ := exists_etaleChart_isPullback_self B S hS X W V g
  exact (mono_iff_injective _).1 (mono_of_isLimit_fork
    (isLimitForkOfSurjectiveSingleton B S hS
      ((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj)
      (isSheaf_ran_structureSetSheaf B S hS X) hg hpb
      (Presheaf.fork_condition_of_isPullback _ hpb)))

/-- The counit of the right Kan extension along the comparison functor of Stacks 03G1 is
injective on sections over every étale scheme chart. -/
theorem injective_ranCounit_app (X : AlgebraicSpaces B S hS)
    (V : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Injective
      (((comparisonFunctor B S hS X).op.ranCounit.app
        (structureSetSheaf B S hS X).obj).app V) :=
  ((isIso_iff_bijective _).1 inferInstance).1

end Restriction

/-! ### The kernel on one surjective chart -/

section ChartKernel

variable {X Y : AlgebraicSpaces B S hS}

/-- The chart projection of the sections of the direct image is restriction along the given
morphism followed by the counit of the right Kan extension. -/
theorem chartProjection_app_eq_ranCounit_app (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (a : ((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj).obj
      (op (chartBaseChange B S hS f V))) :
    (chartProjection B S hS f V j).app (structureSetSheaf B S hS X) a =
      ((comparisonFunctor B S hS X).op.ranCounit.app
          (structureSetSheaf B S hS X).obj).app j.right
        (((comparisonFunctor B S hS X).op.ran.obj
          (structureSetSheaf B S hS X).obj).map j.hom a) :=
  chartProjection_app_apply B S hS f V j a

/-- The chart projection of the sections of the direct image over `V` to an étale scheme chart
of `X` whose morphism to `X ×_Y V` is surjective on points is injective. -/
theorem injective_chartProjection_of_isSurjective (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j₀ : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (hj₀ : IsSurjective B S hS
      ((SpacesEtale.toSpaces B S hS X).map j₀.hom.unop).hom) :
    Function.Injective
      ((chartProjection B S hS f V j₀).app (structureSetSheaf B S hS X)) :=
  fun a b hab ↦
    injective_ran_map_of_isSurjective B S hS X j₀.hom.unop hj₀
      (injective_ranCounit_app B S hS X j₀.right
        (((chartProjection_app_eq_ranCounit_app B S hS f V j₀ a).symm.trans hab).trans
          (chartProjection_app_eq_ranCounit_app B S hS f V j₀ b)))

/-- **The kernel of the structure map of Stacks 03G8 on one surjective chart.** If an étale
scheme chart `j₀` of `X` above `X ×_Y V` is surjective over `X ×_Y V`, then the kernel of
`f♯ : 𝒪_Y ⟶ f_*𝒪_X` on sections over the étale scheme chart `V` of `Y` is the kernel of
pullback of regular functions to `j₀` alone. -/
theorem ker_structureSharp_eq_of_isSurjective (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j₀ : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (hj₀ : IsSurjective B S hS
      ((SpacesEtale.toSpaces B S hS X).map j₀.hom.unop).hom) :
    RingHom.ker ((structureSharp B S hS f).hom.app (op V)).hom =
      RingHom.ker (chartPullbackRingHom B S hS f V j₀) := by
  refine le_antisymm (fun a ha ↦ (mem_ker_structureSharp_iff B S hS f V a).1 ha j₀)
    (fun a ha ↦ (mem_ker_structureSharp_iff B S hS f V a).2
      ((structureMapApp_eq_zero_iff B S hS f V a).1 ?_))
  exact injective_chartProjection_of_isSurjective B S hS f V j₀ hj₀
    ((chartProjection_structureMapApp B S hS f V j₀ a).trans
      ((RingHom.mem_ker.1 ha).trans (chartProjection_ringZeroObj B S hS f V j₀).symm))

end ChartKernel

end AlgebraicGeometry.Space

end
