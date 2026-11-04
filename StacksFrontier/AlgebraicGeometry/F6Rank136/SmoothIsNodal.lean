module

public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantStalkRank
public import StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree
public import StacksFrontier.AlgebraicGeometry.FittingRank.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension

/-!
# Smooth families of curves are at-worst-nodal

A morphism of schemes smooth of relative dimension one is at-worst-nodal of relative
dimension one: its relative singular subscheme is empty, so the nodal condition holds
vacuously.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials`: the sheaf
  of relative differentials of a morphism smooth of relative dimension one is finite locally
  free of rank one.
* `AlgebraicGeometry.isEmpty_relativeSingularIdeal_subscheme_of_smoothOfRelativeDimension_one`:
  the relative singular subscheme of such a morphism is empty.
* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_of_smoothOfRelativeDimension`:
  **Stacks Project, Tag 0CD7** — a morphism smooth of relative dimension one is at-worst-nodal
  of relative dimension one.

## Implementation notes

Being at-worst-nodal of relative dimension one is being syntomic of relative dimension one
together with unramifiedness over the base of the relative singular subscheme, the closed
subscheme cut out by the first Fitting ideal of the sheaf of relative differentials. Smoothness
gives syntomicity directly, and the fibre dimension of a morphism smooth of relative dimension
`n` is `n` at every point, which settles the first half.

For the second half the singular subscheme is in fact empty. The relative differentials of a
smooth morphism are finite locally free, hence of finite type with free stalks, so their fibre
rank at a point is the rank of the stalk there; that rank is the local dimension of the fibre,
namely one. A finite locally free sheaf of constant fibre rank one is finite locally free of
rank one, and the Fitting-ideal characterization of constant rank then makes the first Fitting
ideal the unit ideal, whose closed subscheme has no points. Unramifiedness over the base is
vacuous on an empty source.

## References

* [Stacks Project, Tag 0CD7](https://stacks.math.columbia.edu/tag/0CD7)
* [Stacks Project, Tag 0C5A](https://stacks.math.columbia.edu/tag/0C5A)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 02G1.** The sheaf of relative differentials of a morphism smooth of
relative dimension one is finite locally free of rank one: it is finite locally free, and the
rank of its stalk at any point is the local dimension of the fibre there, namely one. -/
public theorem Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials
    {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials f) 1 := by
  have _ : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Scheme.Hom.relativeDifferentials f) :=
    Scheme.Hom.isFiniteLocallyFree_relativeDifferentials f
  obtain ⟨hft, hfree, -⟩ :=
    ((Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae
      (Scheme.Hom.relativeDifferentials f)).out 4 5 rfl rfl).mp hflf
  have _ := hft
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_fiberRank_eq _ 1 fun x => ?_
  rw [Scheme.Modules.fiberRank_eq_finrank_stalk (Scheme.Hom.relativeDifferentials f) x (hfree x)]
  have hdim := finrank_stalk_relativeDifferentials_eq_fiberDimensionAt f x
  rw [fiberDimensionAt_eq_of_smoothOfRelativeDimension f 1 x] at hdim
  exact_mod_cast hdim

/-- The relative singular subscheme of a morphism smooth of relative dimension one is empty:
the relative differentials are finite locally free of rank one, so their first Fitting ideal is
the unit ideal. -/
public theorem isEmpty_relativeSingularIdeal_subscheme_of_smoothOfRelativeDimension_one
    {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] :
    IsEmpty (relativeSingularIdeal f).subscheme := by
  have _ : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have _ : LocallyOfFiniteType f := by
    refine ⟨?_⟩
    intro U hU V hV e
    exact RingHom.FiniteType.of_finitePresentation (f.finitePresentation_appLE hU hV e)
  let _ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials f) 1 :=
    Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials f
  have hFit := (((finiteLocallyFreeOfRank_tfae_fittingIdeal
    (Scheme.Hom.relativeDifferentials f) 1).out 1 2 rfl rfl).mp inferInstance).2
  rw [Nat.cast_one] at hFit
  show IsEmpty (fittingIdeal (Scheme.Hom.relativeDifferentials f) 1).subscheme
  rw [hFit]
  infer_instance

/-- **Stacks Project, Tag 0CD7.** A morphism of schemes smooth of relative dimension one is
at-worst-nodal of relative dimension one: it is syntomic with one-dimensional fibres, and its
relative singular subscheme is empty, hence unramified over the base. -/
@[stacks 0CD7]
public theorem isAtWorstNodalOfRelativeDimensionOne_of_smoothOfRelativeDimension
    {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] :
    IsAtWorstNodalOfRelativeDimensionOne f := by
  let _ : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  let _ := isEmpty_relativeSingularIdeal_subscheme_of_smoothOfRelativeDimension_one f
  exact ⟨⟨syntomic_of_smooth f, fiberDimensionAt_eq_of_smoothOfRelativeDimension f 1⟩,
    ⟨fun x => isEmptyElim x⟩⟩

end AlgebraicGeometry

end
