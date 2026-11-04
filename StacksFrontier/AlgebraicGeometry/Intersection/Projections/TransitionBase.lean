module

public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySubscheme
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.ProjectionConeDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionProper
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base `X × Y` of the incidence correspondence of Tag 0B1S

The incidence correspondence `T = {(x, y, [g]) : x ∈ X, y ∈ Y, r_g(x) = y}` of Tag 0B1S is taken
over the product of the two closed subvarieties, which is
`AlgebraicGeometry.ProjectiveSpaceOfModule.prodOfClosed`. Three properties of that base are what
the analysis of `T` runs on, and they are collected here:

* it is **irreducible**, over an algebraically closed field — this is what the source's
  "`T` is irreducible" rests on, and it is where the product structure of the base does the work
  that no openness or flatness statement about `T ⟶ X × Y` is then needed for;
* its **dimension** is `dim X + dim Y`, by Tag 0B2M, which is
  `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_prodOfClosed`;
* it is **proper** over the ground field, which is what makes the projection `T ⟶ 𝐏` proper and
  hence the bad locus closed
  (`AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_image_transitionVarietyToPar`).

Irreducibility of a product of two irreducible schemes over an algebraically closed field is
available in the library only for a `pullback` of two structure morphisms whose
`GeometricallyIrreducible` instances are in hand; the two steps turning `IsIrreducible X` into
that instance — the reduced closed subscheme on `X` is homeomorphic to `X`, and an irreducible
scheme over a separably closed field is geometrically irreducible — appear inline in the proof of
`AlgebraicGeometry.ProjectiveSpaceOfModule.isIrreducible_constantFamily`, which is about a product
with a *line*. The first of them is separated out here as
`AlgebraicGeometry.ProjectiveSpaceOfModule.irreducibleSpace_closedSubschemeOf` so that it is not
written a third time.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.irreducibleSpace_closedSubschemeOf`: the reduced
  closed subscheme on an irreducible closed subset is irreducible.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.irreducibleSpace_prodOfClosed`: the product of two
  irreducible closed subvarieties is irreducible.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isProper_prodOfClosedToProdTwo_comp_toSpec`: it is
  proper over the ground field, which is the hypothesis
  `AlgebraicGeometry.ProjectiveSpaceOfModule.isProper_transitionVarietyToPar` asks of a base.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
* [Stacks Project, Tag 020J](https://stacks.math.columbia.edu/tag/020J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  (X Y : Set (projectiveSpaceOfModule k V))

/-- **The reduced closed subscheme on an irreducible closed subset is irreducible**, being
homeomorphic to the subset along its closed immersion. -/
public theorem irreducibleSpace_closedSubschemeOf (hXc : IsClosed X) (hXirr : IsIrreducible X) :
    IrreducibleSpace (closedSubschemeOf k V X hXc) := by
  refine ((closedSubschemeOfι k V X hXc).isClosedEmbedding.isEmbedding.toHomeomorph
    ).irreducibleSpace_iff.mpr ?_
  rw [range_closedSubschemeOfι]
  exact Subtype.irreducibleSpace hXirr

/-- The structure morphism of the reduced closed subscheme on an irreducible closed subset is
geometrically irreducible, over an algebraically closed field. -/
private theorem geometricallyIrreducible_closedSubschemeOfToSpec [IsAlgClosed k] (hXc : IsClosed X)
    (hXirr : IsIrreducible X) : GeometricallyIrreducible (closedSubschemeOfToSpec k V X hXc) :=
  haveI := irreducibleSpace_closedSubschemeOf k V X hXc hXirr
  geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k _ _

/-- **The product of two irreducible closed subvarieties of `𝐏(V)` is irreducible**, over an
algebraically closed field. Both factors are geometrically irreducible, being irreducible over a
separably closed field, and a product one of whose factors is geometrically irreducible and
universally open over an irreducible base is irreducible. -/
@[ega "IV 4.5.8" "(i), special case"]
public theorem irreducibleSpace_prodOfClosed [IsAlgClosed k] (hXc : IsClosed X)
    (hYc : IsClosed Y) (hXirr : IsIrreducible X) (hYirr : IsIrreducible Y) :
    IrreducibleSpace (prodOfClosed k V X Y hXc hYc) := by
  have hXs := irreducibleSpace_closedSubschemeOf k V X hXc hXirr
  have hYs := irreducibleSpace_closedSubschemeOf k V Y hYc hYirr
  have h1 := geometricallyIrreducible_closedSubschemeOfToSpec k V X hXc hXirr
  have h2 := geometricallyIrreducible_closedSubschemeOfToSpec k V Y hYc hYirr
  rw [prodOfClosed]
  infer_instance

/-- **The product of two closed subvarieties is proper over the ground field.** This is the
hypothesis `AlgebraicGeometry.ProjectiveSpaceOfModule.isProper_transitionVarietyToPar` asks of a
base, so with it the projection of the incidence correspondence over `X × Y` to the parameter
space is proper. -/
public theorem isProper_prodOfClosedToProdTwo_comp_toSpec [FiniteDimensional k V] [Nontrivial V]
    (hXc : IsClosed X) (hYc : IsClosed Y) :
    IsProper (prodOfClosedToProdTwo k V X Y hXc hYc ≫ prodTwoToSpec k V) := by
  have hmap : prodOfClosedToProdTwo k V X Y hXc hYc ≫
      pullback.fst (projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k V) =
      pullback.fst (closedSubschemeOfToSpec k V X hXc)
          (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc :=
    pullback.lift_fst _ _ _
  have hfst : IsProper (pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have hfac : prodOfClosedToProdTwo k V X Y hXc hYc ≫ prodTwoToSpec k V =
      pullback.fst (closedSubschemeOfToSpec k V X hXc)
          (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfToSpec k V X hXc := by
    rw [prodTwoToSpec, ← Category.assoc, hmap]
    exact Category.assoc _ _ _
  rw [hfac]
  exact MorphismProperty.comp_mem _ _ _ hfst inferInstance

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
