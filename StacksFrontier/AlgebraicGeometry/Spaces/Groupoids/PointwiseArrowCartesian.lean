module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointwiseFibreFullFaithful
public import StacksFrontier.CategoryTheory.FiberedCategory.GrothendieckArrowCancellation

/-!
# Arrows of the groupoid of points, read after a strongly cartesian morphism of the quotient stack

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space over a scheme
`S` of a big fppf site, and let `[U/R]` be its quotient stack. An arrow `δ` of the groupoid of
points of `G` at a test object `T` gives a vertical morphism of `[U/R]` between the two presented
objects, and the two presented objects have a chosen cartesian lift along any `χ : V ⟶ T`.

This file proves that two arrows `δ₁`, `δ₂` of the groupoid of points at `T` induce the same
morphism after a strongly cartesian morphism over `χ` exactly when the two corresponding sections
of the arrow space `R` agree after restriction along `χ`.

Both directions are used in the comparison of quotient stacks after enlarging the big site. The
one that reads a hypothesis about `[U/R]` as a statement about sections of `R` needs the
faithfulness of the 1-morphism from the pointwise groupoid fibration, which is part (2) of
Stacks 044X read on all of `[U/R]`; the converse one needs nothing beyond the composition law of
the pointwise groupoid fibration.

## Main results

* `Deformation.GroupoidInFunctors.evaluationMap_map_eq_iff`: two arrows of an evaluated groupoid
  have the same image under the transport along `f` exactly when the two corresponding sections of
  the arrow functor agree after restriction along `f`.
* `AlgebraicGeometry.Stack.faithful_pointwiseToQuotientStack`: the 1-morphism from the pointwise
  groupoid fibration to the quotient stack is faithful.
* `AlgebraicGeometry.Stack.pointwiseToQuotientStack_comp_ι_map_eq_iff`: the comparison of the two
  induced morphisms of `[U/R]` after a strongly cartesian morphism over `χ`, in terms of sections
  of the arrow space.

## Implementation notes

The presenting pseudofunctor of the pointwise groupoid fibration is written out in full rather
than named: its fibre over `T` is reached through `CategoryTheory.Functor.toPseudofunctor'` and the
groupoid-to-category inclusion, and a name for the composite would not be unfolded where the
statements of `CategoryTheory.presheafOfGroupoids` are matched against it. For the same reason the
identification of its restriction functor with `Deformation.evaluationMap` is recorded as a
separate `rfl` lemma, proved with the unfolding attributes in scope, and used in term mode.

## References

* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Deformation

namespace Deformation.GroupoidInFunctors

universe v u w

/-- **Two arrows of an evaluated groupoid are identified by the transport along `f` exactly when
the two sections of the arrow functor that represent them agree after restriction along `f`.** -/
theorem evaluationMap_map_eq_iff {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) {T T' : C} (f : T ⟶ T')
    {x y : G.Evaluation T} (δ₁ δ₂ : x ⟶ y) :
    (evaluationMap G f).map δ₁ = (evaluationMap G f).map δ₂ ↔
      G.arrows.map f (G.evaluationArrowEquiv T x y δ₁).1 =
        G.arrows.map f (G.evaluationArrowEquiv T x y δ₂).1 :=
  ⟨fun h => (evaluationMap_map_arrow G f δ₁).symm.trans
      ((congrArg (fun t => (G.evaluationArrowEquiv T' _ _ t).1) h).trans
        (evaluationMap_map_arrow G f δ₂)),
    fun h => (G.evaluationArrowEquiv T' _ _).injective (Subtype.ext
      ((evaluationMap_map_arrow G f δ₁).trans (h.trans (evaluationMap_map_arrow G f δ₂).symm)))⟩

end Deformation.GroupoidInFunctors

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bs : AlgebraicSpaces C S hS}

/-- **The 1-morphism from the pointwise groupoid fibration to the quotient stack is faithful.**
It is faithful on every fibre by part (2) of Stacks 044X, hence faithful, and the universe lift it
is composed with is an equivalence. -/
theorem faithful_pointwiseToQuotientStack (G : GroupoidInAlgebraicSpaces C S hS Bs) :
    (pointwiseToQuotientStack G).Faithful := by
  have h1 : (toQuotientStack G).Faithful :=
    Functor.faithful_of_faithful_fiberFunctorOfCompEq (isFibredOneMorphism_toQuotientStack G)
      (fun U => (fullyFaithful_fiberFunctor_toQuotientStack G U).some.faithful)
  exact Functor.Faithful.comp _ _

section Restriction

attribute [local implicit_reducible] Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc BasedCategory.ofFunctor
  Grpd.forgetToCat Grpd.of

/-- The restriction functor of the presenting pseudofunctor of the pointwise groupoid fibration is
the transport of the groupoid of points. -/
theorem pointwisePseudofunctor_map_toFunctor (G : GroupoidInAlgebraicSpaces C S hS Bs)
    {T V : BigFppfOver C S hS} (χ : V ⟶ T) :
    ((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor'.map χ.op.toLoc).toFunctor =
      evaluationMap G.toGroupoidInFunctors χ.op := rfl

end Restriction

/-- **Two arrows of the groupoid of points at `T` induce the same morphism of `[U/R]` after a
strongly cartesian morphism over `χ : V ⟶ T` exactly when the two sections of the arrow space
that represent them agree after restriction along `χ`.**

The strongly cartesian morphism may be replaced by the chosen cartesian lift of `χ` in the
pointwise groupoid fibration, because the 1-morphism to `[U/R]` carries that lift to a strongly
cartesian morphism and is faithful; the chosen lift then cancels in the Grothendieck construction
against the restriction functor, which is the transport of the groupoid of points. -/
theorem pointwiseToQuotientStack_comp_ι_map_eq_iff (G : GroupoidInAlgebraicSpaces C S hS Bs)
    {T V : BigFppfOver C S hS} {a a' : G.toGroupoidInFunctors.Evaluation (op T)}
    (δ₁ δ₂ : a ⟶ a') (χ : V ⟶ T) {z : (quotientStack G).obj}
    (μ : z ⟶ (pointwiseToQuotientStack G).obj ⟨T, a⟩)
    (hμ : (quotientStack G).p.IsStronglyCartesian χ μ) :
    μ ≫ (pointwiseToQuotientStack G).map
          ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' T).map δ₁) =
        μ ≫ (pointwiseToQuotientStack G).map
          ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' T).map δ₂) ↔
      G.arrows.obj.map χ.op (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) a a' δ₁).1 =
        G.arrows.obj.map χ.op (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) a a' δ₂).1 := by
  refine Iff.trans (Functor.map_comp_eq_iff_of_isStronglyCartesian
    (isFibredOneMorphism_pointwiseToQuotientStack G) (faithful_pointwiseToQuotientStack G)
    (CoGrothendieck.cartesianLift (F := (evaluationGroupoidFunctor
      G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') a χ)
    (CoGrothendieck.isStronglyCartesian_homCartesianLift (F := (evaluationGroupoidFunctor
      G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor') a χ) μ hμ _ _) ?_
  refine Iff.trans (CoGrothendieck.cartesianLift_comp_ι_map_eq_iff
    (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor') (a := a) (a' := a') χ δ₁ δ₂) ?_
  refine Iff.trans (Iff.of_eq ?_) (GroupoidInFunctors.evaluationMap_map_eq_iff
    G.toGroupoidInFunctors χ.op δ₁ δ₂)
  exact congrArg (fun K : G.toGroupoidInFunctors.Evaluation (op T) ⥤
      G.toGroupoidInFunctors.Evaluation (op V) => K.map δ₁ = K.map δ₂)
    (pointwisePseudofunctor_map_toFunctor G χ)

end AlgebraicGeometry.Stack

end
