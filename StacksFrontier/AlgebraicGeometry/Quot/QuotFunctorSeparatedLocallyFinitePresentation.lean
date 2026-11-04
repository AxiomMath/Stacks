module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismFlatCover
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.ChartLimitLiftCriterion

/-!
# `Quot_{F/X/B} ⟶ B` is separated and locally of finite presentation (Stacks 0DM3, staged)

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation and `F` a quasi-coherent
`𝒪_X`-module, the standing data `AlgebraicGeometry.Space.QuotSituation` of Stacks 09TR. Stacks
0DM3 asserts that `Quot_{F/X/B} ⟶ B` is separated and, when `F` is of finite presentation, that it
is also locally of finite presentation.

Both clauses are read on the Quot presheaf itself, whose sections live one universe above the site,
with étale charts taken through `CategoryTheory.uliftYoneda`. This is the form of the separation
clause already registered for Stacks 0DM3,
`AlgebraicGeometry.Space.QuotSituation.isSeparatedULift_quotSitePresheafToBase`. It presupposes no
model of the Quot presheaf in the universe of the site. By
`QuotSitePresheafModel.holdsOnEveryEtaleChartULift_quotSitePresheafToBase_iff`
the lfp clause in this form is equivalent to local finite presentation of `M ⟶ B` for any model
`M`.

## The argument for the lfp clause

The source cites the second clause of Stacks 09TU. The argument here goes through limits instead
(compare Stacks 0CM6 and 0CMY). The Quot functor lifts quotients along cofiltered limits of affine
schemes: if `T = lim T_i`, a quotient of `F_T` in `Quot_{F/X/B}(T)` lies over a point of `B`
coming from a stage `T_i`, then it is the pullback of a member of `Quot_{F/X/B}(T_j)` over a later
stage, lying over the same point. This is the hypothesis `hlift` below. From it, every étale chart
square of `Quot_{F/X/B} ⟶ B` is locally of finite presentation by
`holdsOnEveryEtaleChartULift_locallyOfFinitePresentation_of_exists_stage_lift`,
which needs no algebraicity of `Quot_{F/X/B}`.

## Status

The two declarations below are **staged and unregistered**. Their one hypothesis `hlift` is the
lifting property above, for `F` of finite presentation. It is the content of
`AlgebraicGeometry.Space.QuotSituation.exists_stage_quotientPullback_eq` (file
`StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorLimitPreserving.lean`). That lemma
is stated through systems of test schemes over a stage; `hlift` is its reading on sections
of the Quot presheaf. Given that lemma, `hlift` is discharged and
both clauses become theorems with no hypothesis beyond `F` of finite presentation.

A route through Stacks 082Q and Stacks 08K2 instead was examined and not taken. The standing
situation of Stacks 084W, `AlgebraicGeometry.Space.MorphismDescentSystem`, is indexed by a directed
preorder and carries the size bound `#I < cof(cutoff)` as a field, whereas the chart criterion
quantifies over arbitrary cofiltered index categories in `Type u`, so 08K2 in that form does not
apply to the systems that arise.

## Main results

* `QuotSituation.isLocallyOfFinitePresentationULift_quotSitePresheafToBase_of_exists_stage_lift`:
  the lfp clause of Stacks 0DM3, from `hlift`.
* `QuotSituation.isSeparatedULift_and_isLocallyOfFinitePresentationULift_quotSitePresheafToBase`:
  both clauses of Stacks 0DM3 together, from `hlift`.

## References

* [Stacks Project, Tag 0DM3](https://stacks.math.columbia.edu/tag/0DM3)
* [Stacks Project, Tag 0DM2](https://stacks.math.columbia.edu/tag/0DM2)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 0CM6](https://stacks.math.columbia.edu/tag/0CM6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : QuotSituation B S hS)

/-- **Stacks 0DM3, the lfp clause, staged.** If `F` is of finite presentation, then
`Quot_{F/X/B} ⟶ B` is locally of finite presentation: the morphism of schemes underlying every
commuting square of étale charts of the Quot presheaf over `B` is locally of finite presentation.

Hypothesis `hlift`: for `F` of finite presentation, the Quot functor lifts quotients along
cofiltered limits `T = lim T_i` of affine schemes of the site. A section `x` of the Quot presheaf
over `T` lying over the restriction of a point `y` of `B` at a stage `T_i` is the restriction of a
section over a later stage `T_j` lying over the restriction of `y`. This is the content of
`QuotSituation.exists_stage_quotientPullback_eq`; this declaration takes it as a hypothesis and
is unregistered. -/
theorem isLocallyOfFinitePresentationULift_quotSitePresheafToBase_of_exists_stage_lift
    (hlift : D.F.IsFinitePresentationOnSite →
      ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
        (E : I ⥤ BigFppfOver B S hS) (c : Cone E),
        IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) →
        (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i))) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) →
        ∀ (x : D.quotSitePresheaf.obj (op c.pt)) (i : I) (y : D.Y.obj.obj (op (E.obj i))),
          (D.quotSitePresheafToBase.app (op c.pt) x).down = D.Y.obj.map (c.π.app i).op y →
          ∃ (j : I) (g : j ⟶ i) (z : D.quotSitePresheaf.obj (op (E.obj j))),
            (D.quotSitePresheafToBase.app (op (E.obj j)) z).down =
                D.Y.obj.map (E.map g).op y ∧
              D.quotSitePresheaf.map (c.π.app j).op z = x)
    (hF : D.F.IsFinitePresentationOnSite) :
    IsLocallyOfFinitePresentationULift.{u + 1} B S hS D.quotSitePresheafToBase :=
  holdsOnEveryEtaleChartULift_locallyOfFinitePresentation_of_exists_stage_lift B S hS
    D.quotSitePresheafToBase (hlift hF)

/-- **Stacks 0DM3, both clauses together, staged.** The morphism `Quot_{F/X/B} ⟶ B` is separated,
and if `F` is of finite presentation it is also locally of finite presentation.

The separation clause is the registered
`AlgebraicGeometry.Space.QuotSituation.isSeparatedULift_quotSitePresheafToBase` (Stacks 0DM2) and
holds with no hypothesis. The lfp clause is
`QuotSituation.isLocallyOfFinitePresentationULift_quotSitePresheafToBase_of_exists_stage_lift`,
whose hypothesis `hlift` is the content of `QuotSituation.exists_stage_quotientPullback_eq`;
this declaration takes that hypothesis and is unregistered. -/
theorem isSeparatedULift_and_isLocallyOfFinitePresentationULift_quotSitePresheafToBase
    (hlift : D.F.IsFinitePresentationOnSite →
      ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
        (E : I ⥤ BigFppfOver B S hS) (c : Cone E),
        IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) →
        (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i))) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) →
        ∀ (x : D.quotSitePresheaf.obj (op c.pt)) (i : I) (y : D.Y.obj.obj (op (E.obj i))),
          (D.quotSitePresheafToBase.app (op c.pt) x).down = D.Y.obj.map (c.π.app i).op y →
          ∃ (j : I) (g : j ⟶ i) (z : D.quotSitePresheaf.obj (op (E.obj j))),
            (D.quotSitePresheafToBase.app (op (E.obj j)) z).down =
                D.Y.obj.map (E.map g).op y ∧
              D.quotSitePresheaf.map (c.π.app j).op z = x) :
    IsSeparatedULift.{u + 1} B S hS D.quotSitePresheafToBase ∧
      (D.F.IsFinitePresentationOnSite →
        IsLocallyOfFinitePresentationULift.{u + 1} B S hS D.quotSitePresheafToBase) :=
  ⟨D.isSeparatedULift_quotSitePresheafToBase,
    D.isLocallyOfFinitePresentationULift_quotSitePresheafToBase_of_exists_stage_lift hlift⟩

end AlgebraicGeometry.Space.QuotSituation

end
