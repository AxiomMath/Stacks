module

public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageHomChartComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeSpaceDifferentialsVanishing
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverseSupplement
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.InductionSupplement
public import
  StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStepSupplement
public import StacksFrontier.AlgebraicGeometry.Size.CoveringsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedEtaleDescentSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackCompSupplement

/-!
# Maps out of an inverse image are determined by chart components on a dense family

For a morphism `f : X ⟶ Y` of algebraic spaces and a sheaf of commutative rings `𝒜` on the
small étale site of `X`, a map `φ : f⁻¹𝒪_Y ⟶ 𝒜` has *chart components*
`AlgebraicGeometry.Space.inverseImageHomChartRingHom`, ring maps `𝒪_Y(V) ⟶ 𝒜(T)` for the étale
charts `T` of `X` above `X ×_Y V`. They are compatible with shrinking `T`, and two maps whose
chart components agree on the charts `T` in the image of a cover-dense functor are equal.

## Main results

* `AlgebraicGeometry.Space.chartProjection_naturality_general`: the projections computing the
  sections of a direct image over a chart are compatible with morphisms of charts.
* `AlgebraicGeometry.Space.inverseImageHomChartRingHom_restrict`: chart components are
  compatible with shrinking the chart.
* `AlgebraicGeometry.Space.inverseImageHomChartRingHom_ext_of_isCoverDense`: the extensionality
  principle.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The projections of the limit computing the sections of a direct image over an étale chart
`V` of `Y` are compatible with morphisms of charts of `X` above `X ×_Y V`, for every sheaf of
sets. -/
theorem chartProjection_naturality_general (V : SmallEtale B S hS Y.1)
    {j₁ j₂ : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op}
    (φ : j₁ ⟶ j₂) (E : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (t : ((comparisonFunctor B S hS X).op.ran.obj E.obj).obj
      (op (chartBaseChange B S hS f V))) :
    (chartProjection B S hS f V j₂).app E t =
      E.obj.map φ.right ((chartProjection B S hS f V j₁).app E t) := by
  rw [chartProjection_app_apply_general, chartProjection_app_apply_general]
  exact (congrArg (fun k ↦ k t) (((Functor.RightExtension.mk _
    ((comparisonFunctor B S hS X).op.ranCounit.app E.obj)).coneAt
    (op (chartBaseChange B S hS f V))).w φ)).symm

variable (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})

/-- **Chart components are compatible with shrinking the chart.** -/
theorem inverseImageHomChartRingHom_restrict
    (φ : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    {T : SmallEtale B S hS X.1} (q : T ⟶ j.right.unop)
    (x : (smallEtaleRingedTopos B S hS Y).O.obj.obj (op V)) :
    inverseImageHomChartRingHom B S hS f A φ V
        (StructuredArrow.mk (Y := op T) (j.hom ≫ ((comparisonFunctor B S hS X).map q).op)) x =
      A.obj.map q.op (inverseImageHomChartRingHom B S hS f A φ V j x) := by
  rw [inverseImageHomChartRingHom_apply, inverseImageHomChartRingHom_apply]
  exact chartProjection_naturality_general f V (j₁ := j)
    (j₂ := StructuredArrow.mk (Y := op T) (j.hom ≫ ((comparisonFunctor B S hS X).map q).op))
    (StructuredArrow.homMk q.op rfl) _ _

/-- **Maps out of `f⁻¹𝒪_Y` are determined by their chart components on a dense family of
charts.** If two maps `f⁻¹𝒪_Y ⟶ 𝒜` have the same chart components on all charts of `X` in the
image of a cover-dense functor `G`, they are equal. -/
theorem inverseImageHomChartRingHom_ext_of_isCoverDense {C : Type*} [Category* C]
    (G : C ⥤ SmallEtale B S hS X.1) [G.IsCoverDense (SmallEtale.topology B S hS X.1)]
    {φ₁ φ₂ : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A}
    (h : ∀ (c : C) (V : SmallEtale B S hS Y.1)
      (a : (comparisonFunctor B S hS X).obj (G.obj c) ⟶ chartBaseChange B S hS f V) x,
      inverseImageHomChartRingHom B S hS f A φ₁ V (StructuredArrow.mk (Y := op (G.obj c)) a.op) x =
        inverseImageHomChartRingHom B S hS f A φ₂ V (StructuredArrow.mk (Y := op (G.obj c)) a.op)
          x) :
    φ₁ = φ₂ := by
  have hj : ∀ (V : SmallEtale B S hS Y.1)
      (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) x,
      inverseImageHomChartRingHom B S hS f A φ₁ V j x =
        inverseImageHomChartRingHom B S hS f A φ₂ V j x := by
    intro V j x
    refine Functor.IsCoverDense.ext G
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).obj A) _
      (fun c q ↦ ?_)
    change A.obj.map q.op _ = A.obj.map q.op _
    rw [← inverseImageHomChartRingHom_restrict f A φ₁ V j q x,
      ← inverseImageHomChartRingHom_restrict f A φ₂ V j q x]
    exact h c V ((comparisonFunctor B S hS X).map q ≫ j.hom.unop) x
  apply ((smallEtaleRingedToposHom B S hS f).toToposHom.ringAdjunction.homEquiv _ _).injective
  rw [← Iso.cancel_iso_hom_right _ _ (pushforwardRingIsoRan B S hS f A)]
  apply Sheaf.hom_ext
  ext V x
  exact chartProjection_ext_general B S hS f V.unop (fun j ↦ hj V.unop j x)

end AlgebraicGeometry.Space

end
