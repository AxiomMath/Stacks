module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms

/-!
# A sheaf over `X` that is an affine scheme over every affine étale chart is affine over `X`

Let `X` be an algebraic space and `π : F ⟶ X` a morphism from a presheaf on the big fppf site
whose base change along every affine étale chart `V ⟶ X` is represented by an affine scheme.
When `F` is an algebraic space, `π` is affine.

This is the affineness half of the recognition principle used to build the relative spectrum
`\underline{Spec}_X(𝒜)` of a quasi-coherent `𝒪_X`-algebra chart by chart (Stacks 081W): the
chart-level spectra are affine schemes over the affine étale charts of `X`.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_of_affineChart`: under the chart hypothesis, a morphism
  from an algebraic space `F` to `X` is affine.

## Implementation notes

An affine étale morphism `g : V ⟶ X` from an affine object of the site is an affine étale chart
of `X`, so the hypothesis is item (3) of
`AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace`.

## References

* [Stacks Project, Tag 03WE](https://stacks.math.columbia.edu/tag/03WE)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The chart hypothesis: the base change of `π` along every affine étale chart `V ⟶ X` is
represented by an affine scheme `W`, with `p : W ⟶ F` and `q : W ⟶ V` forming a cartesian square
over `π`. -/
abbrev AffineOnAffineCharts {X : AlgebraicSpaces B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (π : F ⟶ X.1) : Prop :=
  ∀ V : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 V →
    ∃ (W : BigAffineFppf B S hS) (p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ F)
      (q : (BigAffineFppf.inclusion B S hS).obj W ⟶ V.obj.left),
      IsPullback p (yoneda.map q) π V.obj.hom

/-- **A morphism from an algebraic space to `X` whose base change along every affine étale chart
of `X` is represented by an affine scheme is affine.**  An étale morphism into `X` from an affine
object of the site is an affine étale chart of `X`, so this is item (3) of
`AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace`. -/
theorem isAffineHom_of_affineChart {X : AlgebraicSpaces B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hFalg : IsAlgebraicSpace B S hS F) (π : F ⟶ X.1)
    (h : AffineOnAffineCharts B S hS π) : IsAffineHom B S hS π := by
  refine ((isAffineHom_tfae_of_isAlgebraicSpace B S hS π hFalg X.2).out 2 3).2 ?_
  intro V g hg
  let V' : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk g, (isEtale_iff_presheaf_of_yoneda B S hS g).1 hg⟩
  have hV' : IsAffineChart B S hS X.1 V' := V.property
  obtain ⟨W, p, q, hpb⟩ := h V' hV'
  exact ⟨W, p, q, hpb⟩

end AlgebraicGeometry.Space

end
