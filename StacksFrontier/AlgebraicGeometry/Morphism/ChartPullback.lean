module

public import StacksFrontier.AlgebraicGeometry.Morphism.Glue
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Basic

/-!
# The charts of the source are cartesian for Tag 07ZG's morphism

Let `ψ : A ⟶ B` be a homomorphism of quasi-coherent graded `𝒪_S`-algebras, let `U(ψ)` be the open
of `Proj_S(B)` on which it induces a morphism, and let

`r_ψ : U(ψ) ⟶ Proj_S(A)`

be the morphism of Tag 07ZG. For an affine open `U` of the base, the chart
`Proj Γ(U, A) ⟶ Proj_S(A)` is the inverse image of `U` along the structure morphism of
`Proj_S(A)`, and `r_ψ` is a morphism over `S`; hence the inverse image of that chart along `r_ψ`
is the part of `U(ψ)` lying over `U`, which is `U(ψ) ⊓ q⁻¹(U)`, and the canonical identification
of that open with the absolute domain of definition `U(ψ_U) ⊆ Proj Γ(U, B)` carries the induced
morphism to the absolute morphism `U(ψ_U) ⟶ Proj Γ(U, A)` of Tag 01MY.

This file proves that square is cartesian, and deduces the affine-local transfer principle: a
property of morphisms of schemes which is Zariski-local at the target holds for `r_ψ` as soon as
it holds for every absolute morphism of Tag 01MY.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.isPullback_relativeMapDomain_inf`: the piece
  `U(ψ) ⊓ q⁻¹(U)` of `U(ψ)`, identified with `U(ψ_U)`, is the inverse image of the chart of
  `Proj_S(B)` over `U`.
* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.isPullback_chart_relativeMapHom`: **the chart of
  `Proj_S(A)` over an affine open of the base pulls back along `r_ψ` to the absolute morphism of
  Tag 01MY.**
* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.of_forall_chart`: **the transfer principle.** A
  property local at the target which holds for all the absolute morphisms of Tag 01MY holds for
  `r_ψ`.

## The route

The cartesian square of the second result is obtained from the chart square of `Proj_S(A)` over
`U` — which is cartesian by Tag 01NQ — by cancelling it off the bottom of the composite square
over the inclusion `U ⊆ S`. The composite square is in turn the vertical pasting of the chart
square of `Proj_S(B)` over `U` with the first result, after the two vertical composites have been
rewritten using that the absolute morphism of Tag 01MY and `r_ψ` are morphisms over `U`
respectively over `S`.

The first result needs nothing about `r_ψ`: both vertical arrows are inclusions of opens, so by
`AlgebraicGeometry.IsOpenImmersion.isPullback` it suffices that the square commutes and that the
chart pulls `U(ψ)` back to `U(ψ_U)`, which is Tag 07ZG's affine-local description of the open.

The transfer principle then reads the restriction of `r_ψ` over the range of each chart of
`Proj_S(A)` through that cartesian square, the ranges of the charts covering `Proj_S(A)`.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

namespace Stacks.AlgebraicGeometry.Tag07ZGMorphism

universe u

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-- **The piece of `U(ψ)` over an affine open `U` of the base is the inverse image of `U(ψ)` under
the chart of `Proj_S(B)` over `U`.** Both vertical arrows are inclusions of opens, so this is
exactly Tag 07ZG's affine-local description of `U(ψ)`: the chart pulls `U(ψ)` back to the absolute
domain of definition `U(ψ_U)`. -/
public theorem isPullback_relativeMapDomain_inf (U : AffineOpen S) :
    IsPullback
      ((chartPieceIso ψ U).hom ≫
        (relativeProj B).scheme.homOfLE
          (inf_le_left : ψ.relativeMapDomain ⊓ ((relativeProj B).toBase ⁻¹ᵁ U.1) ≤ _))
      (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
      ψ.relativeMapDomain.ι ((relativeProj B).chart U.1 U.2) := by
  refine AlgebraicGeometry.IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [Category.assoc, Scheme.homOfLE_ι, chartPieceIso, Iso.trans_hom, Category.assoc,
      Scheme.isoOfEq_hom_ι, Scheme.Hom.isoImage_hom_ι]
  · rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
    exact ψ.chart_preimage_relativeMapDomain U.1 U.2

/-- The composite square over the inclusion of an affine open `U` of the base: the piece of `U(ψ)`
over `U`, identified with `U(ψ_U)`, is the inverse image of `U` in `U(ψ)`. This is the vertical
pasting of the chart square of `Proj_S(B)` over `U` with
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.isPullback_relativeMapDomain_inf`. -/
public theorem isPullback_relativeMapHom_comp_toBase (U : AffineOpen S) :
    IsPullback
      ((chartPieceIso ψ U).hom ≫
        (relativeProj B).scheme.homOfLE
          (inf_le_left : ψ.relativeMapDomain ⊓ ((relativeProj B).toBase ⁻¹ᵁ U.1) ≤ _))
      (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) ≫
        projInclusionToOpen A U.1 U.2)
      (relativeMapHom ψ ≫ (relativeProj A).toBase) U.1.ι := by
  rw [mapHom_comp_projInclusionToOpen ψ U.1 U.2, relativeMapHom_comp_toBase ψ]
  exact (isPullback_relativeMapDomain_inf ψ U).paste_vert
    ((relativeProj B).chart_isPullback U.1 U.2)

/-- **The chart of `Proj_S(A)` over an affine open `U` of the base pulls back along `r_ψ` to the
absolute morphism of Tag 01MY.** The chart is the inverse image of `U` and `r_ψ` is a morphism
over the base, so its inverse image along `r_ψ` is the part of `U(ψ)` lying over `U`, namely
`U(ψ) ⊓ q⁻¹(U)`, which `chartPieceIso` identifies with `U(ψ_U)`. -/
public theorem isPullback_chart_relativeMapHom (U : AffineOpen S) :
    IsPullback
      ((chartPieceIso ψ U).hom ≫
        (relativeProj B).scheme.homOfLE
          (inf_le_left : ψ.relativeMapDomain ⊓ ((relativeProj B).toBase ⁻¹ᵁ U.1) ≤ _))
      (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
      (relativeMapHom ψ) ((relativeProj A).chart U.1 U.2) :=
  IsPullback.of_bot (isPullback_relativeMapHom_comp_toBase ψ U)
    ((Category.assoc _ _ _).trans (chartPieceIso_hom_comp_homOfLE_comp_relativeMapHom ψ U))
    ((relativeProj A).chart_isPullback U.1 U.2)

/-- **The affine-local transfer principle for Tag 07ZG's morphism.** A property of morphisms of
schemes which is Zariski-local at the target holds for `r_ψ` as soon as it holds for every
absolute morphism `U(ψ_U) ⟶ Proj Γ(U, A)` of Tag 01MY: the ranges of the charts of `Proj_S(A)`
cover it, and over each of them `r_ψ` restricts to that absolute morphism. -/
public theorem of_forall_chart {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    (h : ∀ U : AffineOpen S,
      P (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))) :
    P (relativeMapHom ψ) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun U : AffineOpen S => ((relativeProj A).chart U.1 U.2).opensRange)
    (ProjBundleSurjection.iSup_opensRange_chart_eq_top (relativeProj A)) fun U => ?_
  have h₂ := isPullback_chart_relativeMapHom ψ U
  have h₁ : IsPullback (pullback.fst (relativeMapHom ψ) ((relativeProj A).chart U.1 U.2))
      (pullback.snd (relativeMapHom ψ) ((relativeProj A).chart U.1 U.2)) (relativeMapHom ψ)
      ((relativeProj A).chart U.1 U.2) := IsPullback.of_hasPullback _ _
  have e₁ : Arrow.mk (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)) ≅
      Arrow.mk (pullback.snd (relativeMapHom ψ) ((relativeProj A).chart U.1 U.2)) :=
    Arrow.isoMk (h₂.isoIsPullback _ _ h₁) (Iso.refl _)
  have e₂ := morphismRestrictOpensRange (relativeMapHom ψ) ((relativeProj A).chart U.1 U.2)
  exact (MorphismProperty.arrow_mk_iso_iff (P := P) (e₁.trans e₂.symm)).mp (h U)

end Stacks.AlgebraicGeometry.Tag07ZGMorphism

end
