module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ExceptionalConormalNonzero
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ExceptionalCurveFieldTransport
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupOntoExceptionalCurve
public import StacksCore.Tactic.StacksAttribute

/-!
# The exceptional-curve dichotomy at a blowup square

Consider a commuting square of integral regular surfaces whose bottom edge `f : W ⟶ A` is proper
and birational and whose vertical edges are the blowups of `W` and `A` at closed points `w` and
`a` with `f w = a`. This file proves `Stacks.ResolutionOfSurfaces.PointBlowupDichotomy`: the
exceptional curve of the blowup of `W` either collapses to a point under the top edge, or maps
isomorphically onto the exceptional curve of the blowup of `A`, both curves are exceptional curves
of the first kind over a common field, and the induced map on conormal sheaves is nonzero. This is
the dichotomy of step 3 of [Stacks, Tag 0C5R].

## Main results

* `Stacks.ResolutionOfSurfaces.map_genericPoint_of_isIso`: an isomorphism of integral schemes
  carries the generic point to the generic point.
* `Stacks.ResolutionOfSurfaces.subsingleton_pointExceptionalCurve_of_isIso`: if the blowup at a
  closed point is an isomorphism, its exceptional curve has at most one point.
* `Stacks.ResolutionOfSurfaces.pointBlowupDichotomy`: the dichotomy of step 3 of
  [Stacks, Tag 0C5R].

## Implementation notes

When the local ring of `W` at `w` is one-dimensional the blowup at `w` is an isomorphism, its
exceptional curve is a subsingleton, and the collapsing alternative holds trivially; so the
dichotomy needs no dimension hypothesis at `w`.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H)
* [Stacks Project, Tag 0C5J](https://stacks.math.columbia.edu/tag/0C5J)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### Two small transport facts -/

/-- An isomorphism of integral schemes carries the generic point to the generic point. -/
public theorem map_genericPoint_of_isIso {Z W : Scheme.{u}} [AlgebraicGeometry.IsIntegral Z]
    [AlgebraicGeometry.IsIntegral W] (γ : Z ⟶ W) [IsIso γ] :
    γ.base (genericPoint Z) = genericPoint W := by
  have h1 : γ.base (genericPoint Z) ⤳ genericPoint W := by
    obtain ⟨z, hz⟩ := (Scheme.homeoOfIso (asIso γ)).surjective (genericPoint W)
    have hz' : γ.base z = genericPoint W := hz
    rw [← hz']
    exact (genericPoint_specializes z).map γ.continuous
  exact (h1.antisymm (genericPoint_specializes _)).eq

/-- If the blowup at a closed point is an isomorphism, its exceptional curve has at most one
point. -/
public theorem subsingleton_pointExceptionalCurve_of_isIso {W : Scheme.{u}} {w : W}
    (hw : IsClosed ({w} : Set W)) (hiso : IsIso (pointBlowUpToBase hw)) :
    Subsingleton (pointExceptionalCurve hw).subscheme := by
  have hinj : Function.Injective (pointBlowUpToBase hw).base :=
    (Scheme.homeoOfIso (asIso (pointBlowUpToBase hw))).injective
  refine ⟨fun z₁ z₂ => (pointExceptionalCurve hw).subschemeι.isEmbedding.injective (hinj ?_)⟩
  rw [blowUpToBase_subschemeι_pointExceptionalCurve hw z₁,
    blowUpToBase_subschemeι_pointExceptionalCurve hw z₂]

/-! ### The top edge of a blowup square -/

/-- The top edge of a commuting square over blowups of integral regular surfaces at closed points
is proper when the bottom edge is. -/
private theorem isProper_of_comp_eq_pointBlowUpToBase_comp {A W : Scheme.{u}}
    (hA : IsIntegralRegularSurface A) (hW : IsIntegralRegularSurface W) {f : W ⟶ A}
    (hf : IsProper f) {a : A} (ha : IsClosed ({a} : Set A)) {w : W} (hw : IsClosed ({w} : Set W))
    (g' : pointBlowUp hw ⟶ pointBlowUp ha)
    (hsq : g' ≫ pointBlowUpToBase ha = pointBlowUpToBase hw ≫ f) : IsProper g' := by
  have := hA.isIntegral
  have := hA.isNoetherian
  have := hW.isIntegral
  have := hW.isNoetherian
  have hcomp : IsProper (pointBlowUpToBase hw ≫ f) :=
    MorphismProperty.comp_mem _ _ _ (inferInstance : IsProper (pointBlowUpToBase hw)) hf
  exact isProper_of_comp_pointBlowUpToBase ha hcomp g' hsq

/-- The top edge of a commuting square over blowups of integral regular surfaces at closed points
is birational when the bottom edge is. -/
private theorem isBirational_of_comp_eq_pointBlowUpToBase_comp {A W : Scheme.{u}}
    (hA : IsIntegralRegularSurface A) (hW : IsIntegralRegularSurface W) {f : W ⟶ A}
    (hbf : IsBirational f) {a : A} (ha : IsClosed ({a} : Set A)) {w : W}
    (hw : IsClosed ({w} : Set W)) (g' : pointBlowUp hw ⟶ pointBlowUp ha)
    (hsq : g' ≫ pointBlowUpToBase ha = pointBlowUpToBase hw ≫ f) : IsBirational g' := by
  have := hA.isIntegral
  have := hA.isNoetherian
  have := hW.isIntegral
  have := hW.isNoetherian
  have := (isIntegralRegularSurface_blowUp_vanishingIdeal w hw hW).isIntegral
  have hcomp : IsBirational (pointBlowUpToBase hw ≫ f) :=
    (isBirational_blowUpToBase _
      (vanishingIdeal_singleton_ne_bot hW.topologicalKrullDim_eq w hw)).comp hbf
  exact isBirational_of_comp_pointBlowUpToBase hA.topologicalKrullDim_eq ha hcomp g' hsq

/-- The exceptional curve of the blowup of an integral regular surface at a closed point with
two-dimensional local ring is an exceptional curve of the first kind. -/
private theorem exists_isExceptionalCurveOfFirstKind_pointExceptionalCurve {W : Scheme.{u}}
    (hW : IsIntegralRegularSurface W) {w : W} (hw : IsClosed ({w} : Set W))
    (hdim : ringKrullDim (W.presheaf.stalk w) = 2) :
    ∃ e : projectiveLineProj (IsLocalRing.ResidueField (W.presheaf.stalk w)) ≅
        (pointExceptionalCurve hw).subscheme,
      (pointExceptionalCurve hw).IsExceptionalCurveOfFirstKind
        (IsLocalRing.ResidueField (W.presheaf.stalk w)) e :=
  Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal w hw
    (AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hW.isRegular w) hdim

/-- The local ring of the blowup of an integral regular surface at a closed point with
two-dimensional local ring, taken at the generic point of the exceptional curve, is a discrete
valuation ring. -/
private theorem isDiscreteValuationRing_stalk_genericPoint_pointExceptionalCurve {W : Scheme.{u}}
    (hW : IsIntegralRegularSurface W) {w : W} (hw : IsClosed ({w} : Set W))
    (hdimw : ringKrullDim (W.presheaf.stalk w) = 2)
    [AlgebraicGeometry.IsIntegral (pointBlowUp hw)]
    [AlgebraicGeometry.IsIntegral (pointExceptionalCurve hw).subscheme] :
    IsDiscreteValuationRing ((pointBlowUp hw).presheaf.stalk
      ((pointExceptionalCurve hw).subschemeι.base
        (genericPoint (pointExceptionalCurve hw).subscheme))) := by
  have := hW.isIntegral
  have := hW.isNoetherian
  have hW' : IsIntegralRegularSurface (pointBlowUp hw) :=
    isIntegralRegularSurface_blowUp_vanishingIdeal w hw hW
  obtain ⟨e, -⟩ := exists_isExceptionalCurveOfFirstKind_pointExceptionalCurve hW hw hdimw
  exact isDiscreteValuationRing_stalk_of_isRegular hW'.isRegular
    (coheight_subschemeι_genericPoint_eq_one hW'.topologicalKrullDim_eq.le
      (topologicalKrullDim_eq_one_of_iso_projectiveLineProj _ e)
      (subschemeι_pointExceptionalCurve_ne_genericPoint hW hw hdimw _))

/-! ### The dichotomy -/

/-- If the blowup at `w` is an isomorphism, the exceptional curve collapses under `g'`. -/
private theorem exceptionalCurveDichotomy_of_isIso_pointBlowUpToBase {A W : Scheme.{u}} {a : A}
    (ha : IsClosed ({a} : Set A)) [AlgebraicGeometry.IsIntegral (pointBlowUp ha)] {w : W}
    (hw : IsClosed ({w} : Set W)) (hiso : IsIso (pointBlowUpToBase hw))
    (g' : pointBlowUp hw ⟶ pointBlowUp ha) :
    ExceptionalCurveDichotomy A (pointBlowUp hw) a ha (pointExceptionalCurve hw) g' := by
  have := subsingleton_pointExceptionalCurve_of_isIso hw hiso
  rcases isEmpty_or_nonempty ((pointExceptionalCurve hw).subscheme : Type u) with hemp | ⟨⟨z₀⟩⟩
  · exact Or.inl ⟨genericPoint (pointBlowUp ha), fun z => (hemp.false z).elim⟩
  · exact Or.inl ⟨g'.base ((pointExceptionalCurve hw).subschemeι.base z₀),
      fun z => by rw [Subsingleton.elim z z₀]⟩

/-- The exceptional-curve dichotomy at a commuting blowup square whose two blown-up points have
two-dimensional local rings. -/
private theorem exceptionalCurveDichotomy_of_ringKrullDim_stalk_eq_two {A W : Scheme.{u}}
    (hA : IsIntegralRegularSurface A) (hW : IsIntegralRegularSurface W) {f : W ⟶ A}
    (hf : IsProper f) (hbf : IsBirational f) {a : A} (ha : IsClosed ({a} : Set A))
    (hdima : ringKrullDim (A.presheaf.stalk a) = 2) {w : W} (hw : IsClosed ({w} : Set W))
    (hdimw : ringKrullDim (W.presheaf.stalk w) = 2) (hwa : f.base w = a)
    (g' : pointBlowUp hw ⟶ pointBlowUp ha)
    (hsq : g' ≫ pointBlowUpToBase ha = pointBlowUpToBase hw ≫ f) :
    ExceptionalCurveDichotomy A (pointBlowUp hw) a ha (pointExceptionalCurve hw) g' := by
  have := hA.isIntegral
  have := hA.isNoetherian
  have := hW.isIntegral
  have := hW.isNoetherian
  have hA' : IsIntegralRegularSurface (pointBlowUp ha) :=
    isIntegralRegularSurface_blowUp_vanishingIdeal a ha hA
  have hW' : IsIntegralRegularSurface (pointBlowUp hw) :=
    isIntegralRegularSurface_blowUp_vanishingIdeal w hw hW
  have := hA'.isIntegral
  have := hA'.isNoetherian
  have := hW'.isIntegral
  obtain ⟨e, hE⟩ := exists_isExceptionalCurveOfFirstKind_pointExceptionalCurve hW hw hdimw
  obtain ⟨e'', hE''⟩ := exists_isExceptionalCurveOfFirstKind_pointExceptionalCurve hA ha hdima
  have hEint : AlgebraicGeometry.IsIntegral (pointExceptionalCurve hw).subscheme :=
    isIntegral_subscheme_of_iso_projectiveLineProj _ _ e
  have hE'int : AlgebraicGeometry.IsIntegral (pointExceptionalCurve ha).subscheme :=
    isIntegral_subscheme_of_iso_projectiveLineProj _ _ e''
  rcases exists_isIso_pointExceptionalCurveMap_or_const hA hW f hf hbf ha hdima hw hdimw hwa
    g' hsq with hconst | ⟨γ, hγsq, hγiso⟩
  · exact Or.inl hconst
  obtain ⟨U', hU'⟩ := exists_maximal_isomorphism_open g'
  have hgen : γ.base (genericPoint (pointExceptionalCurve hw).subscheme) =
      genericPoint (pointExceptionalCurve ha).subscheme := map_genericPoint_of_isIso γ
  have hstalk := isIso_stalkMap_genericPoint hA'.isRegular hA'.topologicalKrullDim_eq.le
    (topologicalKrullDim_eq_one_of_iso_projectiveLineProj _ e'')
    (subschemeι_pointExceptionalCurve_ne_genericPoint hA ha hdima _) g'
    (isProper_of_comp_eq_pointBlowUpToBase_comp hA hW hf ha hw g' hsq)
    (isBirational_of_comp_eq_pointBlowUpToBase_comp hA hW hbf ha hw g' hsq) U' hU' γ hγsq hgen
  have := isDiscreteValuationRing_stalk_genericPoint_pointExceptionalCurve hW hw hdimw
  have hjimm : IsImmersion ((pointExceptionalCurve hw).subschemeι ≫ g') := by
    rw [← hγsq]
    infer_instance
  exact Or.inr ⟨IsLocalRing.ResidueField (W.presheaf.stalk w), inferInstance,
    pointExceptionalCurve ha, e, e ≪≫ asIso γ, hE,
    Scheme.IdealSheafData.isExceptionalCurveOfFirstKind_of_iso (e ≪≫ asIso γ) e'' hE'',
    preimage_singleton_subset_range_exceptionalIdeal ha, γ, rfl,
    (pointExceptionalCurve hw).subschemeι ≫ g', hjimm, hγsq, rfl,
    Stacks.Conormal.ne_zero_immersionConormalSheafMap_of_isIso_stalkMap hE''.1 γ g'
      hγsq.symm hgen hstalk (IsDiscreteValuationRing.not_a_field _)⟩

/-- The exceptional-curve dichotomy `Stacks.ResolutionOfSurfaces.PointBlowupDichotomy` of step 3
of [Stacks, Tag 0C5R] holds. -/
public theorem pointBlowupDichotomy : PointBlowupDichotomy.{u} := by
  intro A W f a ha w hw g' hA hW hf hbf haU hwa hsq
  have := hA.isIntegral
  have := hA.isNoetherian
  have := hW.isIntegral
  have := hW.isNoetherian
  obtain ⟨U, hU⟩ := exists_maximal_isomorphism_open f
  have hdima : ringKrullDim (A.presheaf.stalk a) = 2 :=
    ringKrullDim_stalk_eq_two_of_notMem_isomorphism_open hA f hbf U hU ha (haU U hU)
  have := (isIntegralRegularSurface_blowUp_vanishingIdeal a ha hA).isIntegral
  rcases isIso_pointBlowUpToBase_or_ringKrullDim_stalk_eq_two hW w hw with hiso | hdimw
  · exact exceptionalCurveDichotomy_of_isIso_pointBlowUpToBase ha hw hiso g'
  · exact exceptionalCurveDichotomy_of_ringKrullDim_stalk_eq_two hA hW hf hbf ha hdima hw hdimw
      hwa g' hsq

end Stacks.ResolutionOfSurfaces

end
