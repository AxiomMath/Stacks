module

public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceExceptionalCurveGlobal
public import
 StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ExceptionalCurveOntoMap
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ExceptionalSquareChain

/-!
# The exceptional curve of the blowup either collapses or maps isomorphically

This file instantiates `ExceptionalCurveOntoMap.lean` at the square of step 3 of
[Stacks, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R): a proper birational morphism
`f : W ⟶ A` of integral Noetherian schemes regular of dimension two, a closed point `a ∈ A`, a
closed point `w ∈ W` over it, and a morphism `g'` filling in the square over the two blowups.

The conclusion is the source's dichotomy of step 3 *except for the nonvanishing of the conormal
comparison map*: either `g'` carries the exceptional curve `E` of the blowup at `w` to a single
point of the blowup at `a`, or the induced morphism `γ : E ⟶ E'` onto the exceptional curve
downstairs is an isomorphism.

## Main results

* `Stacks.ResolutionOfSurfaces.exists_isIso_pointExceptionalCurveMap_or_const` — **the dichotomy
  of step 3 at the level of the two curves**: the exceptional curve of the blowup at `w` either
  collapses under `g'`, or maps onto the exceptional curve of the blowup at `a` by an isomorphism.

## What is and is not proved

Proved here: the instantiation. Its three inputs are
`Stacks.ResolutionOfSurfaces.range_subschemeι_comp_subset_range_pointExceptionalCurve` (the
containment `g'(E) ⊆ E'`), the presentation of each exceptional curve as the projective line over
the residue field
(`Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal`), and the
fact that no point of `E'` is the generic point of the blowup at `a`, which holds because every
point of `E'` lies over `a` while the generic point lies over the generic point of `A`.

**What is still missing for `Stacks.ResolutionOfSurfaces.PointBlowupDichotomy`** is the second
alternative's remaining clause: the nonvanishing of the conormal comparison map
`γ^* 𝒞_{E'/A'} ⟶ 𝒞_{E/W'}`, together with a presentation of both curves over a *single* field
compatible with `γ`. The isomorphism `γ` produced here is what the source uses to obtain that
single field, namely `κ(w) ≅ κ(a)`; transporting
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind` from one presentation to
another is not available in the library, and neither is the nonvanishing. Every step of the
source's argument after those two is formalized; see the module documentation of
`ExceptionalSquareChain.lean`.

**No `@[stacks 0C5R]` attribute is placed here**: this is a step of the proof of that tag, not a
clause of its statement.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-- **No point of the exceptional curve is the generic point of the blowup.** Every point of the
exceptional curve lies over the point blown up, and the generic point of the blowup lies over the
generic point of the base, which is not the point blown up because its local ring is
two-dimensional. -/
public theorem subschemeι_pointExceptionalCurve_ne_genericPoint {A : Scheme.{u}}
    (hA : IsIntegralRegularSurface A) {a : A} (ha : IsClosed ({a} : Set A))
    [AlgebraicGeometry.IsIntegral (pointBlowUp ha)]
    (hdim : ringKrullDim (A.presheaf.stalk a) = 2)
    (p : (pointExceptionalCurve ha).subscheme) :
    (pointExceptionalCurve ha).subschemeι.base p ≠ genericPoint (pointBlowUp ha) := by
  have hAint := hA.isIntegral
  have hAnoe := hA.isNoetherian
  have hA' : IsIntegralRegularSurface (pointBlowUp ha) :=
    isIntegralRegularSurface_blowUp_vanishingIdeal a ha hA
  have hA'int := hA'.isIntegral
  intro hp
  have h1 : pointBlowUpToBase ha ((pointExceptionalCurve ha).subschemeι.base p) = a :=
    blowUpToBase_subschemeι_pointExceptionalCurve ha p
  have hbir : IsBirational (pointBlowUpToBase ha) :=
    isBirational_blowUpToBase _ (vanishingIdeal_singleton_ne_bot hA.topologicalKrullDim_eq a ha)
  have h2 : pointBlowUpToBase ha (genericPoint (pointBlowUp ha)) = genericPoint A := by
    simpa [genericPoints_eq_singleton, Set.bijOn_singleton] using hbir.bijOn
  rw [hp, h2] at h1
  have h3 := ringKrullDim_stalk_genericPoint_eq_zero A
  rw [h1, hdim] at h3
  norm_num at h3

/-- **The dichotomy of step 3 of [Stacks, Tag 0C5R] at the level of the two curves.** Let
`f : W ⟶ A` be a proper birational morphism of integral Noetherian schemes regular of dimension
two, let `a ∈ A` and `w ∈ W` be closed points with `f(w) = a` whose local rings are
two-dimensional, and let `g'` fill in the square over the blowups at `w` and at `a`. Then either
`g'` carries the exceptional curve `E` of the blowup at `w` to a single point, or the morphism
`γ : E ⟶ E'` onto the exceptional curve of the blowup at `a` is an isomorphism.

The containment `g'(E) ⊆ E'` is
`Stacks.ResolutionOfSurfaces.range_subschemeι_comp_subset_range_pointExceptionalCurve`, the
presentations of the two curves as projective lines are
`Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal`, and the
dichotomy itself is
`Stacks.ResolutionOfSurfaces.exists_isIso_subschemeMap_or_const`. -/
public theorem exists_isIso_pointExceptionalCurveMap_or_const {A W : Scheme.{u}}
    (hA : IsIntegralRegularSurface A) (hW : IsIntegralRegularSurface W) (f : W ⟶ A)
    (hf : IsProper f) (hbf : IsBirational f) {a : A} (ha : IsClosed ({a} : Set A))
    (hdima : ringKrullDim (A.presheaf.stalk a) = 2) {w : W} (hw : IsClosed ({w} : Set W))
    (hdimw : ringKrullDim (W.presheaf.stalk w) = 2) (hwa : f.base w = a)
    (g' : pointBlowUp hw ⟶ pointBlowUp ha)
    (hsq : g' ≫ pointBlowUpToBase ha = pointBlowUpToBase hw ≫ f) :
    (∃ y : pointBlowUp ha, ∀ t : (pointExceptionalCurve hw).subscheme,
        g'.base ((pointExceptionalCurve hw).subschemeι.base t) = y) ∨
      ∃ γ : (pointExceptionalCurve hw).subscheme ⟶ (pointExceptionalCurve ha).subscheme,
        γ ≫ (pointExceptionalCurve ha).subschemeι =
            (pointExceptionalCurve hw).subschemeι ≫ g' ∧ IsIso γ := by
  have hAint := hA.isIntegral
  have hAnoe := hA.isNoetherian
  have hALN : IsLocallyNoetherian A := hAnoe.toIsLocallyNoetherian
  have hWint := hW.isIntegral
  have hWnoe := hW.isNoetherian
  have hWLN : IsLocallyNoetherian W := hWnoe.toIsLocallyNoetherian
  have hA' : IsIntegralRegularSurface (pointBlowUp ha) :=
    isIntegralRegularSurface_blowUp_vanishingIdeal a ha hA
  have hW' : IsIntegralRegularSurface (pointBlowUp hw) :=
    isIntegralRegularSurface_blowUp_vanishingIdeal w hw hW
  have hA'int := hA'.isIntegral
  have hA'noe := hA'.isNoetherian
  have hW'int := hW'.isIntegral
  -- the two presentations as projective lines
  obtain ⟨e, -⟩ :=
    Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal w hw
      (AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hW.isRegular w) hdimw
  obtain ⟨e', -⟩ :=
    Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal a ha
      (AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hA.isRegular a) hdima
  -- properness and birationality of `g'`
  have hcompprop : IsProper (pointBlowUpToBase hw ≫ f) :=
    MorphismProperty.comp_mem _ _ _ inferInstance hf
  have hcompbir : IsBirational (pointBlowUpToBase hw ≫ f) :=
    (isBirational_blowUpToBase _
      (vanishingIdeal_singleton_ne_bot hW.topologicalKrullDim_eq w hw)).comp hbf
  have hg'prop : IsProper g' := isProper_of_comp_pointBlowUpToBase ha hcompprop g' hsq
  have hg'bir : IsBirational g' :=
    isBirational_of_comp_pointBlowUpToBase hA.topologicalKrullDim_eq ha hcompbir g' hsq
  obtain ⟨U', hU'⟩ := exists_maximal_isomorphism_open g'
  exact exists_isIso_subschemeMap_or_const _ _ e e' hA'.isRegular hA'.topologicalKrullDim_eq.le
    (subschemeι_pointExceptionalCurve_ne_genericPoint hA ha hdima) g' hg'prop hg'bir U' hU'
    (range_subschemeι_comp_subset_range_pointExceptionalCurve f ha hw hwa g' hsq)

end Stacks.ResolutionOfSurfaces

end
