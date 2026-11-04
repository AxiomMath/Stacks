module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint

/-!
# Smoothness at a point is local on the source

Smoothness at a point of the source is unchanged by passing to an open subscheme of the source
through that point.  **This file states that in the two forms a composite with an open immersion
needs**, neither of which is available for the *definition* of smoothness at a point, which
prescribes the restriction `f.resLE ⊤ U le_top` rather than the composite `U.ι ≫ f`.

## Main results

* `InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp`: smoothness at a point is the
  existence of an open neighbourhood `U` of it with `U.ι ≫ f` smooth.
* `InfinitesimalLifting.smoothAt_of_smooth_comp`: if `j` is an open immersion and `j ≫ f` is
  smooth, then `f` is smooth at every point of the image of `j`.
* `InfinitesimalLifting.SmoothAt.comp_isOpenImmersion`: if `f` is smooth at `j z` for an open
  immersion `j`, then `j ≫ f` is smooth at `z`.
* `InfinitesimalLifting.smoothAt_of_isomorphicArrow`: smoothness at a point is invariant under
  an isomorphism of arrows, that is, under conjugating the morphism by isomorphisms of its
  source and its target.

## Implementation notes

Open immersions are smooth and smoothness is stable under composition, which is all three
transfers need; no locality principle for the morphism property is used.  Passing between
`f.resLE ⊤ U le_top` and `U.ι ≫ f` is `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι` together with
`AlgebraicGeometry.Scheme.topIso`, whose inverse undoes the inclusion of the top open of the
target and is smooth because it is an isomorphism.

For the second statement the open neighbourhood is the open image of `j`, and `j` differs from
its inclusion by the isomorphism `AlgebraicGeometry.Scheme.Hom.isoOpensRange`.  For the third it
is the preimage along `j` of the neighbourhood supplied by the hypothesis, and the comparison
between the two opens is `AlgebraicGeometry.Scheme.Hom.resLE` of `j`, which is smooth because
`j` is.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace InfinitesimalLifting

variable {X S : Scheme.{u}}

/-- Smoothness of the restriction of `f` to an open of its source, read on the composite with
the inclusion of that open. -/
public theorem smooth_ι_comp_iff_smooth_resLE (f : X ⟶ S) (U : X.Opens) :
    Smooth (U.ι ≫ f) ↔ Smooth (f.resLE ⊤ U le_top) := by
  have he : f.resLE ⊤ U le_top ≫ (⊤ : S.Opens).ι = U.ι ≫ f := f.resLE_comp_ι le_top
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : Smooth ((f.resLE ⊤ U le_top ≫ (⊤ : S.Opens).ι) ≫ S.topIso.inv) := by
      rw [he]
      exact MorphismProperty.comp_mem (W := @Smooth) _ _ h inferInstance
    rwa [Category.assoc, S.ι_toIso_inv, Category.comp_id] at h'
  · rw [← he]
    exact MorphismProperty.comp_mem (W := @Smooth) _ _ h inferInstance

/-- Smoothness at a point, with the open neighbourhood of the point entering through the
composite `U.ι ≫ f` instead of through the restriction `f.resLE ⊤ U le_top`. -/
public theorem smoothAt_iff_exists_open_smooth_comp (f : X ⟶ S) (x : X) :
    SmoothAt f x ↔ ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f) :=
  ⟨fun ⟨U, hxU, hU⟩ => ⟨U, hxU, (smooth_ι_comp_iff_smooth_resLE f U).mpr hU⟩,
    fun ⟨U, hxU, hU⟩ => ⟨U, hxU, (smooth_ι_comp_iff_smooth_resLE f U).mp hU⟩⟩

/-- If `j` is an open immersion and `j ≫ f` is smooth, then `f` is smooth at every point of the
image of `j`. -/
public theorem smoothAt_of_smooth_comp {P : Scheme.{u}} (j : P ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ S) (h : Smooth (j ≫ f)) (z : P) : SmoothAt f (j z) := by
  refine (smoothAt_iff_exists_open_smooth_comp f (j z)).mpr ⟨j.opensRange, ⟨z, rfl⟩, ?_⟩
  rw [show j.opensRange.ι ≫ f = j.isoOpensRange.inv ≫ j ≫ f by
    rw [← Category.assoc, j.isoOpensRange_inv_comp]]
  exact MorphismProperty.comp_mem (W := @Smooth) _ _ inferInstance h

/-- If `f` is smooth at `j z` for an open immersion `j`, then `j ≫ f` is smooth at `z`. -/
public theorem SmoothAt.comp_isOpenImmersion {P : Scheme.{u}} (j : P ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ S) (z : P) (h : SmoothAt f (j z)) : SmoothAt (j ≫ f) z := by
  obtain ⟨U, hzU, hU⟩ := (smoothAt_iff_exists_open_smooth_comp f (j z)).mp h
  refine (smoothAt_iff_exists_open_smooth_comp (j ≫ f) z).mpr ⟨j ⁻¹ᵁ U, hzU, ?_⟩
  have he : j.resLE U (j ⁻¹ᵁ U) le_rfl ≫ U.ι = (j ⁻¹ᵁ U).ι ≫ j := j.resLE_comp_ι le_rfl
  rw [show (j ⁻¹ᵁ U).ι ≫ j ≫ f = j.resLE U (j ⁻¹ᵁ U) le_rfl ≫ U.ι ≫ f by
    rw [← Category.assoc, ← he, Category.assoc]]
  exact MorphismProperty.comp_mem (W := @Smooth) _ _ inferInstance hU

/-- **Smoothness at a point is invariant under an isomorphism of arrows.** If a commutative
square identifies `f₁` with `f₂` through isomorphisms of their sources and of their targets,
then `f₁` is smooth at a point exactly when `f₂` is smooth at the corresponding point. -/
public theorem smoothAt_of_isomorphicArrow {A₁ B₁ A₂ B₂ : Scheme.{u}} (f₁ : A₁ ⟶ B₁)
    (f₂ : A₂ ⟶ B₂) (eA : A₁ ≅ A₂) (eB : B₁ ≅ B₂) (hw : f₁ ≫ eB.hom = eA.hom ≫ f₂) (a : A₁)
    (h : SmoothAt f₁ a) : SmoothAt f₂ (eA.hom a) := by
  obtain ⟨U, haU, hU⟩ := (smoothAt_iff_exists_open_smooth_comp f₁ a).mp h
  have hs : Smooth ((U.ι ≫ eA.hom) ≫ f₂) := by
    rw [Category.assoc, ← hw, ← Category.assoc]
    exact MorphismProperty.comp_mem (W := @Smooth) _ _ hU inferInstance
  have key := smoothAt_of_smooth_comp (U.ι ≫ eA.hom) f₂ hs ⟨a, haU⟩
  rwa [show (U.ι ≫ eA.hom) (⟨a, haU⟩ : U.toScheme) = eA.hom a from
    Scheme.Hom.comp_apply U.ι eA.hom ⟨a, haU⟩] at key

end InfinitesimalLifting

end
