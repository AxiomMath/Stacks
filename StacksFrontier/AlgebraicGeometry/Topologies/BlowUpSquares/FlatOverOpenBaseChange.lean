module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute

/-!
# Flatness over an open of the base, read as flatness of one morphism to the base

Flatness of a morphism over an open `V` of its target can be read in two ways: as flatness of the
restriction `f ∣_ V` to a morphism over `V`, or as flatness of the single morphism
`f⁻¹(V) ⟶ Y` obtained by composing the inclusion of the preimage with `f`.  The two agree,
because the inclusion of an open is flat and flatness can be cancelled from a postcomposition
with an open immersion.

The second reading is the one the descent results along a cofiltered limit of schemes are stated
for — they descend a property of the *structure morphism* of an object over a stage — so the
translation is what lets flatness over an open be descended.  The second statement here does
exactly that: under a base change of the base, flatness over an open and flatness over its
inverse image correspond.

## Main results

* `AlgebraicGeometry.flat_morphismRestrict_iff_flat_preimage_ι_comp`: the two readings of
  flatness over an open agree.
* `AlgebraicGeometry.flat_pullback_snd_ι_iff_flat_morphismRestrict`: so does the reading by the
  fibre product projection.
* `AlgebraicGeometry.flat_morphismRestrict_iff_flat_pullback_snd_of_isPullback`: flatness over an
  open of the base corresponds, under base change, to flatness of the base change of the
  restricted structure morphism.

## Implementation notes

The second result is the statement that the restriction of a base change is the base change of
the restriction: the square whose horizontal edges are the restriction of the base-change
morphism to the preimages and whose vertical edges are the two composites `f⁻¹(V) ⟶ Y` and
`f₀⁻¹(V₀) ⟶ Y₀` is cartesian, being the vertical paste of the cartesian square of
`AlgebraicGeometry.isPullback_morphismRestrict` with the given one.  Uniqueness of fibre products
then identifies the fibre product itself with `f⁻¹(V)`, and flatness is invariant under the
resulting isomorphism.

## References

* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Flatness is invariant under isomorphism. -/
private instance respectsIso_flat :
    MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- Flatness can be cancelled from a postcomposition with an open immersion. -/
public theorem Flat.hasOfPostcompProperty_isOpenImmersion :
    MorphismProperty.HasOfPostcompProperty (@Flat : MorphismProperty Scheme.{u})
      @IsOpenImmersion := by
  apply hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict
  intro A B q W hq
  have : Flat q := hq
  infer_instance

/-- **The two readings of flatness over an open of the target agree.** A morphism is flat over an
open `V` of its target, in the sense that its restriction `f ∣_ V` is flat, exactly when the
composite of the inclusion of `f⁻¹(V)` with `f` is flat. -/
public theorem flat_morphismRestrict_iff_flat_preimage_ι_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) : Flat (f ∣_ V) ↔ Flat ((f ⁻¹ᵁ V).ι ≫ f) := by
  rw [← morphismRestrict_ι f V]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : Flat (f ∣_ V) := h
    infer_instance
  · exact Flat.hasOfPostcompProperty_isOpenImmersion.of_postcomp (f ∣_ V) V.ι inferInstance h

/-- Flatness of the fibre product projection over an open of the target is flatness of the
restriction to that open. -/
public theorem flat_pullback_snd_ι_iff_flat_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) : Flat (pullback.snd f V.ι) ↔ Flat (f ∣_ V) := by
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f V]
  exact MorphismProperty.cancel_left_of_respectsIso (P := (@Flat : MorphismProperty Scheme.{u}))
    (pullbackRestrictIsoRestrict f V).hom (f ∣_ V)

/-- **The restriction of a base change is the base change of the restriction.** For a cartesian
square with `f` the base change of `f₀` along `u`, the restriction of `f` to the inverse image of
an open `V₀` of the target of `f₀` sits in a cartesian square over the restriction of `f₀` to
`V₀`, read through the composites with the inclusions of the preimages. -/
public theorem isPullback_preimage_ι_comp_of_isPullback {X Y X₀ Y₀ : Scheme.{u}} {f : X ⟶ Y}
    {f₀ : X₀ ⟶ Y₀} {u : Y ⟶ Y₀} {w : X ⟶ X₀} (hX : IsPullback f w u f₀) (V₀ : Y₀.Opens) :
    IsPullback (w ∣_ (f₀ ⁻¹ᵁ V₀)) ((w ⁻¹ᵁ (f₀ ⁻¹ᵁ V₀)).ι ≫ f) ((f₀ ⁻¹ᵁ V₀).ι ≫ f₀) u :=
  (isPullback_morphismRestrict w (f₀ ⁻¹ᵁ V₀)).paste_vert hX.flip

/-- The preimage under the base change of the preimage of an open is the preimage of the inverse
image of that open. -/
public theorem preimage_preimage_eq_of_isPullback {X Y X₀ Y₀ : Scheme.{u}} {f : X ⟶ Y}
    {f₀ : X₀ ⟶ Y₀} {u : Y ⟶ Y₀} {w : X ⟶ X₀} (hX : IsPullback f w u f₀) (V₀ : Y₀.Opens) :
    w ⁻¹ᵁ (f₀ ⁻¹ᵁ V₀) = f ⁻¹ᵁ (u ⁻¹ᵁ V₀) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hX.w]

/-- **Flatness over an open of the base corresponds under base change to flatness of the base
change of the restricted structure morphism.** For a cartesian square with `f` the base change of
`f₀` along `u`, and an open `V` of the target of `f` which is the inverse image of an open `V₀` of
the target of `f₀`, flatness of `f ∣_ V` is flatness of the base change along `u` of the morphism
`f₀⁻¹(V₀) ⟶ Y₀`.

This is the form in which flatness over an open is descended along a cofiltered limit of schemes:
the right-hand side is flatness of the structure morphism of the base change of an object over
the stage, which is what Stacks 04AI,
`AlgebraicGeometry.exists_flat_baseChange_of_limitBaseChange`, speaks about. -/
public theorem flat_morphismRestrict_iff_flat_pullback_snd_of_isPullback {X Y X₀ Y₀ : Scheme.{u}}
    {f : X ⟶ Y} {f₀ : X₀ ⟶ Y₀} {u : Y ⟶ Y₀} {w : X ⟶ X₀} (hX : IsPullback f w u f₀)
    (V₀ : Y₀.Opens) {V : Y.Opens} (hV : u ⁻¹ᵁ V₀ = V) :
    Flat (f ∣_ V) ↔ Flat (pullback.snd ((f₀ ⁻¹ᵁ V₀).ι ≫ f₀) u) := by
  have hpb := isPullback_preimage_ι_comp_of_isPullback hX V₀
  have hiso : hpb.isoPullback.hom ≫ pullback.snd ((f₀ ⁻¹ᵁ V₀).ι ≫ f₀) u =
      (w ⁻¹ᵁ (f₀ ⁻¹ᵁ V₀)).ι ≫ f := hpb.isoPullback_hom_snd
  rw [flat_morphismRestrict_iff_flat_preimage_ι_comp, ← hV,
    ← preimage_preimage_eq_of_isPullback hX V₀, ← hiso]
  exact MorphismProperty.cancel_left_of_respectsIso (P := (@Flat : MorphismProperty Scheme.{u}))
    hpb.isoPullback.hom (pullback.snd ((f₀ ⁻¹ᵁ V₀).ι ≫ f₀) u)

end AlgebraicGeometry

end
