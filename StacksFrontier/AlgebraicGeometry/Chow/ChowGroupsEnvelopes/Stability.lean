module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Envelopes are stable under composition and base change

The composite of two envelopes of schemes is an envelope, and an arbitrary base change of an
envelope is again an envelope.

## Main results

* `AlgebraicGeometry.isEnvelope_comp` states that envelopes are closed under composition.
* `AlgebraicGeometry.isEnvelope_isStableUnderBaseChange` states that envelopes are stable
  under arbitrary base change.

## References

* [Stacks Project, Tag 0GU6](https://stacks.math.columbia.edu/tag/0GU6)
* [Stacks Project, Tag 0GU7](https://stacks.math.columbia.edu/tag/0GU7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The composite of two envelopes of schemes is an envelope. -/
@[stacks 0GU6]
lemma isEnvelope_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (hf : IsEnvelope f) (hg : IsEnvelope g) : IsEnvelope (g ≫ f) :=
  ⟨MorphismProperty.comp_mem @IsProper g f hg.1 hf.1, isCompletelyDecomposed_comp g f hg.2 hf.2⟩

/-- A morphism whose precomposition with an isomorphism is completely decomposed is itself
completely decomposed. -/
private lemma isCompletelyDecomposed_of_comp_isIso
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ Z) [IsIso i]
    (h : IsCompletelyDecomposed (i ≫ f)) : IsCompletelyDecomposed f := by
  intro z
  obtain ⟨x, hx, hres⟩ := h z
  refine ⟨i x, hx, ?_⟩
  rw [Scheme.residueFieldMap_comp] at hres
  exact (isIso_comp_right_iff _ _).mp hres

/-- Envelopes of schemes are stable under arbitrary base change. -/
@[stacks 0GU7]
instance isEnvelope_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ IsEnvelope f) where
  of_isPullback {X Y Y' S f g f' g'} sq hg :=
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper) sq hg.1,
      isCompletelyDecomposed_of_comp_isIso sq.isoPullback.inv g' <| by
        simpa only [sq.isoPullback_inv_snd] using isCompletelyDecomposed_pullback g f hg.2⟩

end AlgebraicGeometry
