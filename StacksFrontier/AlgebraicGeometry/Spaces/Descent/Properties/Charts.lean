module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Chart squares with a surjective morphism of schemes

Descending a property of schemes, or of morphisms of schemes, from the source of a morphism of
algebraic spaces to its target needs a commuting square of étale charts in which the chart of
the source and the chart of the target are both surjective, *and* in which the morphism of
schemes between the two charts is itself surjective. Surjectivity of that morphism of schemes
is what the scheme-level descent statements consume, and it is not a consequence of
surjectivity of the two charts.

## Main results

* `AlgebraicGeometry.Space.exists_etale_chart_square_over` lifts an étale chart of the target
  of a morphism of algebraic spaces to an étale chart of the source, together with a morphism
  of the site making the square commute which is surjective whenever the morphism of algebraic
  spaces is.

## Implementation notes

The lift is the atlas of the fibre product of the morphism with the given chart of the target.
Étaleness and surjectivity of the resulting chart of the source come from stability of both
properties under base change and composition, exactly as in
`AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`; what is added here is the
last conclusion, which holds because the second projection of the fibre product is a base
change of the given morphism and the atlas is surjective.

Surjectivity of the given chart of the target, and surjectivity of the morphism of algebraic
spaces, are both left as hypotheses of conclusions rather than of the statement, so that one
application of the lemma serves the situations in which they are available and those in which
they are not.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- An étale chart `b` of the target of a morphism `f` of algebraic spaces over `S` lifts to an
étale chart `a` of the source together with a morphism `h` of the site making the square
commute. The chart `a` is surjective as soon as `b` is, and `h` is surjective as a morphism of
schemes as soon as `f` is surjective on points. -/
theorem exists_etale_chart_square_over
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ Y)
    (hbE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (h : U ⟶ V),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      yoneda.map h ≫ b = a ≫ f ∧
      ((MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf b →
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf a) ∧
      (IsSurjective B S hS f → Surjective ((BigFppfOver.toScheme B S hS).map h)) := by
  let T := BigFppfOver.toScheme B S hS
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  let R := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) T
  have : E.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have : R.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS surjective_isStableUnderComposition.{u}
  have : E.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  have : R.IsStableUnderBaseChange := inverseImage_isStableUnderBaseChange B S hS inferInstance
  have : E.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition E
  have : R.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition R
  have : E.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange E
  have : R.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange R
  have hV := isAlgebraicSpace_yoneda B S hS V
  have hW := isAlgebraicSpace_pullback B S hS f b hX hV hY
  obtain ⟨U, c, hcS, hcE⟩ := hW.exists_atlas
  have hfstE : E.presheaf (pullback.fst f b) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f b).flip hbE
  let h : U ⟶ V := yoneda.preimage (c ≫ pullback.snd f b)
  have hh : yoneda.map h = c ≫ pullback.snd f b := yoneda.map_preimage _
  refine ⟨U, c ≫ pullback.fst f b, h,
    MorphismProperty.comp_mem E.presheaf _ _ hcE hfstE, ?_, fun hbS ↦
      MorphismProperty.comp_mem R.presheaf _ _ hcS
        (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f b).flip hbS), ?_⟩
  · rw [hh, Category.assoc, ← pullback.condition, ← Category.assoc]
  · intro hfs
    have hsnd : IsSurjective B S hS (pullback.snd f b) :=
      isSurjective_of_isPullback B S hS
        (AlgebraicSpaces.isPullback_fiberProduct B S hS (ObjectProperty.homMk f : (⟨X, hX⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
          (ObjectProperty.homMk b : (⟨yoneda.obj V, hV⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩))
        hfs
    have hcs : R.presheaf (c ≫ pullback.snd f b) :=
      (surjective_iff_surjective_pointsMap B S hS _ hV U _).mpr
        (isSurjective_comp B S hS ((surjective_iff_surjective_pointsMap B S hS _ hW U c).mp hcS)
          hsnd)
    apply MorphismProperty.of_relative_map (P := R) (F := yoneda) (f := h)
    rwa [hh]

end AlgebraicGeometry.Space

end
