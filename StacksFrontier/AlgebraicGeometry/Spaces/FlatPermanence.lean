module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Descent
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective

/-!
# Descent of flatness along a surjective flat morphism of algebraic spaces

Let `X ⟶ Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S`, with `X ⟶ Y` surjective
and flat. If the composite `X ⟶ Z` is flat, then `Y ⟶ Z` is flat. This is the structure-sheaf
case of Tag 05VY, and it reduces to the corresponding descent statement for schemes.

Flatness of a morphism of algebraic spaces is the every-étale-chart condition
`AlgebraicGeometry.Space.IsFlat`, so the conclusion is a statement about an arbitrary
commuting square of étale charts `a₀` of `Y` and `b₀` of `Z` over a morphism `h₀` of the site.
Base changing `X ⟶ Y` along the chart `a₀` gives an algebraic space `X ×_Y U₀` whose
projection to `U₀` is flat and surjective and whose projection to `X` is étale; a surjective
étale scheme atlas `U₁` of that fibre product therefore produces a morphism `k : U₁ ⟶ U₀` of
the site which is flat and surjective on schemes, and whose composite with `h₀` is flat
because it is the scheme morphism of a chart square for `X ⟶ Z`. Scheme-level descent then
gives flatness of `h₀`.

## Main results

* `AlgebraicGeometry.Space.isFlat_of_comp_of_isSurjective_of_isFlat` is the structure-sheaf
  case of Tag 05VY: flatness of a morphism of algebraic spaces descends along a surjective
  flat morphism.

## References

* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 05VY at the structure sheaf.** If `f : X ⟶ Y` is a surjective flat morphism of
algebraic spaces over `S` and the composite `f ≫ g` is flat, then `g` is flat. -/
theorem isFlat_of_comp_of_isSurjective_of_isFlat
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hsurj : IsSurjective B S hS f) (hflat : IsFlat B S hS f)
    (hcomp : IsFlat B S hS (f ≫ g)) :
    IsFlat B S hS g := by
  have hmul := isMultiplicative_presheaf_etale B S hS
  let _ : HasBinaryProducts ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance
  intro U₀ V₀ a₀ b₀ h₀ ha₀ hb₀ hsq
  -- The base change `P = X ×_Y U₀` of `f` along the chart `a₀` of `Y`.
  have hU₀ : IsAlgebraicSpace B S hS (yoneda.obj U₀) := isAlgebraicSpace_yoneda B S hS U₀
  have hP : IsAlgebraicSpace B S hS (pullback f a₀) :=
    isAlgebraicSpace_pullback B S hS f a₀ hX hU₀ hY
  have hfstE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst f a₀) :=
    presheaf_of_isPullback B S hS (IsPullback.of_hasPullback f a₀).flip ha₀
  have hsndFlat : IsFlat B S hS (pullback.snd f a₀) :=
    isFlat_of_isPullback B S hS (IsPullback.of_hasPullback f a₀).flip ha₀ hflat
  have hsndSurj : IsSurjective B S hS (pullback.snd f a₀) :=
    isSurjective_pullback_snd B S hS hX hY hU₀ f a₀ hsurj
  -- A surjective étale scheme atlas of `P`, and the morphism of the site it induces to `U₀`.
  obtain ⟨U₁, p, hpS, hpE⟩ := hP.exists_atlas
  have hk : yoneda.map (yoneda.preimage (p ≫ pullback.snd f a₀)) = p ≫ pullback.snd f a₀ :=
    yoneda.map_preimage _
  set k : U₁ ⟶ U₀ := yoneda.preimage (p ≫ pullback.snd f a₀)
  -- `k` is flat, being the scheme morphism of a chart square for the flat `P ⟶ U₀`.
  have hkFlat : Flat ((BigFppfOver.toScheme B S hS).map k) :=
    hsndFlat U₁ U₀ p (𝟙 (yoneda.obj U₀)) k hpE (hmul.id_mem (yoneda.obj U₀))
      (by rw [Category.comp_id, hk])
  -- `k` is surjective, because it is surjective on points of the represented presheaves.
  have hprep : yoneda.relativelyRepresentable p :=
    Functor.relativelyRepresentable.of_diag hP.diagonal_representable p
  have hpSurj : IsSurjective B S hS p :=
    (surjective_iff_pointsMap_surjective_of_representable B S hS p hprep).1 hpS
  have hkSurj : Surjective ((BigFppfOver.toScheme B S hS).map k) :=
    surjective_of_surjective_pointsMap_yoneda_map B S hS k
      (by rw [hk]; exact isSurjective_comp B S hS hpSurj hsndSurj)
  -- `(U₁, V₀)` is a chart square for `f ≫ g` over `k ≫ h₀`, so `k ≫ h₀` is flat.
  have hcompFlat : Flat ((BigFppfOver.toScheme B S hS).map (k ≫ h₀)) := by
    refine hcomp U₁ V₀ (p ≫ pullback.fst f a₀) b₀ (k ≫ h₀)
      (MorphismProperty.comp_mem _ p (pullback.fst f a₀) hpE hfstE) hb₀ ?_
    calc yoneda.map (k ≫ h₀) ≫ b₀
        = yoneda.map k ≫ yoneda.map h₀ ≫ b₀ := by rw [Functor.map_comp, Category.assoc]
      _ = (p ≫ pullback.snd f a₀) ≫ a₀ ≫ g := by rw [hk, hsq]
      _ = p ≫ (pullback.snd f a₀ ≫ a₀) ≫ g := by simp
      _ = p ≫ (pullback.fst f a₀ ≫ f) ≫ g := by rw [pullback.condition]
      _ = (p ≫ pullback.fst f a₀) ≫ f ≫ g := by simp
  rw [Functor.map_comp] at hcompFlat
  have : Surjective ((BigFppfOver.toScheme B S hS).map k) := hkSurj
  have : Flat ((BigFppfOver.toScheme B S hS).map k) := hkFlat
  have : Flat ((BigFppfOver.toScheme B S hS).map k ≫
    (BigFppfOver.toScheme B S hS).map h₀) := hcompFlat
  exact flat_of_comp_of_surjective_flat ((BigFppfOver.toScheme B S hS).map k)
    ((BigFppfOver.toScheme B S hS).map h₀)

end AlgebraicGeometry.Space

end
