module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# Closed immersions of algebraic spaces are quasi-compact

A closed immersion of algebraic spaces over a scheme `S` is a quasi-compact morphism: every
base change of it along a morphism from a quasi-compact algebraic space has quasi-compact
source.

## Main results

* `AlgebraicGeometry.Space.isMultiplicative_presheaf_etale`: étaleness after every
  representable base change contains the identities and is stable under composition.
* `AlgebraicGeometry.Space.presheaf_etale_of_isEtale` and
  `AlgebraicGeometry.Space.isEtale_of_presheaf_etale` identify
  `AlgebraicGeometry.Space.IsEtale` with étaleness after every representable base change; the
  first needs the source of the morphism to be representable, the second does not.
* `AlgebraicGeometry.Space.isQuasiCompact_of_isClosedImmersion'`: a closed immersion of
  presheaves on the big fppf category over `S` is quasi-compact.
* `AlgebraicGeometry.Space.isQuasiCompact_of_isClosedImmersion`: a closed immersion of
  algebraic spaces is quasi-compact.

## References

* [Stacks Project, Tag 04CG](https://stacks.math.columbia.edu/tag/04CG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Étaleness of scheme morphisms, tested after every representable base change, contains the
identities and is stable under composition. -/
theorem isMultiplicative_presheaf_etale :
    MorphismProperty.IsMultiplicative
      ((MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) := by
  set E : MorphismProperty Scheme.{u} := @AlgebraicGeometry.Etale.{u}
  have : E.IsMultiplicative := inferInstance
  have : (E.inverseImage (BigFppfOver.toScheme B S hS)).IsMultiplicative :=
    { id_mem _ := E.id_mem _, comp_mem _ _ := E.comp_mem _ _ }
  exact ⟨⟩

/-- A morphism out of a representable presheaf which is étale in the sense of
`AlgebraicGeometry.Space.IsEtale` is étale after every representable base change. -/
theorem presheaf_etale_of_isEtale {U : BigFppfOver B S hS}
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : yoneda.obj U ⟶ Z} (ha : IsEtale B S hS a) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a := by
  have := isMultiplicative_presheaf_etale B S hS
  simpa only [Category.id_comp] using ha U (𝟙 (yoneda.obj U)) (MorphismProperty.id_mem _ _)

/-- A morphism of presheaves which is étale after every representable base change is étale in
the sense of `AlgebraicGeometry.Space.IsEtale`. -/
theorem isEtale_of_presheaf_etale {W X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {b : W ⟶ X}
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    IsEtale B S hS b := by
  have := isMultiplicative_presheaf_etale B S hS
  exact fun _ φ hφ ↦ MorphismProperty.comp_mem _ φ b hφ hb

/-- A closed immersion of presheaves on the big fppf category over `S` is quasi-compact. -/
theorem isQuasiCompact_of_isClosedImmersion' {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} (hf : IsClosedImmersion B S hS f) :
    IsQuasiCompact B S hS f := by
  intro Z _ hZ g
  obtain ⟨U, a, hU, hasurj, haetale⟩ := hZ
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := hU
  have : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hf.rep.snd (a ≫ g))) := hf.property_snd (a ≫ g)
  obtain ⟨b, hb⟩ : ∃ b, IsPullback (yoneda.map (hf.rep.snd (a ≫ g))) b a (pullback.fst g f) :=
    ⟨_, IsPullback.of_bot' (hf.rep.isPullback (a ≫ g)).flip (IsPullback.of_hasPullback g f)⟩
  have key (Q : MorphismProperty Scheme.{u})
      (h : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf a) :
      (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf b :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hb h
  exact ⟨hf.rep.pullback (a ≫ g), b,
    (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding
      ((BigFppfOver.toScheme B S hS).map (hf.rep.snd (a ≫ g)))).compactSpace, key _ hasurj,
    isEtale_of_presheaf_etale B S hS (key _ (presheaf_etale_of_isEtale B S hS haetale))⟩

/-- A closed immersion of algebraic spaces over `S` is quasi-compact. -/
@[stacks 04CG]
theorem isQuasiCompact_of_isClosedImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (_hF : IsAlgebraicSpace B S hS F) (_hG : IsAlgebraicSpace B S hS G)
    (hf : IsClosedImmersion B S hS f) :
    IsQuasiCompact B S hS f :=
  isQuasiCompact_of_isClosedImmersion' B S hS hf

end AlgebraicGeometry.Space

end
