module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.SelfProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# Chow's lemma for algebraic spaces: the statement

Chow's lemma for algebraic spaces says that an algebraic space `X` over `Spec A` whose structure
morphism is separated and of finite type is the target of a proper surjective morphism `X' ⟶ X`
whose source is a *scheme*, H-quasi-projective over `Spec A`. This file states that conclusion and
the lemma itself as propositions, and proves closure properties of the conclusion.

## Main definitions

* `AlgebraicGeometry.Space.HasChowSchemeCover`: the existence, for a single algebraic space, of a
  scheme in the site, proper and surjective over the space, whose structure morphism to the base
  is H-quasi-projective.
* `AlgebraicGeometry.Space.ChowLemmaForSpaces`: Chow's lemma for algebraic spaces, as a
  proposition quantified over the ring `A` and over the algebraic space.

## Main results

* `AlgebraicGeometry.Space.hasChowSchemeCover_of_isProper_of_isSurjective`: a Chow scheme
  cover propagates along a proper surjection, so that an algebraic space proper-surjectively
  covered by one which has a Chow scheme cover has one itself.
* `AlgebraicGeometry.Space.hasChowSchemeCover_yoneda_of_isHQuasiProjective`: a scheme in the
  site which is H-quasi-projective over the base is its own Chow scheme cover.
* `AlgebraicGeometry.Space.hasChowSchemeCover_of_isIso`: the conclusion transports along an
  isomorphism of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.isProper_of_isIso`: an isomorphism of algebraic spaces over `S` is
  proper.
* `AlgebraicGeometry.Space.exists_isAffine_isEtale_isSurjective_chart_of_isQuasiCompact`: an
  algebraic space quasi-compact over a compact base admits a surjective étale chart whose source
  is an affine scheme.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- There is an object `X'` of the big fppf site over `S` — that is, a scheme over `S` inside the
site — and a morphism from the presheaf it represents to `X` which is proper and surjective, such
that the structure morphism of `X'` to `S` is H-quasi-projective. -/
def HasChowSchemeCover (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ (X' : BigFppfOver B S hS) (p : yoneda.obj X' ⟶ X),
    IsProper B S hS p ∧ IsSurjective B S hS p ∧
      IsHQuasiProjective (B.inclusion.map X'.hom)

/-- Chow's lemma for algebraic spaces: for every ring `A` whose spectrum lies in the chosen big
fppf site and every algebraic space `X` over `Spec A` whose structure morphism
`X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))` is separated and of finite type, `X` has a Chow scheme
cover. -/
def ChowLemmaForSpaces : Prop :=
  ∀ (A : CommRingCat.{u}) (hA : B.Contains (Spec A))
    (X : (BigFppfOver B (Spec A) hA)ᵒᵖ ⥤ Type u),
    IsAlgebraicSpace B (Spec A) hA X →
    ∀ f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))),
    IsSeparated B (Spec A) hA f →
    IsFiniteType B (Spec A) hA f →
    HasChowSchemeCover B (Spec A) hA X

/-- If `g : Y ⟶ X` is a proper surjective morphism of algebraic spaces over `S` and `Y` has a Chow
scheme cover, then so does `X`. -/
theorem hasChowSchemeCover_of_isProper_of_isSurjective
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (g : Y ⟶ X) (hgp : IsProper B S hS g) (hgs : IsSurjective B S hS g)
    (h : HasChowSchemeCover B S hS Y) : HasChowSchemeCover B S hS X := by
  obtain ⟨Y', p, hp, hps, hqp⟩ := h
  exact ⟨Y', p ≫ g,
    isProper_comp B S hS (isAlgebraicSpace_yoneda B S hS Y') hY hX p g hp hgp,
    isSurjective_comp B S hS hps hgs, hqp⟩

/-- An isomorphism of algebraic spaces over `S` is proper. -/
theorem isProper_of_isIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G) [IsIso e] :
    IsProper B S hS e :=
  ⟨isSeparated_of_isIso B S hS e,
    ⟨isLocallyOfFiniteType_of_isEtale' B S hS e (isEtale_of_isIso B S hS e),
      isQuasiCompact_of_isIso B S hS e⟩,
    universallyClosed_of_isIso B S hS e⟩

/-- A Chow scheme cover transports along an isomorphism of algebraic spaces over `S`. -/
theorem hasChowSchemeCover_of_isIso {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (e : X ⟶ Y) [IsIso e] (h : HasChowSchemeCover B S hS X) :
    HasChowSchemeCover B S hS Y :=
  hasChowSchemeCover_of_isProper_of_isSurjective B S hS hY hX e
    (isProper_of_isIso B S hS e) (bijective_pointsMap_of_isIso B S hS e).2 h

/-- A scheme in the site which is H-quasi-projective over the base is its own Chow scheme
cover. -/
theorem hasChowSchemeCover_yoneda_of_isHQuasiProjective (X' : BigFppfOver B S hS)
    (h : IsHQuasiProjective (B.inclusion.map X'.hom)) :
    HasChowSchemeCover B S hS (yoneda.obj X') :=
  ⟨X', 𝟙 _, isProper_of_isIso B S hS (𝟙 _),
    fun x ↦ ⟨x, congrFun (pointsMap_id B S hS (yoneda.obj X')) x⟩, h⟩

/-! ### The affine surjective étale chart of the source -/

/-- An algebraic space quasi-compact over a compact base is quasi-compact. -/
theorem isQuasiCompactSpace_of_isQuasiCompact_toBase [CompactSpace S]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (hf : IsQuasiCompact B S hS f) : IsQuasiCompactSpace B S hS X := by
  have hTc : CompactSpace ((BigFppfOver.toScheme B S hS).obj (Over.mk (𝟙 (B.obj hS)))) :=
    inferInstanceAs (CompactSpace S)
  have h := hf (yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS))))
    (isQuasiCompactSpace_yoneda_obj B S hS hTc) (𝟙 _)
  have : IsIso (pullback.snd (𝟙 (yoneda.obj (Over.mk (𝟙 (B.obj hS))))) f) :=
    (IsPullback.of_hasPullback (𝟙 (yoneda.obj (Over.mk (𝟙 (B.obj hS))))) f).flip.isIso_fst_of_isIso
  exact IsQuasiCompactSpace.of_iso B S hS h
    (asIso (pullback.snd (𝟙 (yoneda.obj (Over.mk (𝟙 (B.obj hS))))) f))

/-- An algebraic space over a compact base `S` whose structure morphism is quasi-compact admits a
surjective étale chart whose source is an affine scheme. -/
theorem exists_isAffine_isEtale_isSurjective_chart_of_isQuasiCompact [CompactSpace S]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))) (hf : IsQuasiCompact B S hS f) :
    ∃ (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
        (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf c ∧
        IsEtale B S hS c :=
  (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).1
    (isQuasiCompactSpace_of_isQuasiCompact_toBase B S hS f hf)

end AlgebraicGeometry.Space

end
