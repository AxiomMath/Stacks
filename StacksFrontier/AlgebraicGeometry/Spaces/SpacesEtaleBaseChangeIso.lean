module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.CategoryTheory.Comma.Over.PullbackCoherence

/-!
# Base change along an isomorphism of algebraic spaces is an equivalence of spaces-étale sites

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be an *isomorphism* of
algebraic spaces over `S`. The base-change functor
`AlgebraicGeometry.Space.spacesBaseChange` of **Stacks 03G2**, from the spaces-étale site of `Y`
to that of `X`, is then an equivalence.

This is the unit counterpart of `AlgebraicGeometry.Space.spacesBaseChange_comp`, and it is what
lets a base change along a morphism which factors as an isomorphism followed by the inclusion of
a thickening subfunctor be compared with the base change along that inclusion alone, which is
where the Stacks 05ZH statements are available.

## Main results

* `AlgebraicGeometry.Space.isEtaleOver_overMap_of_isIso`: an algebraic space étale over `X`
  becomes, along an isomorphism `X ⟶ Y`, an algebraic space étale over `Y`.
* `AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isIso` and
  `AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isIso`: base change along an
  isomorphism is essentially surjective, hence an equivalence.

## Implementation notes

Fullness and faithfulness are formal: the base-change functor is the restriction to the
étale-over objects of `CategoryTheory.Over.pullback`, which is an equivalence along an
isomorphism — `CategoryTheory.Over.isEquivalence_pullback_of_isIso` — and both the full
subcategory inclusion and a restriction of a fully faithful functor to full subcategories are
fully faithful.

Essential surjectivity is the only thing with content, and it is one cartesian square: an object
`V` étale over `X` is carried to `Y` by `CategoryTheory.Over.map f`, which keeps it étale over
the base because `f` is an isomorphism, and the square exhibiting `V` as the base change of
`CategoryTheory.Over.map f` applied to it has its two horizontal legs an identity and `f`, so it
is cartesian by `CategoryTheory.IsPullback.of_horiz_isIso`.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space étale over `X` is étale over `Y` along an isomorphism `f : X ⟶ Y`.**
Its structure morphism to `Y` is the composite of its structure morphism to `X` with `f`, and an
isomorphism is étale. -/
theorem isEtaleOver_overMap_of_isIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [IsIso f]
    (V : Over X) (hV : IsEtaleOver B S hS X V) :
    IsEtaleOver B S hS Y ((Over.map f).obj V) := by
  have hf : IsIso f.hom :=
    (ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)).map_isIso f
  exact isEtale_comp B S hS hV (isEtale_of_isIso B S hS f.hom)

/-- **Base change along an isomorphism of algebraic spaces is essentially surjective on the
spaces-étale sites.** An object étale over `X` is the base change along `f` of its image under
`CategoryTheory.Over.map f`, the comparison square having an identity and `f` as its horizontal
legs. -/
instance essSurj_spacesBaseChange_of_isIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [IsIso f] :
    (spacesBaseChange B S hS f).functor.EssSurj where
  mem_essImage V := by
    refine ⟨⟨(Over.map f).obj V.1, isEtaleOver_overMap_of_isIso B S hS f V.1 V.property⟩, ⟨?_⟩⟩
    refine (SpacesEtale.inclusion B S hS X).preimageIso ?_
    have hsq : IsPullback (𝟙 V.1.left) V.1.hom (V.1.hom ≫ f) f :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    refine Over.isoMk hsq.isoPullback.symm ?_
    change hsq.isoPullback.inv ≫ V.1.hom = pullback.snd (V.1.hom ≫ f) f
    rw [Iso.inv_comp_eq]
    exact hsq.isoPullback_hom_snd.symm

/-- **Base change along an isomorphism of algebraic spaces is an equivalence of the
spaces-étale sites.** This is not part of **Stacks 03G2**, which states that base change is a
morphism of sites and is compatible with composition; it is the unit counterpart of that
compatibility, `AlgebraicGeometry.Space.spacesBaseChange_comp`, and is therefore left
unregistered. -/
theorem isEquivalence_spacesBaseChange_of_isIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    [IsIso f] : (spacesBaseChange B S hS f).functor.IsEquivalence := by
  have hiso : (spacesBaseChange B S hS f).functor ⋙ SpacesEtale.inclusion B S hS X ≅
      SpacesEtale.inclusion B S hS Y ⋙ Over.pullback f := Iso.refl _
  let : (spacesBaseChange B S hS f).functor.Faithful := Functor.Faithful.of_comp_iso hiso
  let : (spacesBaseChange B S hS f).functor.Full := Functor.Full.of_comp_faithful_iso hiso
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.Space

end
