module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotCoherentCondition
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Subfunctors of `Hilb_{X/B}` as subfunctors of `Quot_{𝒪_X/X/B}`

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation. Through the
identification `Hilb_{X/B} = Quot_{𝒪_X/X/B}`, every subfunctor of the Quot functor of the
structure sheaf is a subfunctor of the Hilbert functor; for a condition `Q` on the objects of
`Coh_{X/B}`, the fibre product `Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}` becomes the subfunctor
`AlgebraicGeometry.Space.hilbertCondition` of `Hilb_{X/B}`.

Every property of morphisms which is stable under base change passes from the inclusion of the
subfunctor of `Quot_{𝒪_X/X/B}` to the inclusion of the corresponding subfunctor of `Hilb_{X/B}`.
In particular properties of `Quot^P_{𝒪_X/X/B} ⟶ Quot_{𝒪_X/X/B}`, such as representability by
flat closed immersions or by open and closed immersions, are properties of
`Hilb^P_{X/B} ⟶ Hilb_{X/B}`.

## Main results

* `CategoryTheory.MorphismProperty.relative_preimage_ι`: for a morphism of presheaves `p` and a
  subfunctor `G` of its target, if the inclusion of `G` has a relative property, so has the
  inclusion of the inverse image of `G` along `p`.
* `AlgebraicGeometry.Space.relative_hilbertCondition_ι_of_relative_quotCondition_ι`: a relative
  property of `Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B} ⟶ Quot_{𝒪_X/X/B}` is one of the
  corresponding subfunctor of `Hilb_{X/B}`.

## References

* [Stacks Project, Tag 0DPG](https://stacks.math.columbia.edu/tag/0DPG)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory

universe w u

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category C] {E : Type*} [Category E] {F : C ⥤ (Eᵒᵖ ⥤ Type w)}
  {P : MorphismProperty C}

/-- If the inclusion of a subfunctor `G` has a relative property, so has the inclusion of its
inverse image `G.preimage p` along a morphism of presheaves `p`. -/
theorem relative_preimage_ι {X Y : Eᵒᵖ ⥤ Type w} {G : Subfunctor X} (p : Y ⟶ X)
    (h : P.relative F G.ι) : P.relative F (G.preimage p).ι :=
  (P.relative_isStableUnderBaseChange).of_isPullback (Subfunctor.isPullback_preimage p G) h

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
  {Q : CoherentObject (structureSheafQuotSituation f hf).toCoherentSituation → Prop}
  (hQ : ∀ {A' A : CoherentObject (structureSheafQuotSituation f hf).toCoherentSituation},
    CoherentHom A' A → Q A → Q A')

/-- The subfunctor of `Hilb_{X/B}` corresponding to `Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}` is
the inverse image of that fibre product along the isomorphism `Hilb_{X/B} ≅ Quot_{𝒪_X/X/B}`. -/
theorem hilbertCondition_eq_preimage :
    hilbertCondition f hf Q hQ =
      ((structureSheafQuotSituation f hf).quotCondition Q hQ).preimage
        (hilbertPresheafIsoQuotSitePresheaf f hf).hom :=
  rfl

/-- If the inclusion of the fibre product `Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}` into
`Quot_{𝒪_X/X/B}` has a relative property, then so has the inclusion of the corresponding subfunctor
of `Hilb_{X/B}`. -/
theorem relative_hilbertCondition_ι_of_relative_quotCondition_ι
    {P : MorphismProperty (BigFppfOver B S hS)}
    (h : P.relative uliftYoneda.{u + 1} ((structureSheafQuotSituation f hf).quotCondition Q hQ).ι) :
    P.relative uliftYoneda.{u + 1} (hilbertCondition f hf Q hQ).ι :=
  MorphismProperty.relative_preimage_ι _ h

end AlgebraicGeometry.Space

end
