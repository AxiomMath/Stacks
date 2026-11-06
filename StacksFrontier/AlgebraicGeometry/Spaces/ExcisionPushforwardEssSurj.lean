module

public import StacksFrontier.AlgebraicGeometry.Spaces.ExcisionPushforwardBaseChange

/-!
# Essential surjectivity of the base-change functor of Stacks 0BGY

Let `f : V ⟶ W` be a separated étale morphism of algebraic spaces over a scheme `S`, let `T` be
a subfunctor of `W` whose preimage is carried isomorphically onto it, and let `W₀` be a
subfunctor of `W` containing the open complement of `T`.

The presheaf of pairs of
`StacksFrontier/AlgebraicGeometry/Spaces/ExcisionPushforward.lean` turns an algebraic space over
`V` which is unchanged over `f^{-1}W₀` into an algebraic space over `W` which is unchanged over
`W₀` and whose base change along `f` is the given one. That is exactly the essential
surjectivity of the base-change functor of Stacks 0BGY.

## Main results

* `AlgebraicGeometry.Space.essSurj_baseChangeFunctor_of_isAlgebraicSpace`: the base-change
  functor of Stacks 0BGY is essentially surjective, granted that the presheaf of pairs is an
  algebraic space.

## Implementation notes

The object produced is `CategoryTheory.Over.mk` of
`AlgebraicGeometry.Space.excisionProj`; that it is a modification outside `W₀` is
`AlgebraicGeometry.Space.isIso_pullback_snd_excisionProj` together with the algebraicity
hypothesis, and that its base change is the given object is
`AlgebraicGeometry.Space.excisionBaseChangeIso`.

The isomorphism asked for lives in the full subcategory of modifications, so it is produced by
`CategoryTheory.ObjectProperty.isoMk` from an isomorphism of the underlying objects of the
slice category over `V`; the last step there is the identification of
`CategoryTheory.Over.mk` of the structure morphism of an object of a slice category with that
object.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance high] hasPullbacks_presheaf_ExcisionPushforwardGluing
  hasPullback_presheaf_ExcisionPushforwardGluing

/-- **Essential surjectivity of the base-change functor of Stacks 0BGY**, granted that the
presheaf of pairs is an algebraic space. Every algebraic space over `V` which is unchanged over
`f^{-1}W₀` is the base change of one over `W` which is unchanged over `W₀`. -/
theorem essSurj_baseChangeFunctor_of_isAlgebraicSpace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {V W : AlgebraicSpaces B S hS} (f : V ⟶ W) (T W₀ : Subfunctor W.obj)
    (hT : IsIso (T.fromPreimage f.hom)) (hcompl : openComplement B S hS T ≤ W₀)
    (hf : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom)
    (halg : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (h : Y ⟶ V.obj)
      (hY : IsAlgebraicSpace B S hS Y), IsIso (pullback.snd h (W₀.preimage f.hom).ι) →
      IsAlgebraicSpace B S hS (excisionSpace B S hS f.hom h V.property W.property hY)) :
    (baseChangeFunctor B S hS f W₀).1.EssSurj :=
  ⟨fun N => ⟨⟨Over.mk (excisionProj B S hS f.hom N.obj.hom V.property W.property N.property.1),
    ⟨halg N.obj.left N.obj.hom N.property.1 N.property.2,
      isIso_pullback_snd_excisionProj B S hS f.hom N.obj.hom V.property W.property
        N.property.1 W₀ N.property.2⟩⟩,
    ⟨ObjectProperty.isoMk (P := IsModification B S hS (W₀.preimage f.hom))
      (excisionBaseChangeIso B S hS f.hom N.obj.hom V.property W.property
        N.property.1 T W₀ hT hcompl hf hsep N.property.2 ≪≫
          Over.isoMk (Iso.refl N.obj.left) (by simp))⟩⟩⟩

end AlgebraicGeometry.Space

end
