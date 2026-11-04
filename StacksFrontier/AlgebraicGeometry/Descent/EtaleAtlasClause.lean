module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent

/-!
# The atlas clause of Stacks 03I2

A morphism of sheaves on the big fppf site of `S` which, over a surjective étale chart of its
target, becomes a separated, locally quasi-finite, surjective and étale morphism of schemes is
representable, surjective and étale.

## Main results

* `AlgebraicGeometry.Space.presheaf_inverseImage_inf_locallyOfFiniteType_of_etale`: a morphism of
  presheaves on the big fppf site of `S` which is representable with a property `P` after every
  representable base change, and étale after every representable base change, is representable
  with `P ⊓ @AlgebraicGeometry.LocallyOfFiniteType` after every representable base change.
* `AlgebraicGeometry.Space.presheaf_surjective_and_etale_of_surjectiveEtaleChart_unconditional`:
  a morphism of presheaves between sheaves on the big fppf site of `S` which, over one surjective
  étale chart of its target, becomes a separated, locally quasi-finite, surjective and étale
  morphism of schemes is representable, surjective and étale.

## References

* [Stacks Project, Tag 01TD](https://stacks.math.columbia.edu/tag/01TD)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of presheaves on the big fppf site of `S` which is representable with a property
`P` after every representable base change, and étale after every representable base change, is
representable with `P ⊓ @AlgebraicGeometry.LocallyOfFiniteType` after every representable base
change. -/
theorem presheaf_inverseImage_inf_locallyOfFiniteType_of_etale
    {P : MorphismProperty Scheme.{u}} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {h : X ⟶ Y}
    (hP : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf h)
    (hE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf h) :
    ((P ⊓ @LocallyOfFiniteType.{u}).inverseImage
      (BigFppfOver.toScheme B S hS)).presheaf h := by
  refine ⟨hP.rep, fun _ _ g fst snd sq => ⟨hP.property g fst snd sq, ?_⟩⟩
  have : Etale ((BigFppfOver.toScheme B S hS).map snd) := hE.property g fst snd sq
  infer_instance

/-- Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S` with `X` and `Y`
sheaves, and let `g : yoneda.obj U ⟶ Y` be a surjective étale chart of `Y` along which the base
change of `f` is a separated, locally quasi-finite, surjective and étale morphism of schemes. Then
`f` is representable, surjective and étale. -/
theorem presheaf_surjective_and_etale_of_surjectiveEtaleChart_unconditional
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hYs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) {f : X ⟶ Y}
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ Y}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hV : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g))
    (hVs : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g))
    (hVe : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f :=
  presheaf_surjective_and_etale_of_locallyOfFiniteType_chart
    (isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_locallyQuasiFinite_inf_lft B S hS)
    hX hYs hs he (presheaf_inverseImage_inf_locallyOfFiniteType_of_etale hV hVe) hVs hVe

end AlgebraicGeometry.Space

end
