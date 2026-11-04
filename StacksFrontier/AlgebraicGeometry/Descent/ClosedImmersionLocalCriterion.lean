module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionQuasiAffineTfae

/-!
# The local criteria for a closed immersion of algebraic spaces

Stacks 03M4 characterizes a closed immersion of algebraic spaces over a scheme `S` by five
conditions. Four of the five equivalences are proved for an arbitrary Zariski-local property of
morphisms of schemes in `StacksFrontier.AlgebraicGeometry.Spaces.ImmersionQuasiAffineTfae`, as
`AlgebraicGeometry.Space.presheaf_tfae`; the remaining one, the implication back from the
condition tested on a single surjective étale chart, takes effective descent for the property
along the surjective étale morphisms of the site. At the closed immersions that input holds
outright, as
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`, so the
five conditions are equivalent with no hypotheses.

This is a module of its own because the unconditional descent statement is proved downstream of
the file which proves the five equivalences: a closed immersion is affine, and effective descent
at the affine morphisms is itself established using the criteria of that file.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_tfae`: **Stacks 03M4 for closed immersions**, the
  five conditions equivalent with no hypotheses.

## Implementation notes

The open-immersion clause of Stacks 03M4 is
`AlgebraicGeometry.Space.isOpenImmersion_tfae_of_isAlgebraicSpace`, which lives with its own
unconditional descent statement in
`StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionEtaleDescent`. The immersion clause remains
conditional: an immersion of schemes is not affine in general, so the reduction used here is
unavailable for it, and the descent input is still
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isImmersion_of_isQuasiAffineHom`,
which assumes Stacks 0247.

Condition (2) of the source quantifies over all schemes `Z` over the target and condition (3)
over all affine ones; here they quantify over the objects of the big fppf site of `S` and over
the affine ones, which is the rendition the library's open-immersion clause of the tag already
uses.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03M4 for closed immersions**, unconditionally.

A morphism of algebraic spaces over `S` is a closed immersion exactly when every one of its base
changes to a representable presheaf is, exactly when every one of its base changes to an affine
object of the site is, exactly when its base change along one surjective étale scheme chart of
the target is, and exactly when its base changes along the members of some Zariski covering of
the target are.

This is `AlgebraicGeometry.Space.presheaf_tfae` at the closed immersions, whose descent
hypothesis — Stacks 03I2 for the closed immersions of schemes — is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`. -/
@[stacks 03M4 "closed immersions", ega "I 4.2.4" "(b)"]
theorem isClosedImmersion_tfae
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) :
    List.TFAE [
      IsClosedImmersion B S hS f,
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
        IsClosedImmersion B S hS (pullback.snd f g)),
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          IsClosedImmersion B S hS (pullback.snd f g)),
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ G),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        IsClosedImmersion B S hS (pullback.snd f g)),
      (∃ (I : Type u) (U : I → Subfunctor G),
        IsZariskiCover B S hS I U ∧
        ∀ i, IsClosedImmersion B S hS (pullback.snd f (U i).ι))
    ] :=
  presheaf_tfae B S hS _ _root_.AlgebraicGeometry.IsClosedImmersion.isZariskiLocalAtTarget
    (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS) hF hG f

end AlgebraicGeometry.Space

end
