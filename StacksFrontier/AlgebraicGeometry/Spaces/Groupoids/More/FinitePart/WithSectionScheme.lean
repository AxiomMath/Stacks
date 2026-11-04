module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.SeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.WithSection

/-!
# The finite part containing a section is a scheme, separated and étale over the base

Let `f : X ⟶ Y` be a separated morphism of algebraic spaces over `S` which is flat and locally
of finite presentation, and let `σ : Y ⟶ X` be a section of `f`.  The finite part `(X/Y)_fin`
of `f` is then an algebraic space whose projection to `Y` is étale (Stacks 04QH) and separated
(Stacks 04RI, part (1)), and is a scheme as soon as `Y` is one (Stacks 04RI, part (2)).  Inside
it sits the open subspace `(X/Y, σ)_fin` of those pairs whose open subspace contains the
section, by Stacks 04RR.

This file combines the two.  Because the inclusion `(X/Y, σ)_fin ⟶ (X/Y)_fin` is an open
immersion, and in particular étale and a monomorphism, the projection
`(X/Y, σ)_fin ⟶ Y` obtained by composing it with the projection of `(X/Y)_fin` is again étale
and separated, and `(X/Y, σ)_fin` is a scheme whenever `Y` is.

This is exactly the step by which **Stacks 04RY** improves on **Stacks 04RW**: the object space
produced there is `U' = (R_s/U, e)_fin`, and the improvement is that under the extra hypotheses
that `s` is flat and locally of finite presentation and that `U` is a scheme, `U'` is a *scheme*
and `U' ⟶ U` is *separated* (and still étale).

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_finitePartWithSection`: `(X/Y, σ)_fin` is an
  algebraic space over `S`.
* `AlgebraicGeometry.Space.isEtale_ι_comp_baseMap_finitePartWithSection`: the projection
  `(X/Y, σ)_fin ⟶ Y` is étale.
* `AlgebraicGeometry.Space.isSeparated_ι_comp_baseMap_finitePartWithSection`: the projection
  `(X/Y, σ)_fin ⟶ Y` is separated.
* `AlgebraicGeometry.Space.isRepresentable_finitePartWithSection`: `(X/Y, σ)_fin` is a scheme
  when `Y` is.

## Implementation notes

The projection `(X/Y, σ)_fin ⟶ Y` is written out as the composite of the subfunctor inclusion
with `AlgebraicGeometry.Space.FiniteOpenSubspacePresheaf.baseMap` rather than given a name of
its own, because that is the form in which it appears in the identification carried by
`AlgebraicGeometry.Space.FinitePartUniversalOpen.objectProjection_spec`, which is where these
results are consumed.

Separatedness of the inclusion is read off the fact that a subfunctor inclusion is a
monomorphism, which is weaker than part (2) of Stacks 04RR and does not need `f` separated on
its own account; separatedness of `f` is needed only for the projection of `(X/Y)_fin`.

Representability is taken from part (4) of Stacks 04RR, which is stated as the production of an
open subscheme of a scheme representing `(X/Y)_fin`; the representing object for `(X/Y)_fin` is
supplied by part (2) of Stacks 04RI.

## References

* [Stacks Project, Tag 04QH](https://stacks.math.columbia.edu/tag/04QH)
* [Stacks Project, Tag 04RI](https://stacks.math.columbia.edu/tag/04RI)
* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 04RY](https://stacks.math.columbia.edu/tag/04RY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `(X/Y, σ)_fin` is an open subspace of `(X/Y)_fin`, for `f` separated and locally of finite
type: Stacks 04RR, part (3), fed by Stacks 04QH. -/
theorem isOpenSubspace_finitePartWithSection_of_isSeparated
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (hsep : IsSeparated B S hS f.hom)
    (hlft : IsLocallyOfFiniteType B S hS f.hom) :
    IsOpenSubspace B S hS (finitePartWithSection B S hS f σ hσ).toSubfunctor :=
  isOpenSubspace_finitePartWithSection B S hS f σ hσ
    (isAlgebraicSpace_finiteOpenSubspacePresheaf B S hS f hsep hlft)

/-- For `f` separated and locally of finite type, `(X/Y, σ)_fin` is an algebraic space over
`S`. -/
theorem isAlgebraicSpace_finitePartWithSection
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (hsep : IsSeparated B S hS f.hom)
    (hlft : IsLocallyOfFiniteType B S hS f.hom) :
    IsAlgebraicSpace B S hS (finitePartWithSection B S hS f σ hσ).toSubfunctor.toFunctor :=
  (isOpenSubspace_finitePartWithSection_of_isSeparated B S hS f σ hσ hsep hlft).1

/-- The projection `(X/Y, σ)_fin ⟶ Y` is étale, for `f` separated and locally of finite type:
the subfunctor inclusion is an open immersion, hence étale, and the projection of `(X/Y)_fin`
is étale by Stacks 04QH. -/
theorem isEtale_ι_comp_baseMap_finitePartWithSection
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (hsep : IsSeparated B S hS f.hom)
    (hlft : IsLocallyOfFiniteType B S hS f.hom) :
    IsEtale B S hS ((finitePartWithSection B S hS f σ hσ).toSubfunctor.ι ≫
      (finiteOpenSubspacePresheaf B S hS f).baseMap) :=
  isEtale_comp B S hS
    (isEtale_ι_of_isOpenSubspace
      (isOpenSubspace_finitePartWithSection_of_isSeparated B S hS f σ hσ hsep hlft))
    (isEtale_baseMap_finiteOpenSubspacePresheaf B S hS f hsep hlft)

/-- The projection `(X/Y, σ)_fin ⟶ Y` is separated, for `f` separated, flat and locally of
finite presentation: the subfunctor inclusion is a monomorphism, hence separated, and the
projection of `(X/Y)_fin` is separated by Stacks 04RI, part (1).

This is the separatedness assertion of **Stacks 04RY** for `U' = (R_s/U, e)_fin`. -/
theorem isSeparated_ι_comp_baseMap_finitePartWithSection
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (hsep : IsSeparated B S hS f.hom)
    (hflat : IsFlat B S hS f.hom)
    (hfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    IsSeparated B S hS ((finitePartWithSection B S hS f σ hσ).toSubfunctor.ι ≫
      (finiteOpenSubspacePresheaf B S hS f).baseMap) :=
  isSeparated_comp B S hS _ _
    (isSeparated_of_mono (finitePartWithSection B S hS f σ hσ).toSubfunctor.ι inferInstance)
    (isSeparated_baseMap_finiteOpenSubspacePresheaf B S hS f hsep hflat hfp)

/-- For `f` separated, flat and locally of finite presentation and `Y` a scheme, `(X/Y, σ)_fin`
is a scheme: `(X/Y)_fin` is one by Stacks 04RI, part (2), and `(X/Y, σ)_fin` is an open
subscheme of it by Stacks 04RR, part (4).

This is the representability assertion of **Stacks 04RY** for `U' = (R_s/U, e)_fin`. -/
theorem isRepresentable_finitePartWithSection
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (hsep : IsSeparated B S hS f.hom)
    (hflat : IsFlat B S hS f.hom)
    (hfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (hY : Y.obj.IsRepresentable) :
    (finitePartWithSection B S hS f σ hσ).toSubfunctor.toFunctor.IsRepresentable := by
  have hP : (finiteOpenSubspacePresheaf B S hS f).toFunctor.IsRepresentable :=
    isRepresentable_finiteOpenSubspacePresheaf_of_isRepresentable B S hS f hsep hflat hfp hY
  obtain ⟨V, -, e', -, -⟩ := openSubscheme_finitePartWithSection B S hS f σ hσ
    (finiteOpenSubspacePresheaf B S hS f).toFunctor.reprX
    (finiteOpenSubspacePresheaf B S hS f).toFunctor.reprW
  exact Functor.IsRepresentable.mk' e'

end AlgebraicGeometry.Space

end
