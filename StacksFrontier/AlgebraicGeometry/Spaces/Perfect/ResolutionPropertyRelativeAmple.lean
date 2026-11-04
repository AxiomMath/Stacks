module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmple
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple

/-!
# The resolution property along a relatively ample morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and `L` an `f`-ample module
on `X`. Over an affine scheme `T` mapping to `Y`, the base change of `L` to the scheme fibre
product `T ×_Y X` is invertible and ample, so that scheme has the resolution property. When `Y`
is quasi-compact, `T` may be taken to be a surjective étale chart of `Y`.

## Main results

* `AlgebraicGeometry.Space.isAmple_baseChangeModule_of_isRelativelyAmple`: the base change of
  an `f`-ample module to the scheme fibre product over an affine scheme mapping to `Y` is
  invertible and ample.
* `AlgebraicGeometry.Space.hasResolutionProperty_baseChange_of_isRelativelyAmple`: that scheme
  has the resolution property.
* `AlgebraicGeometry.Space.exists_affine_etale_cover_hasResolutionProperty_of_isRelativelyAmple`:
  for a quasi-compact `Y` and an `f`-ample `L` there are an affine scheme `V` with a surjective
  étale morphism to `Y` and a cartesian square presenting the fibre product `V ×_Y X` as a
  scheme `U`, on which the base change of `L` is ample and which has the resolution property.

## References

* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 0F87](https://stacks.math.columbia.edu/tag/0F87)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The base change of an `f`-ample module over an affine scheme is ample.**  For
`f : X ⟶ Y` a morphism of algebraic spaces, `L` an `f`-ample module, `T` an affine scheme over
the base with a morphism to `Y`, and a cartesian square presenting the fibre product as a
scheme `U`, the pullback of `L` to `U` is invertible and ample. -/
theorem isAmple_baseChangeModule_of_isRelativelyAmple {X Y : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {L : Modules.{u, u} B S hS X.1 X.2} (hL : IsRelativelyAmple B S hS f L)
    (T U : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (g : yoneda.obj T ⟶ Y.1) (p : yoneda.obj U ⟶ X.1) (q : U ⟶ T)
    (hsq : IsPullback p (yoneda.map q) f.hom g) :
    ∃ hinv : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U p),
      @Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U p) hinv := by
  obtain ⟨hinv, hamp⟩ := hL.isRelativelyAmple_baseChange T U g p q hsq
  exact ⟨hinv, (@Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple
    ((BigFppfOver.toScheme B S hS).obj U) ((BigFppfOver.toScheme B S hS).obj T) hT
    ((BigFppfOver.toScheme B S hS).map q) (baseChangeModule B S hS L U p) hinv).mp hamp⟩

/-- **A scheme fibre product of a relatively ample morphism over an affine base has the
resolution property.** -/
theorem hasResolutionProperty_baseChange_of_isRelativelyAmple {X Y : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {L : Modules.{u, u} B S hS X.1 X.2} (hL : IsRelativelyAmple B S hS f L)
    (T U : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (g : yoneda.obj T ⟶ Y.1) (p : yoneda.obj U ⟶ X.1) (q : U ⟶ T)
    (hsq : IsPullback p (yoneda.map q) f.hom g) :
    _root_.AlgebraicGeometry.HasResolutionProperty
      ((BigFppfOver.toScheme B S hS).obj U) := by
  obtain ⟨hinv, hamp⟩ := isAmple_baseChangeModule_of_isRelativelyAmple hL T U hT g p q hsq
  exact @_root_.AlgebraicGeometry.hasResolutionProperty_of_isAmple _
    (baseChangeModule B S hS L U p) hinv hamp

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme with `Y` quasi-compact, and
let `L` be an `f`-ample module on `X`.  Then there is an affine scheme `V` over the base with a
surjective étale morphism `g` to `Y`, and a cartesian square presenting the fibre product
`V ×_Y X` as a scheme `U`, such that the base change of `L` to `U` is ample and `U` has the
resolution property. -/
@[stacks 0GUT "the first step of the proof: an affine surjective étale chart of the target over
which the scheme fibre product carries an ample module and has the resolution property"]
theorem exists_affine_etale_cover_hasResolutionProperty_of_isRelativelyAmple
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : IsRelativelyAmple B S hS f L) (hY : IsQuasiCompactSpace B S hS Y.1) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        IsEtale B S hS g ∧
        ∃ (U : BigFppfOver B S hS) (q : U ⟶ V) (p : yoneda.obj U ⟶ X.1),
          IsPullback p (yoneda.map q) f.hom g ∧
            (∃ hinv : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
                (baseChangeModule B S hS L U p),
              @Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj U)
                (baseChangeModule B S hS L U p) hinv) ∧
            _root_.AlgebraicGeometry.HasResolutionProperty
              ((BigFppfOver.toScheme B S hS).obj U) := by
  obtain ⟨V, g, hVaff, hVsurj, hVet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y.1 Y.2).mp hY
  obtain ⟨U, q, p, hsq⟩ := hL.relativelyRepresentable g
  exact ⟨V, g, hVaff, hVsurj, hVet, U, q, p, hsq,
    isAmple_baseChangeModule_of_isRelativelyAmple hL V U hVaff g p q hsq,
    hasResolutionProperty_baseChange_of_isRelativelyAmple hL V U hVaff g p q hsq⟩

end AlgebraicGeometry.Space

end
