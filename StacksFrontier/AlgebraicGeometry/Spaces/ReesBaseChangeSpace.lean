module

public import StacksFrontier.AlgebraicGeometry.Spaces.ReesSpectrumSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# The base change of a space over an affine object to the spectrum of a Rees algebra

Let `T` be an affine object of the site, `J` a finitely generated ideal of `A = Γ(T, 𝒪_T)` and
`f : X ⟶ h_T` a morphism of algebraic spaces.  The base change `X_B = X ×_{h_T} h_{Spec B}` along
the spectrum of the Rees algebra `B = A[Jt]` (`AlgebraicGeometry.Space.reesSpectrumOver`) is the
algebraic space of the proof of [Stacks, Tag 08AW]: its projection to `X` is affine, and its
projection to `h_{Spec B}` is proper when `f` is.

## Main definitions

* `AlgebraicGeometry.Space.reesBaseChange`: `X_B`.
* `AlgebraicGeometry.Space.reesBaseChangeProjection`: `X_B ⟶ X`.
* `AlgebraicGeometry.Space.reesBaseChangeStructure`: `X_B ⟶ h_{Spec B}`.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_reesBaseChangeProjection`.
* `AlgebraicGeometry.Space.isProper_reesBaseChangeStructure`.

## References

* [Stacks Project, Tag 08AW](https://stacks.math.columbia.edu/tag/08AW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (hJ : J.FG)
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)

/-- `X_B = X ×_{h_T} h_{Spec A[Jt]}`. -/
abbrev reesBaseChange : AlgebraicSpaces B S hS :=
  pullback f (schemeSpaceMap (reesSpectrumSiteHom B S hS T J hJ))

/-- The projection `X_B ⟶ X`. -/
abbrev reesBaseChangeProjection : reesBaseChange B S hS T J hJ f ⟶ X :=
  pullback.fst f (schemeSpaceMap (reesSpectrumSiteHom B S hS T J hJ))

/-- The projection `X_B ⟶ h_{Spec A[Jt]}`. -/
abbrev reesBaseChangeStructure :
    reesBaseChange B S hS T J hJ f ⟶ schemeSpace (reesSpectrumOver B S hS T J hJ) :=
  pullback.snd f (schemeSpaceMap (reesSpectrumSiteHom B S hS T J hJ))

/-- The defining square of `X_B`, read in presheaves. -/
theorem isPullback_reesBaseChange :
    IsPullback (reesBaseChangeProjection B S hS T J hJ f).hom
      (reesBaseChangeStructure B S hS T J hJ f).hom f.hom
      (yoneda.map (reesSpectrumSiteHom B S hS T J hJ)) :=
  AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback _ _)

/-- **The projection `X_B ⟶ X` is affine**: it is the base change of `Spec A[Jt] ⟶ T`, an affine
morphism of schemes. -/
theorem isAffineHom_reesBaseChangeProjection :
    IsAffineHom B S hS (reesBaseChangeProjection B S hS T J hJ f).hom :=
  isAffineHom_of_isPullback' B S hS (isPullback_reesBaseChange B S hS T J hJ f).flip
    (isAffineHom_yoneda_map B S hS (reesSpectrumSiteHom B S hS T J hJ))

/-- **The projection `X_B ⟶ h_{Spec A[Jt]}` is proper when `f` is.** -/
theorem isProper_reesBaseChangeStructure (hf : IsProper B S hS f.hom) :
    IsProper B S hS (reesBaseChangeStructure B S hS T J hJ f).hom :=
  isProper_of_isPullback B S hS (reesBaseChange B S hS T J hJ f).2 X.2
    (schemeSpace (reesSpectrumOver B S hS T J hJ)).2 (schemeSpace T).2
    (isPullback_reesBaseChange B S hS T J hJ f) hf

end AlgebraicGeometry.Space

end
