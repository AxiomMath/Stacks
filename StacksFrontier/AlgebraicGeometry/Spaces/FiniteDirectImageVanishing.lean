module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence

/-!
# Vanishing of the higher direct images along a finite morphism of algebraic spaces

For a finite morphism `f : X ⟶ Y` of algebraic spaces and a quasi-coherent `𝒪_X`-module `𝓕`,
`R^n f_*𝓕 = 0` for every `n > 0`, the vanishing assertion of Stacks 07UH.  A finite morphism is
affine, so this is Stacks 073H.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isFinite_of_isQuasicoherent`:
  the vanishing.

## References

* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 07UH, vanishing of the higher direct images.**  Let `f : X ⟶ Y` be a finite
morphism of algebraic spaces over `S` and let `𝓕` be a quasi-coherent `𝒪_X`-module.  Then
`R^n f_*𝓕 = 0` for every `n > 0`.

A finite morphism is affine, `AlgebraicGeometry.Space.IsFinite.isAffineHom`, so this is
Stacks 073H.  The source asks for `Y` locally Noetherian and `𝓕` coherent; neither is needed. -/
theorem isZero_rightDerived_modulePushforward_of_isFinite_of_isQuasicoherent (f : X ⟶ Y)
    (hf : IsFinite B S hS f.hom) (G : Modules.{u, u} B S hS X.obj X.property)
    (hG : G.IsQuasicoherentOnSite) (n : ℕ) (hn : 0 < n) :
    have := hasInjectiveResolutions_modules B S hS X.obj X.property
    IsZero (((modulePushforward B S hS f).rightDerived n).obj G) :=
  isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherentOnSite B S hS f
    hf.isAffineHom G hG n hn

end AlgebraicGeometry.Space

end
