module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperRepresentableDirectImageCoherence

/-!
# Direct images of a coherent module along a finite morphism of algebraic spaces

Let `f : X ⟶ Y` be a finite morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, with `Y` locally Noetherian, and let `𝓕` be a coherent `𝒪_X`-module.  Then
`R^p f_*𝓕 = 0` for `p > 0` and `f_*𝓕` is coherent.  This is Stacks 07UH, both assertions
together.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_and_isCoherent_modulePushforward_of_isFinite`:
  **Stacks 07UH**.

## Implementation notes

The vanishing assertion is
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isFinite_of_isCoherent`
(a finite morphism is affine and a coherent module quasi-coherent, so this is Stacks 073H), and
the coherence assertion is `AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite'`
(a finite morphism is representable and proper, Stacks 04NZ, and the global sections of a
coherent module on a scheme proper over an affine Noetherian scheme are finite, Stacks 02O6).
Local Noetherianity of `Y` is the étale-local property of Stacks 03E6, as in the source.

## References

* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 07UH.**  Let `f : X ⟶ Y` be a finite morphism of algebraic spaces over `S` with `Y`
locally Noetherian, and let `𝓕` be a coherent `𝒪_X`-module.  Then `R^p f_*𝓕 = 0` for every
`p > 0`, and `f_*𝓕` is a coherent `𝒪_Y`-module. -/
@[stacks 07UH]
theorem isZero_rightDerived_and_isCoherent_modulePushforward_of_isFinite
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFinite B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCoherent B S hS X.1 X.2 G) :
    (have := hasInjectiveResolutions_modules B S hS X.1 X.2
      ∀ p : ℕ, 0 < p → IsZero (((modulePushforward B S hS f).rightDerived p).obj G)) ∧
      IsCoherent B S hS Y.1 Y.2 ((modulePushforward B S hS f).obj G) :=
  ⟨fun p hp => isZero_rightDerived_modulePushforward_of_isFinite_of_isCoherent B S hS f hf G hG
      p hp,
    isCoherent_modulePushforward_of_isFinite' B S hS f hf hY G hG⟩

end AlgebraicGeometry.Space

end
