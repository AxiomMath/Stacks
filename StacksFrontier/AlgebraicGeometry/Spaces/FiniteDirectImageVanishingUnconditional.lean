module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules

/-!
# The vanishing half of Stacks 07UH, with nothing carried

Let `f : X ⟶ Y` be a finite morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `𝓕` be a coherent `𝒪_X`-module.  Stacks 07UH asserts two things:
`R^p f_* 𝓕 = 0` for `p > 0`, and `f_* 𝓕` coherent.  This file proves the first, with no
hypothesis carried.

`StacksFrontier/AlgebraicGeometry/Spaces/FiniteDirectImageCoherence.lean` proves it granted the
hypothesis `hchart`, that is
`AlgebraicGeometry.Space.ChartwiseIsZeroHigherDirectImage`; that hypothesis is discharged in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineHigherPushforwardUnconditional.lean`, so nothing is
left to carry.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isFinite_of_isCoherent` —
  **the vanishing half of Stacks 07UH**, unconditionally.

## Implementation notes

The whole content is that a finite morphism is affine
(`AlgebraicGeometry.Space.IsFinite.isAffineHom`) and a coherent module is quasi-coherent
(`AlgebraicGeometry.Space.IsCoherent` extends
`CategoryTheory.SheafOfModules.IsQuasicoherentOnSite`), so this is
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite`, which
is Stacks 073H.  The source's proof goes the same way round, through Stacks 071Z and the case
of schemes.

*What the source assumes and this does not.*  Stacks 07UH assumes `Y` locally Noetherian.  That
assumption is used by the coherence half — it is what makes `f_* 𝓕` coherent — and not by the
vanishing half, which only needs `f` affine and `𝓕` quasi-coherent.  So the statement below
omits it; the hypotheses it does carry, `f` finite, `𝓕` coherent and `0 < p`, are the source's.

The coherence half is not proved here: it is
`AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite'`, and both halves together,
under exactly the source's hypotheses, are
`AlgebraicGeometry.Space.isZero_rightDerived_and_isCoherent_modulePushforward_of_isFinite`.

## References

* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The vanishing half of Stacks 07UH.**  For a finite morphism `f : X ⟶ Y` of algebraic
spaces over `S`, a coherent `𝒪_X`-module `𝓕` and `p > 0`, the higher direct image vanishes:
`R^p f_* 𝓕 = 0`.

A finite morphism is affine, `AlgebraicGeometry.Space.IsFinite.isAffineHom`, and a coherent
module is quasi-coherent, so this is Stacks 073H,
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite`.

`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isFinite` is the same
statement with the affine case carried as the hypothesis `hchart` and with `𝓕` only required to
be a module; that hypothesis is now discharged by
`AlgebraicGeometry.Space.chartwiseIsZeroHigherDirectImage_of_isAffineHom`, which asks for `𝓕`
quasi-coherent and `p > 0` — exactly what the source assumes here.

The source also assumes `Y` locally Noetherian; that is used by the coherence half of the tag,
not by this one. -/
@[stacks 07UH "vanishing of the higher direct images, with nothing carried"]
theorem isZero_rightDerived_modulePushforward_of_isFinite_of_isCoherent
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFinite B S hS f.hom)
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCoherent B S hS X.1 X.2 G) (p : ℕ)
    (hp : 0 < p) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((modulePushforward B S hS f).rightDerived p).obj G) :=
  isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite B S hS f
    (IsFinite.isAffineHom hf) G hG.toIsQuasicoherentOnSite p hp

end AlgebraicGeometry.Space

end
