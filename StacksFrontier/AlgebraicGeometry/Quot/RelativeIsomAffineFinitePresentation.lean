module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomSpaceRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsomRepresentableFinitePresentation

/-!
# The relative Isom space is affine of finite presentation over the base

Stacks 08K9: in Situation 08JT assume that `f : X ⟶ B` is of finite presentation and that `𝓕`
and `𝒢` are finitely presented `𝒪_X`-modules, flat over `B`, with support proper over `B`. Then
the functor `Isom(𝓕, 𝒢)` is an algebraic space affine of finite presentation over `B`.

## Main results

Declarations are in the namespace `AlgebraicGeometry.Space.HomSituation`.

* `isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_hasProperSupport`: `Isom(𝓕, 𝒢)`
  is an algebraic space affine of finite presentation over `B`.

## Implementation notes

`Isom(𝓕, 𝒢) = (H' ×_B H) ×_{c, I ×_B I', σ} B` for the four relative Hom functors `H' = Hom(𝒢, 𝓕)`,
`H = Hom(𝓕, 𝒢)`, `I = Hom(𝓕, 𝓕)` and `I' = Hom(𝒢, 𝒢)`
(`isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_finitePresentation`, through
`isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_homFunctors`), and each of the four is
an algebraic space affine and of finite presentation over `B` by the second assertion of
Stacks 08K6 (`isAffineFinitePresentationAlgebraicSpaceOverBase_of_finitePresentation`), whose
hypotheses hold because the target module of each is `𝓕` or `𝒢`.

"Support proper over `B`" is `AlgebraicGeometry.Space.HasProperSupport`: the support of the
module, a closed subset of `|X|`, is proper over `B` (Stacks 0CZD), for `f` locally of finite type,
which holds as `f` is of finite presentation.

## References

* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.HomSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- In Situation 08JT assume that `f : X ⟶ B` is of finite presentation and that `𝓕` and `𝒢`
are finitely presented `𝒪_X`-modules, flat over `B`, with support proper over `B`. Then the
functor `Isom(𝓕, 𝒢)` is an algebraic space affine of finite presentation over `B`. -/
@[stacks 08K9 "Isom(F, G) is an algebraic space affine of finite presentation over B, for f of \
finite presentation and F, G of finite presentation, flat over B, with support proper over B"]
theorem isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_hasProperSupport
    (s : HomSituation B S hS) (hfp : IsFinitePresentation B S hS s.f.hom)
    (hF : s.F.IsFinitePresentationOnSite) (hG : s.G.IsFinitePresentationOnSite)
    (hFflat : IsFlatOver B S hS s.X.2 s.f.hom s.F)
    (hGflat : IsFlatOver B S hS s.X.2 s.f.hom s.G)
    (hFsupp : HasProperSupport B S hS s.X.2 s.base.2 s.f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp.1)
      ((SheafOfModules.toSheaf _).obj s.F))
    (hGsupp : HasProperSupport B S hS s.X.2 s.base.2 s.f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp.1)
      ((SheafOfModules.toSheaf _).obj s.G)) :
    IsAffineFinitePresentationAlgebraicSpaceOver s.base s.isomFunctor :=
  s.isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_finitePresentation hfp hF hG
    hFflat hGflat hFsupp hGsupp fun s' hfp' hF' hG' hflat' hsupp' =>
      s'.isAffineFinitePresentationAlgebraicSpaceOverBase_of_finitePresentation hfp' hF' hG'
        hflat' hsupp'

end AlgebraicGeometry.Space.HomSituation

end
