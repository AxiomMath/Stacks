module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsomRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport

/-!
# Stacks 08K9 at the source's hypotheses, from the finite presentation part of Stacks 08K6

In Situation 08JT let `f` be of finite presentation and let `F` and `G` be finitely presented,
flat over the base and with support proper over the base. Given the finite presentation part of
Stacks 08K6, the relative Isom functor `Isom(F, G)` is an algebraic space affine and of finite
presentation over the base.

## Main results

* `HomSituation.isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_finitePresentation`:
  Stacks 08K9 at the source's hypotheses, from the finite presentation part of Stacks 08K6.

## Implementation notes

`HomSituation.isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_finitePresentation`
takes the finite presentation part of Stacks 08K6 as its hypothesis `h08K6`. The hypotheses of
08K9 supply those of 08K6 for each of the four Hom functors: `f` is the same morphism, and the
target module of each is `F` or `G`, both finitely presented, flat over the base and with support
proper over the base. The reduction to the four Hom functors is
`HomSituation.isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_homFunctors`.

## References

* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space.HomSituation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (s : HomSituation B S hS)

/-- **Stacks 08K9 at the source's hypotheses, from Stacks 08K6.** In Situation 08JT let `f` be of
finite presentation and let `F` and `G` be finitely presented, flat over the base and with support
proper over the base. Given the finite presentation part of Stacks 08K6 (`h08K6`), the relative
Isom functor `Isom(F, G)` is an algebraic space affine and of finite presentation over the base.

The hypotheses supply those of 08K6 for the four Hom functors `H' = Hom(G, F)`, `H = Hom(F, G)`,
`I = Hom(F, F)` and `I' = Hom(G, G)` the proof uses: all four have the morphism `f`, and their
target modules `F`, `G`, `F`, `G` are finitely presented, flat over the base and with support
proper over the base. -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_finitePresentation
    (hfp : IsFinitePresentation B S hS s.f.hom)
    (hF : s.F.IsFinitePresentationOnSite) (hG : s.G.IsFinitePresentationOnSite)
    (hFflat : IsFlatOver B S hS s.X.2 s.f.hom s.F)
    (hGflat : IsFlatOver B S hS s.X.2 s.f.hom s.G)
    (hFsupp : HasProperSupport B S hS s.X.2 s.base.2 s.f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp.1)
      ((SheafOfModules.toSheaf _).obj s.F))
    (hGsupp : HasProperSupport B S hS s.X.2 s.base.2 s.f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp.1)
      ((SheafOfModules.toSheaf _).obj s.G))
    (h08K6 : ∀ (s' : HomSituation B S hS) (hfp' : IsFinitePresentation B S hS s'.f.hom),
      s'.F.IsFinitePresentationOnSite → s'.G.IsFinitePresentationOnSite →
      IsFlatOver B S hS s'.X.2 s'.f.hom s'.G →
      HasProperSupport B S hS s'.X.2 s'.base.2 s'.f.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp'.1)
        ((SheafOfModules.toSheaf _).obj s'.G) →
      s'.IsAffineFinitePresentationAlgebraicSpaceOverBase (modulePushforwardCoherence B S hS)) :
    IsAffineFinitePresentationAlgebraicSpaceOver s.base s.isomFunctor :=
  s.isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_homFunctors _
    (h08K6 s.swap hfp hG hF hFflat hFsupp) (h08K6 s hfp hF hG hGflat hGsupp)
    (h08K6 s.endoSource hfp hF hF hFflat hFsupp) (h08K6 s.endoTarget hfp hG hG hGflat hGsupp)

end AlgebraicGeometry.Space.HomSituation

end
