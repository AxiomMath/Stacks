module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFinitePresentationStability
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackStageSystem
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsomRepresentableFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentStackIsomEqualizer

/-!
# Stacks 08W6 from the finite presentation part of Stacks 08K6

In Situation 08KB the diagonal of `Coh_{X/Y}` is representable by algebraic spaces, given the
finite presentation part of Stacks 08K6.

## Main results

* `CoherentSituation.coherentCFG_hasRepresentableDiagonal_of_finitePresentationHom`:
  Stacks 08W6, through Stacks 08K9
  (`HomSituation.isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_finitePresentation`)
  and `AlgebraicGeometry.Space.CoherentSituation.coherentCFG_hasRepresentableDiagonal`.

## References

* [Stacks Project, Tag 08W6](https://stacks.math.columbia.edu/tag/08W6)
* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space.CoherentSituation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

attribute [local instance] cohCategory cohIsFibered

/-- **Stacks 08W6 from Stacks 08K6.** In Situation 08KB the diagonal of `Coh_{X/Y}` is
representable by algebraic spaces, given the finite presentation part of Stacks 08K6 (`h08K6`).

Over the equalizer `E` of the two base maps of two objects of `Coh_{X/Y}` over a scheme, the
standing datum of Stacks 08JT has the base change `X_E ⟶ E` of `f`, of finite presentation, and
the pullbacks of the two modules, finitely presented, flat over `E` and with support proper over
`E` (`AlgebraicGeometry.Space.CoherentSituation.pullbackObject'`). So Stacks 08K9
(`HomSituation.isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_finitePresentation`)
makes its relative Isom functor an algebraic space over `E`, which is the input of
`AlgebraicGeometry.Space.CoherentSituation.coherentCFG_hasRepresentableDiagonal`. -/
theorem coherentCFG_hasRepresentableDiagonal_of_finitePresentationHom
    (h08K6 : ∀ (s' : HomSituation B S hS) (hfp' : IsFinitePresentation B S hS s'.f.hom),
      s'.F.IsFinitePresentationOnSite → s'.G.IsFinitePresentationOnSite →
      IsFlatOver B S hS s'.X.2 s'.f.hom s'.G →
      HasProperSupport B S hS s'.X.2 s'.base.2 s'.f.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp'.1)
        ((SheafOfModules.toSheaf _).obj s'.G) →
      s'.IsAffineFinitePresentationAlgebraicSpaceOverBase (modulePushforwardCoherence B S hS)) :
    Stack.HasRepresentableDiagonal B S hS D.coherentCFG := by
  let hst := modulePullbackStabilityOfFinitePresentation B S hS
  refine D.coherentCFG_hasRepresentableDiagonal hst fun U x y => ?_
  let A := coherentEqualizerObjectFst D x.1 y.1 x.2 y.2 hst
  let A' := coherentEqualizerObjectSnd D x.1 y.1 x.2 y.2 hst
  obtain ⟨_, hU, hP⟩ := A.properSupport
  obtain ⟨_, hU', hP'⟩ := A'.properSupport
  obtain ⟨H, p, -, -, hθ⟩ :=
    HomSituation.isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_finitePresentation
      (coherentEqualizerHomSituation D x.1 y.1 x.2 y.2 hst) (D.isFinitePresentation_projection _)
      A.finitePresentation A'.finitePresentation A.flat A'.flat ⟨hU, hP⟩ ⟨hU', hP'⟩ h08K6
  exact ⟨H, p, hθ⟩

end AlgebraicGeometry.Space.CoherentSituation

end
