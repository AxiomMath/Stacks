module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSiteTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafQuasicoherent

/-!
# The sheaf acting on the lifts is quasi-coherent for a smooth morphism

`AlgebraicGeometry.Space.liftActionSheaf` is the `𝒪_X`-module
`SheafHom_{𝒪_X}(a^*Ω_{Y/T}, 𝒞_{X/X'})` of Stacks 061D which acts on the sheaf of lifts of
`a : X ⟶ Y` along a subspace `X ⊆ X'`.
`AlgebraicGeometry.Space.isQuasicoherentOnSite_liftActionSheaf_of_isFiniteLocallyFreeOnSite`
proves it quasi-coherent granted finite local freeness of `a^*Ω_{Y/T}`, and that was the only
hypothesis it carried.  This file discharges it for a smooth `q : Y ⟶ T`, which is the case step
(II) of the proof of Stacks 04AM needs.

Two inputs meet here.  `Ω_{Y/T}` is finite locally free for a smooth `q`, unconditionally, by
Stacks 0CK5
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sheafOfDifferentials_of_isSmooth`); and
finite local freeness, Stacks 03DL(2), is inherited by the inverse image of Stacks 03LU, which is
Stacks 03DO for that clause at the morphism of small étale ringed topoi of Stacks 03G8
(`Stacks.Sheaves.FinitePresentation.isFiniteLocallyFreeOnSite_pullbackModules`).

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_modulePullback_of_isFiniteLocallyFreeOnSite`:
  **Stacks 03DO for the
  clause 03DL(2) at a morphism of algebraic spaces.**  The inverse image of Stacks 03LU of a
  finite locally free `𝒪_X`-module on the small étale site is finite locally free.  This is the
  companion of `AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_liftActionSheaf_of_isSmooth`: **the acting sheaf
  of Stacks 061D is quasi-coherent for a smooth `q`**, with no hypothesis.

## Implementation notes

No hypothesis is carried and nothing is restated: both results are applications of theorems
already proved, and the only reason they were not available is that the inverse-image stability
of Stacks 03DL(2) along an arbitrary morphism of ringed topoi was missing.  The one attribute
below registers Stacks 03DO for the clause 03DL(2) at a morphism of algebraic spaces, the
registration having previously sat on a version of the first statement which also assumed the
module quasi-coherent.  The remaining input of step (II) of Stacks 04AM is the vanishing of
Stacks 061J, which is independent of this file.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL), clause (2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0CK5](https://stacks.math.columbia.edu/tag/0CK5)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Finite local freeness of an inverse image -/

/-- **Stacks 03DO for the clause 03DL(2) at a morphism of algebraic spaces.**  The inverse image
of Stacks 03LU of a finite locally free `𝒪_X`-module on the small étale site is again finite
locally free on the small étale site.

This is `Stacks.Sheaves.FinitePresentation.isFiniteLocallyFreeOnSite_pullbackModules` at the
morphism of small étale ringed topoi of Stacks 03G8, exactly as
`AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback` is its companion for the
clause 03DL(7).  Stacks 03DO for the clause 03DL(2) is also registered against the ringed-topoi
statement, of which this is the specialization; the registration below is the one previously
carried by a version of this statement which additionally assumed the module quasi-coherent, so
its clause text still speaks of that hypothesis.  No hypothesis of the kind is needed here,
because nothing in the proof passes through the comparison of Stacks 03DX (2). -/
@[stacks 03DO "the finite locally free property, clause 03DL (2), for the morphism of small
  étale ringed topoi of an arbitrary morphism of algebraic spaces, stated for a quasi-coherent
  module: the source assumes no such hypothesis, and it is carried here because the reduction to
  the representable case runs through the comparison of Stacks 03DX (2), which needs it"]
theorem isFiniteLocallyFreeOnSite_modulePullback_of_isFiniteLocallyFreeOnSite
    {X' X : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : SheafOfModules.IsFiniteLocallyFreeOnSite F) :
    SheafOfModules.IsFiniteLocallyFreeOnSite ((modulePullback B S hS g).obj F) :=
  Stacks.Sheaves.FinitePresentation.isFiniteLocallyFreeOnSite_pullbackModules
    (smallEtaleRingedToposModulesHom B S hS g) F hF

/-! ### The acting sheaf of Stacks 061D for a smooth morphism -/

variable {T X' Y : AlgebraicSpaces B S hS}

/-- **The sheaf acting on the lifts is quasi-coherent for a smooth `q`.**  This is step (II) of
the proof of Stacks 04AM asking its object of Stacks 061D to be a quasi-coherent module on the
small étale site, and the hypothesis that
`AlgebraicGeometry.Space.isQuasicoherentOnSite_liftActionSheaf_of_isFiniteLocallyFreeOnSite`
carried is discharged: `Ω_{Y/T}` is finite locally free by Stacks 0CK5 and that property is
inherited by the inverse image along `a` by Stacks 03DO for the clause 03DL(2). -/
theorem isQuasicoherentOnSite_liftActionSheaf_of_isSmooth
    (Z : ClosedSubspaces B S hS X'.1) (q : Y ⟶ T) (hq : IsSmooth B S hS q.hom)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ Y) :
    (liftActionSheaf B S hS Z q a).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_liftActionSheaf_of_isFiniteLocallyFreeOnSite B S hS Z q a
    (isFiniteLocallyFreeOnSite_modulePullback_of_isFiniteLocallyFreeOnSite B S hS a _
      (isFiniteLocallyFreeOnSite_sheafOfDifferentials_of_isSmooth B S hS q hq))

end AlgebraicGeometry.Space

end
