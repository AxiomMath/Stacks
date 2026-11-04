module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# Quasi-coherence of the direct image along a finite morphism

Let `f : X ⟶ Y` be a finite morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `F` be a quasi-coherent `𝒪_X`-module on the small étale site of `X`.
This file records that the direct image `f_*F` is again quasi-coherent.

The proof is a composition of two results already in the development.  By Descent,
Proposition 03DX(2) for the small étale site of an algebraic space,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, quasi-coherence
is the same as being cartesian on affine charts: the comparison
`F(A) ⊗_{𝒪(A)} 𝒪(Z) → F(Z)` is bijective for every morphism `Z ⟶ A` of affine étale charts.
That property passes to the direct image along a finite — hence affine — morphism, by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallBaseChangeModulePushforward`, because
the four rings of the base-change square of a morphism of affine charts of `Y` form a pushout.
Reading 03DX(2) back the other way turns the conclusion into quasi-coherence of `f_*F`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallBaseChangeModulePushforward`: the direct
  image of a quasi-coherent module along a finite morphism of algebraic spaces is
  quasi-coherent.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The direct image of a quasi-coherent module along a finite morphism of algebraic spaces
is quasi-coherent.**

Quasi-coherence on the small étale site is the base change property of the sections between
affine charts, Descent, Proposition 03DX(2), and that property transfers to the direct image
along a finite morphism because the base-change square of rings of a morphism of affine charts
of the target is a pushout. -/
theorem isQuasicoherentOnSite_smallBaseChangeModulePushforward
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFinite B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : F.IsQuasicoherentOnSite) :
    ((smallBaseChangeModulePushforward B S hS f
      (relativelyRepresentable_hom_of_isFinite B S hS f hf)).obj F).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS Y.1 Y.2 _).2
    (isCartesianOnAffineCharts_smallBaseChangeModulePushforward B S hS f
      (relativelyRepresentable_hom_of_isFinite B S hS f hf) F hf.isAffineHom
      ((isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X.1 X.2 F).1 hqc))

end AlgebraicGeometry.Space

end
