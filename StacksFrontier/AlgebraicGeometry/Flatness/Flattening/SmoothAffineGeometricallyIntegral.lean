module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraComparison
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Geometric integrality of a smooth morphism with geometrically irreducible fibres

A smooth morphism with geometrically irreducible fibres is geometrically integral. For a morphism
`g : X ⟶ Y` of affine schemes this transfers to the morphism of spectra of the rings of functions:
`GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(X, ⊤))))` for the
algebra structure induced by `g`.

## Main results

* `AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyIrreducible_hom`: a smooth
  morphism with geometrically irreducible fibres is geometrically integral.
* `AlgebraicGeometry.geometricallyIntegral_specMap_appTop`: geometric integrality of a morphism
  of affine schemes transfers to the induced morphism of spectra of functions.
* `AlgebraicGeometry.geometricallyIntegral_specMap_algebraMap_of_smooth`: for a smooth morphism
  of affine schemes with geometrically irreducible fibres, the induced morphism of spectra of
  functions is geometrically integral.
* `AlgebraicGeometry.algebraSmooth_appTop`, `AlgebraicGeometry.finitePresentation_appTop_algebra`
  and `AlgebraicGeometry.flat_appTop_algebra`: the functions on the source of a smooth morphism of
  affine schemes form a smooth, finitely presented and flat algebra over those on the target.

## References

* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
* [Stacks Project, Tag 05MS](https://stacks.math.columbia.edu/tag/05MS)
-/

@[expose] public section

open CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

/-- Geometric integrality of a morphism of schemes is invariant under pre- and postcomposition
with an isomorphism. -/
instance geometricallyIntegral_respectsIso :
    MorphismProperty.RespectsIso @GeometricallyIntegral := by
  rw [GeometricallyIntegral.eq_geometrically, geometrically_eq_universally]
  exact MorphismProperty.universally_respectsIso _

/-- **A smooth morphism with geometrically irreducible fibres is geometrically integral.** -/
theorem geometricallyIntegral_of_smooth_of_geometricallyIrreducible_hom {X Y : Scheme.{u}}
    (g : X ⟶ Y) [Smooth g] (hg : GeometricallyIrreducible g) :
    GeometricallyIntegral g :=
  have := geometricallyReduced_of_smooth g
  GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible g

/-- A morphism of affine schemes which is geometrically integral induces a map of functions
whose spectrum is again geometrically integral. -/
theorem geometricallyIntegral_specMap_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : X ⟶ Y) (hg : GeometricallyIntegral g) :
    GeometricallyIntegral (Spec.map g.appTop) := by
  rw [show Spec.map g.appTop = X.isoSpec.inv ≫ g ≫ Y.isoSpec.hom by
    rw [← Scheme.isoSpec_hom_naturality]; simp]
  exact MorphismProperty.RespectsIso.precomp _ X.isoSpec.inv _
    (MorphismProperty.RespectsIso.postcomp _ Y.isoSpec.hom _ hg)

/-- The functions on the source of a smooth morphism of affine schemes form a smooth algebra
over the functions on the target. -/
theorem algebraSmooth_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : X ⟶ Y)
    [Smooth g] :
    letI := (g.appTop).hom.toAlgebra
    Algebra.Smooth Γ(Y, ⊤) Γ(X, ⊤) := by
  let := (g.appTop).hom.toAlgebra
  exact RingHom.smooth_algebraMap.1
    ((HasRingHomProperty.iff_of_isAffine (P := @Smooth)).1 ‹Smooth g›)

/-- The functions on the source of a smooth morphism of affine schemes form an algebra of finite
presentation over the functions on the target. -/
theorem finitePresentation_appTop_algebra {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : X ⟶ Y) [Smooth g] :
    letI := (g.appTop).hom.toAlgebra
    Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) := by
  let := (g.appTop).hom.toAlgebra
  exact (algebraSmooth_appTop g).2

/-- The functions on the source of a smooth morphism of affine schemes are flat over the
functions on the target. -/
theorem flat_appTop_algebra {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : X ⟶ Y)
    [Smooth g] :
    letI := (g.appTop).hom.toAlgebra
    Module.Flat Γ(Y, ⊤) Γ(X, ⊤) := by
  let := (g.appTop).hom.toAlgebra
  have := algebraSmooth_appTop g
  exact Algebra.Smooth.flat Γ(Y, ⊤) Γ(X, ⊤)

/-- For a smooth morphism of affine schemes with geometrically irreducible fibres, the spectrum
of the algebra of functions on the source is geometrically integral over the spectrum of the
functions on the target. -/
theorem geometricallyIntegral_specMap_algebraMap_of_smooth {X Y : Scheme.{u}} [IsAffine X]
    [IsAffine Y] (g : X ⟶ Y) [Smooth g] (hg : GeometricallyIrreducible g) :
    letI := (g.appTop).hom.toAlgebra
    GeometricallyIntegral (Spec.map (ofHom (algebraMap Γ(Y, ⊤) Γ(X, ⊤)))) := by
  let := (g.appTop).hom.toAlgebra
  exact geometricallyIntegral_specMap_appTop g
    (geometricallyIntegral_of_smooth_of_geometricallyIrreducible_hom g hg)

end AlgebraicGeometry

end
