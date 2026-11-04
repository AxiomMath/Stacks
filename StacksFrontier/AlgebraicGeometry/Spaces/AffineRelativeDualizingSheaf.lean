module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplex

/-!
# The relative dualizing complex and sheaf over an affine base

Let `f : X ⟶ Y` be a proper, flat morphism of finite presentation of algebraic spaces with `Y`
affine. By the third remark after Stacks 0E5X, the relative dualizing complex of `X/Y` is
`ω^•_{X/Y} = a(𝒪_Y)`, where `a` is the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`
(Stacks 0E55). For a family of curves with Cohen–Macaulay fibres, the relative dualizing sheaf is
`ω_{X/Y} = H^{-1}(ω^•_{X/Y})` (Stacks 0E6Q).

## Main definitions

* `AlgebraicGeometry.Space.affineRelativeDualizingComplex`: `a(𝒪_Y)`.
* `AlgebraicGeometry.Space.affineRelativeDualizingSheaf`: `H^{-1}(a(𝒪_Y))`.

## References

* [Stacks Project, Tag 0E5X](https://stacks.math.columbia.edu/tag/0E5X)
* [Stacks Project, Tag 0E55](https://stacks.math.columbia.edu/tag/0E55)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- For `f : X ⟶ Y` of finite presentation with `Y` affine, the object `a(𝒪_Y)`, where `a` is the
right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` (Stacks 0E55). When `f` is moreover proper
and flat, this is the relative dualizing complex `ω^•_{X/Y}` of Stacks 0E5X. -/
def affineRelativeDualizingComplex {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfp : IsFinitePresentation B S hS f.hom) (hY : IsAffineSpace B S hS Y.1) :
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
  (quasicoherentDerivedRightAdjoint hZ f
    (isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS f.hom hY hfp.2.1)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS hZ f.hom X.2 hY
      hfp.2.2)
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY)).obj
      (derivedStructureSheaf B S hS Y.1 Y.2)

/-- The relative dualizing sheaf `ω_{X/Y} = H^{-1}(ω^•_{X/Y})` over an affine base, for
`ω^•_{X/Y} = a(𝒪_Y)` (Stacks 0E6Q). -/
def affineRelativeDualizingSheaf {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfp : IsFinitePresentation B S hS f.hom) (hY : IsAffineSpace B S hS Y.1) :
    Modules.{u, u} B S hS X.1 X.2 :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  (DerivedCategory.homologyFunctor _ (-1)).obj (affineRelativeDualizingComplex hZ f hfp hY).obj

end AlgebraicGeometry.Space

end
