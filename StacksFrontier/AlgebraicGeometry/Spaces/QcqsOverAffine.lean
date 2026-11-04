module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineTargetHigherDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Algebraic spaces quasi-compact and quasi-separated over an affine space

For a morphism `f : X ⟶ Y` of algebraic spaces over `S` with `Y` affine, quasi-compactness of
`f` makes `X` quasi-compact and quasi-separatedness of `f` makes `X` quasi-separated; and every
morphism between affine algebraic spaces is affine.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isQuasiCompact` (in
  `StacksFrontier/AlgebraicGeometry/Spaces/HigherDirectImageUniformBound.lean`): the source of a
  quasi-compact morphism to a quasi-compact algebraic space is quasi-compact.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace`: the source
  of a quasi-compact morphism to an affine algebraic space is quasi-compact.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace`:
  the source of a quasi-separated morphism to an affine algebraic space is quasi-separated.
* `AlgebraicGeometry.Space.isAffineHom_of_isAffineSpace` (in
  `StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeMap.lean`): a morphism
  between affine algebraic spaces is affine.
* `AlgebraicGeometry.Space.isAffineSpace_chartSpace` and
  `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_chartBaseChangeSpace`: for an affine étale
  chart `V` of `Y` the chart is affine and the base change `V ×_Y X` is quasi-separated;
  quasi-compactness of `V ×_Y X` is `AlgebraicGeometry.Space.isQuasiCompactSpace_chartBaseChange`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The source of a quasi-compact morphism of algebraic spaces with affine target is
quasi-compact. -/
theorem isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsQuasiCompact B S hS f.hom) (hY : IsAffineSpace B S hS Y.1) :
    IsQuasiCompactSpace B S hS X.1 :=
  isQuasiCompactSpace_of_isQuasiCompact B S hS Y.2 hY.isQuasiCompactSpace f.hom hf

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The source of a quasi-separated morphism of algebraic spaces with affine target is
quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsQuasiSeparated B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1) : IsAbsolutelyQuasiSeparated B S hS hZ X.1 :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ X.2
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY) hf

/-- The algebraic space represented by an affine étale chart is an affine algebraic space. -/
theorem isAffineSpace_chartSpace (Y : AlgebraicSpaces B S hS) (V : SmallEtale B S hS Y.1)
    (hV : IsAffineChart B S hS Y.1 V) : IsAffineSpace B S hS (chartSpace B S hS Y V).1 :=
  isAffineSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V) hV

variable {X Y : AlgebraicSpaces B S hS}

/-- For a quasi-separated `f : X ⟶ Y` and an affine étale chart `V` of `Y`, the base change
`V ×_Y X` is a quasi-separated algebraic space. -/
theorem isAbsolutelyQuasiSeparated_chartBaseChangeSpace (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1) (hV : IsAffineChart B S hS Y.1 V)
    (hf : IsQuasiSeparated B S hS f.hom) :
    IsAbsolutelyQuasiSeparated B S hS hZ (chartBaseChangeSpace B S hS f V).1 :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ
    (chartBaseChangeProjection B S hS f V)
    (isQuasiSeparated_chartBaseChangeProjection B S hS f V hf)
    (isAffineSpace_chartSpace B S hS Y V hV)

end AlgebraicGeometry.Space

end
