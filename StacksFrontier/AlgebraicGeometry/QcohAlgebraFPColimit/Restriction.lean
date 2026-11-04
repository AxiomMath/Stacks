module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.FiniteType

/-!
# Finiteness of a quasi-coherent algebra passes to smaller affine opens

Stacks Tag 05JS asks its approximating algebras to be of finite presentation, and the condition
is imposed on sections over *every* affine open, not over the members of a chosen cover.  This
file records why that is a reasonable demand rather than an overly strong one: for a
quasi-coherent algebra the condition propagates downwards along inclusions of affine opens, by
base change.

The input is the pushout square of Stacks Tag 01LN, already proved in this project as
`Stacks.RelativeSpec.AlgebraSheaf.isPushout_sections`: for `U ≤ U'` affine opens and `A`
quasi-coherent, `A(U)` is `Γ(X, U) ⊗_{Γ(X, U')} A(U')`.  Finite presentation and finite type of
ring maps are stable under base change in Mathlib, and `RingHom.IsStableUnderBaseChange` is
stated in terms of `Algebra.IsPushout`, which is the form the square is available in; no tensor
product has to be formed by hand.

## Main results

* `Stacks.QcohAlgebraFPColimit.finitePresentation_app_of_le`: **for a quasi-coherent algebra,
  finite presentation of the sections over an affine open passes to any smaller affine open.**
* `Stacks.QcohAlgebraFPColimit.finiteType_app_of_le`: the same for finite type.

## Implementation notes

`Algebra.IsPushout R S R' S'` means `S' = S ⊗_R R'`, and
`Stacks.RelativeSpec.AlgebraSheaf.isPushout_sections` provides it with `R = Γ(X, U')`,
`S = Γ(X, U)`, `R' = A(U')`, `S' = A(U)`.  Read in that orientation, base change would transfer
a property of `Γ(X, U') → Γ(X, U)` to `A(U') → A(U)`, which is not what is wanted.  The square
has to be transposed with `Algebra.IsPushout.symm` first, after which base change transfers a
property of `Γ(X, U') → A(U')` to `Γ(X, U) → A(U)` -- the statement here.  The two scalar towers
`RingHom.IsStableUnderBaseChange` requires of the transposed square are exactly the two that
`isPushout_sections` already carries, so nothing further is needed.

This is the restriction direction only. It is *not* locality: deducing the condition at an
arbitrary affine open from its truth on a cover additionally needs
`RingHom.finitePresentation_isLocal`, since an arbitrary affine open is not contained in any one
member of a cover. What this does establish is that the condition of Tag 05JS is not vacuous or
unsatisfiable at the affine opens outside a cover -- the defect one might suspect from its
quantifying over all of them -- because it descends from any affine open to all affine opens
inside it.

## References

* [The Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
* [The Stacks Project, Tag 01LN](https://stacks.math.columbia.edu/tag/01LN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.QcohAlgebraFPColimit

variable {X : Scheme.{u}}

/-- **For a quasi-coherent algebra, finite presentation of the sections over an affine open
passes to any smaller affine open.**  The sections of a quasi-coherent algebra over a smaller
affine open are the base change of those over the larger one (Stacks Tag 01LN), and finite
presentation is stable under base change. -/
theorem finitePresentation_app_of_le (A : AlgebraSheaf X) [A.IsQuasicoherent]
    {U U' : X.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U')
    (hfp : RingHom.FinitePresentation (A.hom.hom.app (op U')).hom) :
    RingHom.FinitePresentation (A.hom.hom.app (op U)).hom := by
  let _ := algebraOfLE X h
  let _ := AlgebraSheaf.algebraSections A U
  let _ := AlgebraSheaf.algebraSections A U'
  let _ := AlgebraSheaf.algebraRestrict A h
  let _ := AlgebraSheaf.algebraSectionsOfLE A h
  let _ := AlgebraSheaf.isScalarTower_restrict A h
  let _ := AlgebraSheaf.isScalarTower_sections A h
  let _ := (AlgebraSheaf.isPushout_sections A hU hU' h).symm
  exact RingHom.finitePresentation_isStableUnderBaseChange
    Γ(X, U') (AlgebraSheaf.sections A U') Γ(X, U) (AlgebraSheaf.sections A U) hfp

/-- **For a quasi-coherent algebra, finite type of the sections over an affine open passes to any
smaller affine open.**  The finite type analogue of
`Stacks.QcohAlgebraFPColimit.finitePresentation_app_of_le`, by the same base change. -/
theorem finiteType_app_of_le (A : AlgebraSheaf X) [A.IsQuasicoherent]
    {U U' : X.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U')
    (hft : RingHom.FiniteType (A.hom.hom.app (op U')).hom) :
    RingHom.FiniteType (A.hom.hom.app (op U)).hom := by
  let _ := algebraOfLE X h
  let _ := AlgebraSheaf.algebraSections A U
  let _ := AlgebraSheaf.algebraSections A U'
  let _ := AlgebraSheaf.algebraRestrict A h
  let _ := AlgebraSheaf.algebraSectionsOfLE A h
  let _ := AlgebraSheaf.isScalarTower_restrict A h
  let _ := AlgebraSheaf.isScalarTower_sections A h
  let _ := (AlgebraSheaf.isPushout_sections A hU hU' h).symm
  exact RingHom.finiteType_isStableUnderBaseChange
    Γ(X, U') (AlgebraSheaf.sections A U') Γ(X, U) (AlgebraSheaf.sections A U) hft

end Stacks.QcohAlgebraFPColimit
