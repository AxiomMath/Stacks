module

public import Mathlib.RingTheory.Localization.FractionRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Stalks
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalksWeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient
public import StacksFrontier.Topology.Sheaves.Presheaf.LocalizationStalk

/-!
# Meromorphic functions on a reduced scheme with finitely many components locally

Let `X` be a reduced scheme every quasi-compact open of which has finitely many irreducible
components. Parts (3), (4) and (5) of Stacks Tag 02OW describe the presheaf of meromorphic
functions on such an `X`: the germs of regular sections at a point are exactly the
nonzerodivisors of the local ring, the stalk of the presheaf of meromorphic functions is the
total quotient ring of that local ring, and on an affine open the meromorphic functions are the
localization of the regular functions at all of their nonzerodivisors.

## Main definitions

* `Stacks.AlgebraicGeometry.ReducedTotalQuotient.FiniteComponentsOnCompactOpens` records the
  finiteness hypothesis: every quasi-compact open has finitely many irreducible components.

## Main results

In the namespace `Stacks.AlgebraicGeometry.ReducedTotalQuotient`,
`regularSectionGerms_eq_nonZeroDivisors` is part (3),
`stalk_totalQuotientPresheaf_isFractionRing` is part (4) and
`isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen` is part (5).

## Implementation notes

Parts (3) and (4) are the reduced cases of the statements proved in
`StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalksWeaklyAssociated` under the hypothesis
that the weakly associated points are generic, namely the two declarations there whose names end
in `_of_weaklyAssociatedPoints_subset_genericPoints`.
On a reduced scheme that hypothesis holds identically, by
`AlgebraicGeometry.weaklyAssociatedPointsOfScheme_eq_genericPoints` (Tag 0EME), so both parts
follow by supplying the inclusion. The finiteness hypothesis of the source is precisely the
second hypothesis of those two statements.

Part (5) needs neither hypothesis: the denominator submonoid of the total quotient presheaf on an
affine open is already the whole of `nonZeroDivisors Γ(X, U)`, so the statement holds for every
scheme and every affine open. That general form is
`AlgebraicGeometry.isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen` (Tag 02OV), and the
statement of part (5) is obtained from it by discarding the hypotheses.

The algebra structure on the meromorphic functions is the one induced by the canonical map from
the structure sheaf, so the localization statement is about the canonical algebra and not about a
chosen model of the localization.

## References

* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReducedTotalQuotient

/-- Every quasi-compact open of `X` has finitely many irreducible components. -/
abbrev FiniteComponentsOnCompactOpens (X : Scheme.{u}) : Prop :=
  ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite

/-- Germs of regular sections are precisely the nonzerodivisors. -/
@[stacks 02OW "part (3)"]
theorem regularSectionGerms_eq_nonZeroDivisors
    (X : Scheme.{u}) [IsReduced X]
    (hfinite : FiniteComponentsOnCompactOpens X) (x : X) :
    (⨆ (U : Opens X) (hx : x ∈ U),
      ((X.presheaf.submonoidPresheafOfStalk
        (fun y ↦ nonZeroDivisors (X.presheaf.stalk y))).obj (Opposite.op U)).map
          (X.presheaf.germ U x hx).hom) =
      nonZeroDivisors (X.presheaf.stalk x) :=
  regularSectionGerms_eq_nonZeroDivisors_of_weaklyAssociatedPoints_subset_genericPoints X
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).le hfinite x

/-- A stalk of the meromorphic-function sheaf is the total quotient ring of the local ring. -/
@[stacks 02OW "part (4)"]
theorem stalk_totalQuotientPresheaf_isFractionRing
    (X : Scheme.{u}) [IsReduced X]
    (hfinite : FiniteComponentsOnCompactOpens X) (x : X) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.totalQuotientPresheaf.stalk x) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        X.presheaf.toTotalQuotientPresheaf).hom.toAlgebra
    IsFractionRing (X.presheaf.stalk x)
      (X.presheaf.totalQuotientPresheaf.stalk x) :=
  stalk_totalQuotientPresheaf_isFractionRing_of_weaklyAssociatedPoints_subset_genericPoints X
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).le hfinite x

/-- Meromorphic functions on an affine open form the total quotient ring of its functions. -/
@[stacks 02OW "part (5)"]
theorem isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen
    (X : Scheme.{u}) [IsReduced X]
    (_hfinite : FiniteComponentsOnCompactOpens X)
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(X, U)
        ((X.presheaf.totalQuotientPresheaf).obj (Opposite.op U)) :=
      (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra
    IsLocalization (nonZeroDivisors Γ(X, U))
      ((X.presheaf.totalQuotientPresheaf).obj (Opposite.op U)) :=
  _root_.AlgebraicGeometry.isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen X U hU

end Stacks.AlgebraicGeometry.ReducedTotalQuotient
