module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalksWeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Divisors.MeromorphicStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regular germs and meromorphic functions on a reduced scheme

Let `X` be a reduced scheme every quasi-compact open of which has finitely many irreducible
components. Then the germs of regular sections of `𝒪_X` at a point are exactly the
nonzerodivisors of the local ring there, the stalk of the presheaf of meromorphic functions is
the total quotient ring of the local ring, and on an affine open the meromorphic functions are
the total quotient ring of the ring of functions. The affine statement holds for an arbitrary
scheme.

An integral scheme satisfies both hypotheses, and there the nonzerodivisors of a local ring are
its nonzero elements, so a regular germ at a point of an integral scheme is just a nonzero germ.

## Main results

* `Stacks.Divisors.isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen`: on an affine open
  of an arbitrary scheme the meromorphic functions are the total quotient ring of the ring of
  functions.
* `Stacks.Divisors.regularGerms_eq_nonZeroDivisors_of_isReduced` and
  `Stacks.Divisors.regularSectionGerms_eq_nonZeroDivisors_of_isReduced`: the regular germs at a
  point are the nonzerodivisors of the local ring.
* `Stacks.Divisors.stalk_totalQuotientPresheaf_isFractionRing_of_isReduced`: the stalk of the
  presheaf of meromorphic functions is the total quotient ring of the local ring.
* `Stacks.Divisors.finite_irreducibleComponents_opens`: every open of an integral scheme has
  finitely many irreducible components.
* `Stacks.Divisors.regularGerms_eq_nonZeroDivisors_of_isIntegral`: the regular germs at a point
  of an integral scheme are the nonzerodivisors of the local ring.

## References

* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 0EME](https://stacks.math.columbia.edu/tag/0EME)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.Divisors

/-- On an affine open of an arbitrary scheme the sections of the total quotient presheaf form the
localization of the ring of functions at all of its nonzerodivisors. -/
theorem isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(X, U) ((X.presheaf.totalQuotientPresheaf).obj (Opposite.op U)) :=
      (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra
    IsLocalization (nonZeroDivisors Γ(X, U))
      ((X.presheaf.totalQuotientPresheaf).obj (Opposite.op U)) := by
  let S := X.presheaf.submonoidPresheafOfStalk (fun x ↦ nonZeroDivisors (X.presheaf.stalk x))
  have hS := submonoidPresheafOfStalk_obj_eq_nonZeroDivisors X U hU
  let Astd : Algebra Γ(X, U) (S.localizationPresheaf.obj (Opposite.op U)) := inferInstance
  have hAlg : (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra = Astd :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  let : Algebra Γ(X, U) (S.localizationPresheaf.obj (Opposite.op U)) :=
    (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra
  change @IsLocalization (Γ(X, U)) _ (nonZeroDivisors Γ(X, U))
    (S.localizationPresheaf.obj (Opposite.op U)) _
    ((X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra)
  rw [← hS]
  exact hAlg.symm ▸ (inferInstance : @IsLocalization (Γ(X, U)) _
    (S.obj (Opposite.op U)) (S.localizationPresheaf.obj (Opposite.op U)) _ Astd)

/-- On a reduced scheme whose quasi-compact opens have finitely many
irreducible components, the germs of regular sections at a point are exactly the
nonzerodivisors of the local ring there. -/
theorem regularSectionGerms_eq_nonZeroDivisors_of_isReduced (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    (⨆ (U : Opens X) (hx : x ∈ U),
      ((X.presheaf.submonoidPresheafOfStalk
        (fun y ↦ nonZeroDivisors (X.presheaf.stalk y))).obj (Opposite.op U)).map
          (X.presheaf.germ U x hx).hom) =
      nonZeroDivisors (X.presheaf.stalk x) :=
  regularSectionGerms_eq_nonZeroDivisors_of_weaklyAssociatedPoints_subset_genericPoints X
    (le_of_eq (weaklyAssociatedPointsOfScheme_eq_genericPoints X)) hfinite x

/-- On a reduced scheme whose quasi-compact opens have finitely many
irreducible components, the stalk of the presheaf of meromorphic functions at a point is the
total quotient ring of the local ring there. -/
theorem stalk_totalQuotientPresheaf_isFractionRing_of_isReduced (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.totalQuotientPresheaf.stalk x) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        X.presheaf.toTotalQuotientPresheaf).hom.toAlgebra
    IsFractionRing (X.presheaf.stalk x) (X.presheaf.totalQuotientPresheaf.stalk x) :=
  stalk_totalQuotientPresheaf_isFractionRing_of_weaklyAssociatedPoints_subset_genericPoints X
    (le_of_eq (weaklyAssociatedPointsOfScheme_eq_genericPoints X)) hfinite x

/-- The regular germs of the structure sheaf of a reduced scheme whose quasi-compact opens have
finitely many irreducible components are the nonzerodivisors of the local ring. -/
@[ega "IV 20.1.3" "special case"]
theorem regularGerms_eq_nonZeroDivisors_of_isReduced (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    regularGerms X.sheaf x = nonZeroDivisors (X.sheaf.presheaf.stalk x) :=
  regularSectionGerms_eq_nonZeroDivisors_of_isReduced X hfinite x

/-- Every open subscheme of an integral scheme has finitely many irreducible components. -/
theorem finite_irreducibleComponents_opens (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) :
    (irreducibleComponents U).Finite := by
  rcases isEmpty_or_nonempty U with h | h
  · exact Set.toFinite _
  · simpa only [irreducibleComponents_eq_singleton] using Set.finite_singleton (Set.univ : Set U)

/-- On an integral scheme the regular germs at a point are the nonzerodivisors of the local
ring. -/
@[ega "IV 20.1.3" "special case"]
theorem regularGerms_eq_nonZeroDivisors_of_isIntegral (X : Scheme.{u}) [IsIntegral X] (x : X) :
    regularGerms X.sheaf x = nonZeroDivisors (X.sheaf.presheaf.stalk x) :=
  regularGerms_eq_nonZeroDivisors_of_isReduced X
    (fun U _ ↦ finite_irreducibleComponents_opens X U) x

end Stacks.Divisors
