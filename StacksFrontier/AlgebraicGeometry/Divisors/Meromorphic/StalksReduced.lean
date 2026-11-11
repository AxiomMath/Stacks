module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalksWeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient

/-!
# Meromorphic functions on a reduced scheme

Let `X` be a reduced scheme all of whose quasi-compact opens have finitely many irreducible
components. Then the germs of regular sections at a point are exactly the nonzerodivisors of
its local ring, and the stalk of the presheaf of meromorphic functions is the total quotient
ring of that local ring.

On an affine open no hypothesis at all is needed: the meromorphic functions on an affine open
of *any* scheme are the localization of its regular functions at all nonzerodivisors.

## Main results

* `AlgebraicGeometry.IsAffineOpen.isLocalization_totalQuotientPresheaf_obj`: on an affine open
  of an arbitrary scheme, the meromorphic functions are the localization at all
  nonzerodivisors.
* `AlgebraicGeometry.regularSectionGerms_eq_nonZeroDivisors_of_isReduced`: the germs of
  regular sections are the nonzerodivisors of the local ring.
* `AlgebraicGeometry.stalk_totalQuotientPresheaf_isFractionRing_of_isReduced`: the stalk of
  the presheaf of meromorphic functions is the total quotient ring of the local ring.

## Implementation notes

The presheaf of meromorphic functions is Mathlib's `TopCat.Presheaf.totalQuotientPresheaf`,
the sectionwise localization at `TopCat.Presheaf.submonoidPresheafOfStalk` applied to the
nonzerodivisors of the stalks. Rather than choosing an isomorphism with a particular
localization type, the affine statement records the universal localization property, with the
algebra structure induced by the canonical map from the structure sheaf.

## References

* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On an affine open of any scheme, the sections of the *presheaf* of meromorphic functions
form the total quotient ring of the ring of regular functions: the localization at all
nonzerodivisors. This is not part (5) of [Stacks, Tag 02OW], which is about the sections of the
sheafification `K_X`; that statement is
`AlgebraicGeometry.isLocalization_totalQuotientSheaf_obj_of_isReduced`. -/
theorem IsAffineOpen.isLocalization_totalQuotientPresheaf_obj
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    letI : Algebra Γ(X, U)
        ((X.presheaf.totalQuotientPresheaf).obj (Opposite.op U)) :=
      (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra
    IsLocalization (nonZeroDivisors Γ(X, U))
      ((X.presheaf.totalQuotientPresheaf).obj (Opposite.op U)) := by
  let S := X.presheaf.submonoidPresheafOfStalk
    (fun x ↦ nonZeroDivisors (X.presheaf.stalk x))
  let Astd : Algebra Γ(X, U) (S.localizationPresheaf.obj (Opposite.op U)) := inferInstance
  have hAlg : (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra = Astd :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  rw [← submonoidPresheafOfStalk_obj_eq_nonZeroDivisors X U hU]
  exact hAlg.symm ▸ (inferInstance : @IsLocalization (Γ(X, U)) _
    (S.obj (Opposite.op U)) (S.localizationPresheaf.obj (Opposite.op U)) _ Astd)

/-- On a reduced scheme whose quasi-compact opens have finitely many irreducible components,
the germs of regular sections at every point are exactly the nonzerodivisors in its local
ring. -/
@[stacks 02OW "part (3)"]
theorem regularSectionGerms_eq_nonZeroDivisors_of_isReduced (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    (⨆ (U : Opens X) (hx : x ∈ U),
      ((X.presheaf.submonoidPresheafOfStalk
        (fun y ↦ nonZeroDivisors (X.presheaf.stalk y))).obj (Opposite.op U)).map
          (X.presheaf.germ U x hx).hom) =
      nonZeroDivisors (X.presheaf.stalk x) :=
  regularSectionGerms_eq_nonZeroDivisors_of_weaklyAssociatedPoints_subset_genericPoints X
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).subset hfinite x

/-- On a reduced scheme whose quasi-compact opens have finitely many irreducible components,
the stalk of the presheaf of meromorphic functions at any point is the total quotient ring of
the local ring there. -/
@[stacks 02OW "part (4)"]
theorem stalk_totalQuotientPresheaf_isFractionRing_of_isReduced (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.totalQuotientPresheaf.stalk x) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        X.presheaf.toTotalQuotientPresheaf).hom.toAlgebra
    IsFractionRing (X.presheaf.stalk x) (X.presheaf.totalQuotientPresheaf.stalk x) :=
  stalk_totalQuotientPresheaf_isFractionRing_of_weaklyAssociatedPoints_subset_genericPoints X
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).subset hfinite x

end AlgebraicGeometry
