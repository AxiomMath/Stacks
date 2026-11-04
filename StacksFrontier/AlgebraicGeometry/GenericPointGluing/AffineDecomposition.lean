module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Stalks
public import StacksFrontier.AlgebraicGeometry.GenericPointGluing.GenericPoints
public import StacksFrontier.AlgebraicGeometry.GenericPointGluing.TotalQuotientPi
public import StacksFrontier.AlgebraicGeometry.ReducedTotalQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generic-point decomposition on an affine open

Let `X` be a reduced scheme and `U` an affine open with finitely many irreducible components.
The meromorphic functions on `U` are then the product of the local rings of `X` at the generic
points lying in `U`. This is the affine, section-level, case of the displayed decomposition of
Stacks Tag 02OW, and the local input from which the sheaf-level statement is assembled.

## Main results

* `Stacks.AlgebraicGeometry.GenericPointGluing.isLocalization_nonZeroDivisors_pi_stalk`: the
  product of the local rings at the generic points lying in `U` is a localization of `Γ(X, U)`
  at its nonzerodivisors.
* `Stacks.AlgebraicGeometry.GenericPointGluing.totalQuotientObjAlgEquivPiStalk`: the resulting
  `Γ(X, U)`-algebra isomorphism from the meromorphic functions on `U` to that product.

## Implementation notes

The two inputs are the commutative algebra of
`StacksFrontier.AlgebraicGeometry.GenericPointGluing.TotalQuotientPi` and the dictionary
between the generic points of `X` lying in an affine open and the minimal primes of its ring
of sections, which is
`AlgebraicGeometry.genericPointsInOpenEquivMinimalPrimes` together with
`AlgebraicGeometry.genericPointsInOpenEquivMinimalPrimes_asIdeal`.

The applications of the two general results are written as explicit terms with every instance
argument supplied. This is not a stylistic choice: elaborating the same application with
`exact` in tactic mode does not merely take long, it fails to terminate inside two million
heartbeats, because the instance arguments are postponed and the resulting unification problem
unfolds the stalk and the section ring without bound. Supplying them makes the elaboration
immediate.

For the second result the other half is
`AlgebraicGeometry.isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen`, which
holds for an arbitrary scheme and affine open; the isomorphism is then the uniqueness of
localizations.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped nonZeroDivisors

universe u

namespace Stacks.AlgebraicGeometry.GenericPointGluing

variable (X : Scheme.{u}) {U : X.Opens}

/-- Finitely many generic points of `X` lie in an open set with finitely many irreducible
components. -/
theorem finite_genericPoints_subtype (hfin : (irreducibleComponents (U : Set X)).Finite) :
    Finite {η : genericPoints X // η.1 ∈ U} := by
  have := (finite_genericPoints_mem (Y := X) U hfin).to_subtype
  refine Finite.of_injective
    (fun η ↦ (⟨η.1.1, η.1.2, η.2⟩ : {y | y ∈ genericPoints (X : Type u) ∧ y ∈ U})) ?_
  intro a b h
  exact Subtype.ext (Subtype.ext (congrArg
    (fun z : {y | y ∈ genericPoints (X : Type u) ∧ y ∈ U} ↦ (z : X)) h))

variable {X}

/-- The prime of `Γ(X, U)` at a generic point of `X` lying in the affine open `U` is a minimal
prime. -/
theorem primeIdealOf_mem_minimalPrimes (hU : IsAffineOpen U)
    (η : {η : genericPoints X // η.1 ∈ U}) :
    (hU.primeIdealOf ⟨η.1.1, η.2⟩).asIdeal ∈ minimalPrimes Γ(X, U) := by
  rw [← genericPointsInOpenEquivMinimalPrimes_asIdeal hU η]
  exact (genericPointsInOpenEquivMinimalPrimes hU η).2

/-- Distinct generic points in an affine open give distinct primes. -/
theorem primeIdealOf_injective (hU : IsAffineOpen U) :
    Function.Injective
      (fun η : {η : genericPoints X // η.1 ∈ U} ↦ (hU.primeIdealOf ⟨η.1.1, η.2⟩).asIdeal) := by
  intro a b hab
  refine (genericPointsInOpenEquivMinimalPrimes hU).injective (Subtype.ext ?_)
  rwa [genericPointsInOpenEquivMinimalPrimes_asIdeal hU a,
    genericPointsInOpenEquivMinimalPrimes_asIdeal hU b]

/-- Every minimal prime of `Γ(X, U)` comes from a generic point of `X` lying in `U`. -/
theorem exists_primeIdealOf_eq (hU : IsAffineOpen U) (q : Ideal Γ(X, U))
    (hq : q ∈ minimalPrimes Γ(X, U)) :
    ∃ η : {η : genericPoints X // η.1 ∈ U},
      (hU.primeIdealOf ⟨η.1.1, η.2⟩).asIdeal = q := by
  obtain ⟨η, hη⟩ := (genericPointsInOpenEquivMinimalPrimes hU).surjective ⟨q, hq⟩
  exact ⟨η, by rw [← genericPointsInOpenEquivMinimalPrimes_asIdeal hU η, hη]⟩

variable [IsReduced X]

/-- On an affine open of a reduced scheme with finitely many irreducible components, the
product of the local rings of `X` at the generic points lying in that open is a localization of
its ring of sections at the nonzerodivisors, that is, a total quotient ring. -/
@[ega "IV 20.1.3.1" "special case"]
theorem isLocalization_nonZeroDivisors_pi_stalk (hU : IsAffineOpen U)
    (hfin : (irreducibleComponents (U : Set X)).Finite) :
    letI : ∀ η : {η : genericPoints X // η.1 ∈ U},
        Algebra Γ(X, U) (X.presheaf.stalk η.1.1) :=
      fun η ↦ X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
    IsLocalization (nonZeroDivisors Γ(X, U))
      (∀ η : {η : genericPoints X // η.1 ∈ U}, X.presheaf.stalk η.1.1) :=
  @isLocalization_nonZeroDivisors_pi_of_isReduced Γ(X, U) _
    {η : genericPoints X // η.1 ∈ U} (finite_genericPoints_subtype X hfin)
    (fun η ↦ (hU.primeIdealOf ⟨η.1.1, η.2⟩).asIdeal)
    (fun η ↦ (hU.primeIdealOf ⟨η.1.1, η.2⟩).2)
    (fun η ↦ X.presheaf.stalk η.1.1)
    (fun _ ↦ inferInstance)
    (fun η ↦ X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩)
    (fun η ↦ hU.isLocalization_stalk ⟨η.1.1, η.2⟩)
    inferInstance (primeIdealOf_mem_minimalPrimes hU) (primeIdealOf_injective hU)
    (exists_primeIdealOf_eq hU)

/-- The meromorphic functions on an affine open of a reduced scheme with finitely many
irreducible components are the product of the local rings of `X` at the generic points lying in
that open. This is the affine case of the displayed decomposition of Stacks Tag 02OW; both
sides are total quotient rings of `Γ(X, U)`, so the isomorphism is the uniqueness of
localizations. -/
noncomputable def totalQuotientObjAlgEquivPiStalk (hU : IsAffineOpen U)
    (hfin : (irreducibleComponents (U : Set X)).Finite) :
    letI : Algebra Γ(X, U) (X.presheaf.totalQuotientPresheaf.obj (Opposite.op U)) :=
      (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra
    letI : ∀ η : {η : genericPoints X // η.1 ∈ U},
        Algebra Γ(X, U) (X.presheaf.stalk η.1.1) :=
      fun η ↦ X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
    (X.presheaf.totalQuotientPresheaf.obj (Opposite.op U)) ≃ₐ[Γ(X, U)]
      (∀ η : {η : genericPoints X // η.1 ∈ U}, X.presheaf.stalk η.1.1) :=
  @IsLocalization.algEquiv Γ(X, U) _ (nonZeroDivisors Γ(X, U))
    (X.presheaf.totalQuotientPresheaf.obj (Opposite.op U)) _
    ((X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra)
    (AlgebraicGeometry.isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen X U hU)
    (∀ η : {η : genericPoints X // η.1 ∈ U}, X.presheaf.stalk η.1.1) _
    (@Pi.algebra {η : genericPoints X // η.1 ∈ U} Γ(X, U)
      (fun η : {η : genericPoints X // η.1 ∈ U} ↦ (X.presheaf.stalk η.1.1 : Type u)) _ _
      (fun η : {η : genericPoints X // η.1 ∈ U} ↦
        X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩))
    (isLocalization_nonZeroDivisors_pi_stalk hU hfin)

end Stacks.AlgebraicGeometry.GenericPointGluing
