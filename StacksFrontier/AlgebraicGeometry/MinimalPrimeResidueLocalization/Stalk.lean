module

public import StacksFrontier.AlgebraicGeometry.AffinePushforwardStalk.Normalization
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.AffineAlgEquiv
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.RingAssembly

/-!
# The stalk of the normalization

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components and let
`x` be a point of `X`.  The stalk at `x` of the pushforward of the structure sheaf of the
normalization of `X` is the integral closure of `𝒪_{X,x}` in the product of the residue fields of
the minimal primes of `𝒪_{X,x}`, and equally in the total ring of fractions of the reduction of
`𝒪_{X,x}`.

## Main results

* `Stacks.NormalizationStalkAmbient.normalizationStalkAlgEquivIntegralClosureMinimalPrimes`: the
  stalk is the integral closure of `𝒪_{X,x}` in the product of the residue fields of its minimal
  primes.
* `Stacks.NormalizationStalkAmbient.normalizationStalkAlgEquivIntegralClosureFractionRing`: the
  stalk is the integral closure of `𝒪_{X,x}` in the total ring of fractions of its reduction.
* `Stacks.NormalizationStalkAmbient.normalizationStalkAlgEquivOfAffineOpen`: the first
  isomorphism, computed on a chosen affine open containing the point.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open Stacks.MinimalPrimeResidueLocalization

universe u

namespace Stacks.NormalizationStalkAmbient

/-- Computed on an affine open containing the point, the stalk of the pushforward of the structure
sheaf of the normalization is the integral closure of `𝒪_{X,x}` in the product of the residue
fields of its minimal primes. -/
public noncomputable def normalizationStalkAlgEquivOfAffineOpen (X : Scheme.{u})
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {x : X} {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U) :
    letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    letI : Algebra (X.presheaf.stalk x)
        (minimalPrimeResidueFieldProduct (X.presheaf.stalk x)) :=
      (minimalPrimeResidueFieldProductHom (X.presheaf.stalk x)).toAlgebra
    normalizationPushforwardStalk X hX x ≃ₐ[X.presheaf.stalk x]
      integralClosure (X.presheaf.stalk x)
        (minimalPrimeResidueFieldProduct (X.presheaf.stalk x)) := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  letI : Algebra Γ(X, U)
      Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U) :=
    ((Scheme.normalization X hX).app U).hom.toAlgebra
  letI : Algebra Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)
      (normalizationPushforwardStalk X hX x) :=
    (((Scheme.normalization X hX).base _* (Scheme.normalizationScheme X hX).presheaf).germ U x
      hxU).hom.toAlgebra
  letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  have hstalk : IsLocalization (hU.primeIdealOf (⟨x, hxU⟩ : U)).asIdeal.primeCompl
      (X.presheaf.stalk x) := hU.isLocalization_stalk (⟨x, hxU⟩ : U)
  have hpush : IsLocalization (Algebra.algebraMapSubmonoid
      Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)
      (hU.primeIdealOf (⟨x, hxU⟩ : U)).asIdeal.primeCompl)
      (normalizationPushforwardStalk X hX x) :=
    isLocalization_normalizationPushforwardStalk X hX hU hxU
  exact algEquivIntegralClosureOfIsLocalization Γ(X, U)
    (hU.primeIdealOf (⟨x, hxU⟩ : U)).asIdeal.primeCompl
    (AlgebraicGeometry.finite_minimalPrimes_of_affine_open hX U hU.isoSpec.symm)
    (X.presheaf.stalk x)
    Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)
    (normalizationPushforwardStalk X hX x)
    (normalizationSectionsAlgEquivIntegralClosureMinimalPrimeResidueFields hX U hU)
    fun a ↦ TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
      (Scheme.normalization X hX).c a

/-- The stalk of the pushforward of the structure sheaf of the normalization is canonically
isomorphic, as an `𝒪_{X,x}`-algebra, to the integral closure of `𝒪_{X,x}` in the product of the
residue fields of its minimal primes. -/
@[stacks 0C3B "the product of the minimal-prime residue fields"]
public noncomputable def
    normalizationStalkAlgEquivIntegralClosureMinimalPrimes (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    letI : Algebra (X.presheaf.stalk x)
        (minimalPrimeResidueFieldProduct (X.presheaf.stalk x)) :=
      (minimalPrimeResidueFieldProductHom (X.presheaf.stalk x)).toAlgebra
    normalizationPushforwardStalk X hX x ≃ₐ[X.presheaf.stalk x]
      integralClosure (X.presheaf.stalk x)
        (minimalPrimeResidueFieldProduct (X.presheaf.stalk x)) :=
  letI h := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  normalizationStalkAlgEquivOfAffineOpen X hX h.choose_spec.1 h.choose_spec.2.1

/-- The stalk of the pushforward of the structure sheaf of the normalization is canonically
isomorphic, as an `𝒪_{X,x}`-algebra, to the integral closure of `𝒪_{X,x}` in the total ring of
fractions of its reduction. -/
@[stacks 0C3B "the total ring of fractions of the reduction"]
public noncomputable def
    normalizationStalkAlgEquivIntegralClosureFractionRing (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    letI : Algebra (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x ⧸ nilradical (X.presheaf.stalk x))) :=
      (reductionFractionRingHom (X.presheaf.stalk x)).toAlgebra
    normalizationPushforwardStalk X hX x ≃ₐ[X.presheaf.stalk x]
      integralClosure (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x ⧸ nilradical (X.presheaf.stalk x))) :=
  normalizationStalkTransferToReductionFractionRing X hX x
    (normalizationStalkAlgEquivIntegralClosureMinimalPrimes X hX x)

end Stacks.NormalizationStalkAmbient

end
