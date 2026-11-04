module

public import StacksFrontier.AlgebraicGeometry.NormalizationStalkAmbient.Reduction
public import StacksFrontier.AlgebraicGeometry.StalkMinimalPrimes.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme

/-!
# The two descriptions of the normalization stalk imply one another

The stalk of the pushforward of the structure sheaf of the normalization can be described as the
integral closure of the local ring in two ambient algebras: the total ring of fractions of the
reduction, and the product of the residue fields of the minimal primes. The local ring of a scheme
whose quasi-compact opens have finitely many irreducible components has finitely many minimal
primes, so the two integral closures agree and each description yields the other.

## Main definitions

* `Stacks.NormalizationStalkAmbient.normalizationPushforwardStalk`: the stalk at `x` of the
  pushforward of the structure sheaf of the normalization.
* `Stacks.NormalizationStalkAmbient.normalizationPushforwardStalkAlgebra`: its canonical
  `𝒪_{X,x}`-algebra structure.

## Main results

* `Stacks.NormalizationStalkAmbient.normalizationStalkTransferToMinimalPrimeResidueFields`: the
  description by the total ring of fractions of the reduction yields the description by the
  product of the minimal-prime residue fields.
* `Stacks.NormalizationStalkAmbient.normalizationStalkTransferToReductionFractionRing`: the
  converse.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.NormalizationStalkAmbient

/-- The stalk at `x` of the pushforward of the structure sheaf of the normalization of `X`. -/
public abbrev normalizationPushforwardStalk (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) : CommRingCat.{u} :=
  let ν := Scheme.normalization X hX
  (TopCat.Presheaf.stalkFunctor CommRingCat x).obj
    ((TopCat.Sheaf.pushforward CommRingCat ν.base).obj
      (Scheme.normalizationScheme X hX).sheaf).presheaf

/-- The canonical `𝒪_{X,x}`-algebra structure on the stalk of the pushforward of the structure
sheaf of the normalization. -/
@[instance_reducible]
public noncomputable def normalizationPushforwardStalkAlgebra (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
  let ν := Scheme.normalization X hX
  ((TopCat.Presheaf.stalkFunctor CommRingCat x).map ν.c).hom.toAlgebra

/-- The description of the normalization stalk by the total ring of fractions of the reduction
yields its description by the product of the residue fields of the minimal primes. -/
public noncomputable def normalizationStalkTransferToMinimalPrimeResidueFields
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X)
    (e :
      letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
        normalizationPushforwardStalkAlgebra X hX x
      letI : Algebra (X.presheaf.stalk x)
          (FractionRing (X.presheaf.stalk x ⧸ nilradical (X.presheaf.stalk x))) :=
        (reductionFractionRingHom (X.presheaf.stalk x)).toAlgebra
      normalizationPushforwardStalk X hX x ≃ₐ[X.presheaf.stalk x]
        integralClosure (X.presheaf.stalk x)
          (FractionRing (X.presheaf.stalk x ⧸ nilradical (X.presheaf.stalk x)))) :
    letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    letI : Algebra (X.presheaf.stalk x)
        (minimalPrimeResidueFieldProduct (X.presheaf.stalk x)) :=
      (minimalPrimeResidueFieldProductHom (X.presheaf.stalk x)).toAlgebra
    normalizationPushforwardStalk X hX x ≃ₐ[X.presheaf.stalk x]
      integralClosure (X.presheaf.stalk x)
        (minimalPrimeResidueFieldProduct (X.presheaf.stalk x)) :=
  letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  letI : Algebra (X.presheaf.stalk x)
      (FractionRing (X.presheaf.stalk x ⧸ nilradical (X.presheaf.stalk x))) :=
    (reductionFractionRingHom (X.presheaf.stalk x)).toAlgebra
  letI : Algebra (X.presheaf.stalk x)
      (minimalPrimeResidueFieldProduct (X.presheaf.stalk x)) :=
    (minimalPrimeResidueFieldProductHom (X.presheaf.stalk x)).toAlgebra
  e.trans (integralClosureReductionAlgEquivMinimalPrimeResidueFields (X.presheaf.stalk x)
    (Stacks.StalkMinimalPrimes.Basic.finite_minimalPrimes_stalk X hX x))

/-- The description of the normalization stalk by the product of the residue fields of the
minimal primes yields its description by the total ring of fractions of the reduction. -/
public noncomputable def normalizationStalkTransferToReductionFractionRing
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X)
    (e :
      letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
        normalizationPushforwardStalkAlgebra X hX x
      letI : Algebra (X.presheaf.stalk x)
          (minimalPrimeResidueFieldProduct (X.presheaf.stalk x)) :=
        (minimalPrimeResidueFieldProductHom (X.presheaf.stalk x)).toAlgebra
      normalizationPushforwardStalk X hX x ≃ₐ[X.presheaf.stalk x]
        integralClosure (X.presheaf.stalk x)
          (minimalPrimeResidueFieldProduct (X.presheaf.stalk x))) :
    letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    letI : Algebra (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x ⧸ nilradical (X.presheaf.stalk x))) :=
      (reductionFractionRingHom (X.presheaf.stalk x)).toAlgebra
    normalizationPushforwardStalk X hX x ≃ₐ[X.presheaf.stalk x]
      integralClosure (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x ⧸ nilradical (X.presheaf.stalk x))) :=
  letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  letI : Algebra (X.presheaf.stalk x)
      (FractionRing (X.presheaf.stalk x ⧸ nilradical (X.presheaf.stalk x))) :=
    (reductionFractionRingHom (X.presheaf.stalk x)).toAlgebra
  letI : Algebra (X.presheaf.stalk x)
      (minimalPrimeResidueFieldProduct (X.presheaf.stalk x)) :=
    (minimalPrimeResidueFieldProductHom (X.presheaf.stalk x)).toAlgebra
  e.trans (integralClosureReductionAlgEquivMinimalPrimeResidueFields (X.presheaf.stalk x)
    (Stacks.StalkMinimalPrimes.Basic.finite_minimalPrimes_stalk X hX x)).symm

end Stacks.NormalizationStalkAmbient

end
