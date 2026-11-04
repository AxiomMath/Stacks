module

public import StacksFrontier.AlgebraicGeometry.NormalizationStalkAmbient.AffineAmbient
public import StacksFrontier.AlgebraicGeometry.NormalizationStalkAmbient.Reduction

/-!
# The affine ambient algebra indexed by minimal primes

Over an affine open `U` of a scheme `X` whose quasi-compact opens have finitely many irreducible
components, `normalizationSectionsRingEquivIntegralClosurePiResidueField` describes the sections
of the normalization over the preimage of `U` as the integral closure of `Γ(X, U)` in the product
of the residue fields at the generic points of `X` lying in `U`.  [Stacks, Tag 0C3B] instead names
the product of the residue fields of the minimal primes of `Γ(X, U)`.  This module reindexes the
one product into the other, with no reducedness hypothesis.

## Main results

* `AlgebraicGeometry.IsAffineOpen.residueFieldAlgEquivIdealResidueField`: the residue field of `X`
  at a point of an affine open is the residue field of the corresponding prime of the ring of
  sections.
* `AlgebraicGeometry.IsAffineOpen.piResidueFieldAlgEquivMinimalPrimeResidueFieldProduct`: a family
  of points of an affine open indexed bijectively by the minimal primes of its ring of sections
  has residue-field product the product of the residue fields of those minimal primes.
* `AlgebraicGeometry.normalizationSectionsRingEquivIntegralClosureMinimalPrimeResidueFields`: the
  sections of the normalization over the preimage of an affine open are the integral closure of
  the ring of sections in the product of the residue fields of its minimal primes.

## Implementation notes

The pointwise comparison does not go through `hU.isoSpec`.  Both residue fields are residue
fields of local rings — `X.residueField x` of the stalk, `Ideal.ResidueField p` of
`Localization.AtPrime p` — and `IsAffineOpen.isLocalization_stalk` already identifies the stalk
with `Localization.AtPrime p` as a `Γ(X, U)`-algebra, so `IsLocalRing.ResidueField.mapEquiv`
transports that identification.  Compatibility with the two structure maps is then definitional,
because `X.evaluation` is the germ followed by the residue map and `algebraMap` into
`Ideal.ResidueField p` is `algebraMap` into `Localization.AtPrime p` followed by the residue map.

The reindexing of the product is `RingEquiv.piCongrRight` for the pointwise isomorphisms followed
by `RingEquiv.piCongrLeft` for the index bijection; the latter is applied through
`Equiv.piCongrLeft_apply_apply`, whose motive has to be supplied explicitly since the fibre
`Ideal.ResidueField p` depends on the primality instance of `p`.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.NormalizationStalkAmbient

universe u

namespace AlgebraicGeometry

/-- The residue field of `X` at a point of an affine open `U` is the residue field of the prime
of `Γ(X, U)` that the point determines. -/
public noncomputable def IsAffineOpen.residueFieldAlgEquivIdealResidueField
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) {η : X} (hη : η ∈ U)
    (p : Ideal Γ(X, U)) [p.IsPrime] (hp : p = (hU.primeIdealOf ⟨η, hη⟩).asIdeal) :
    letI : Algebra Γ(X, U) (X.residueField η) := (X.evaluation U η hη).hom.toAlgebra
    X.residueField η ≃ₐ[Γ(X, U)] p.ResidueField := by
  subst hp
  letI : Algebra Γ(X, U) (X.residueField η) := (X.evaluation U η hη).hom.toAlgebra
  letI := X.presheaf.algebra_section_stalk (⟨η, hη⟩ : U)
  haveI : IsLocalization.AtPrime (X.presheaf.stalk η)
      (hU.primeIdealOf ⟨η, hη⟩).asIdeal := hU.isLocalization_stalk ⟨η, hη⟩
  let e := IsLocalization.algEquiv (hU.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl
    (X.presheaf.stalk η) (Localization.AtPrime (hU.primeIdealOf ⟨η, hη⟩).asIdeal)
  exact AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv e.toRingEquiv)
    (fun a => congrArg
      (IsLocalRing.residue (Localization.AtPrime (hU.primeIdealOf ⟨η, hη⟩).asIdeal))
      (e.commutes a))

/-- A family of points of an affine open `U` indexed bijectively by the minimal primes of
`Γ(X, U)`, each point determining the prime it is indexed by, has residue-field product the
product of the residue fields of the minimal primes of `Γ(X, U)`. -/
public noncomputable def
    IsAffineOpen.piResidueFieldAlgEquivMinimalPrimeResidueFieldProduct
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) {I : Type*}
    (pt : I → X) (hpt : ∀ i, pt i ∈ U) (e : I ≃ minimalPrimes Γ(X, U))
    (he : ∀ i, ((e i : minimalPrimes Γ(X, U)) : Ideal Γ(X, U))
      = (hU.primeIdealOf ⟨pt i, hpt i⟩).asIdeal) :
    letI (i : I) : Algebra Γ(X, U) (X.residueField (pt i)) :=
      (X.evaluation U (pt i) (hpt i)).hom.toAlgebra
    letI : Algebra Γ(X, U) (minimalPrimeResidueFieldProduct Γ(X, U)) :=
      (minimalPrimeResidueFieldProductHom Γ(X, U)).toAlgebra
    (∀ i, X.residueField (pt i)) ≃ₐ[Γ(X, U)] minimalPrimeResidueFieldProduct Γ(X, U) := by
  letI (i : I) : Algebra Γ(X, U) (X.residueField (pt i)) :=
    (X.evaluation U (pt i) (hpt i)).hom.toAlgebra
  letI : Algebra Γ(X, U) (minimalPrimeResidueFieldProduct Γ(X, U)) :=
    (minimalPrimeResidueFieldProductHom Γ(X, U)).toAlgebra
  letI (i : I) : ((e i : minimalPrimes Γ(X, U)) : Ideal Γ(X, U)).IsPrime := (e i).2.1.1
  refine AlgEquiv.ofRingEquiv
    (f := (RingEquiv.piCongrRight fun i =>
        (hU.residueFieldAlgEquivIdealResidueField (hpt i) _ (he i)).toRingEquiv).trans
      (RingEquiv.piCongrLeft (fun p : minimalPrimes Γ(X, U) =>
        @Ideal.ResidueField _ _ p.1 p.2.1.1) e)) (fun a => ?_)
  funext p
  obtain ⟨i, rfl⟩ := e.surjective p
  exact (Equiv.piCongrLeft_apply_apply
      (fun q : minimalPrimes Γ(X, U) => @Ideal.ResidueField _ _ q.1 q.2.1.1) e _ i).trans
    ((hU.residueFieldAlgEquivIdealResidueField (hpt i) _ (he i)).commutes a)

/-- The product of the residue fields at the generic points of `X` lying in an affine open `U` is
the product of the residue fields of the minimal primes of `Γ(X, U)`. -/
public noncomputable def
    IsAffineOpen.genericPointResidueFieldsAlgEquivMinimalPrimeResidueFieldProduct
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    letI (η : {η : genericPoints X // η.1 ∈ U}) : Algebra Γ(X, U) (X.residueField η.1.1) :=
      (X.evaluation U η.1.1 η.2).hom.toAlgebra
    letI : Algebra Γ(X, U) (minimalPrimeResidueFieldProduct Γ(X, U)) :=
      (minimalPrimeResidueFieldProductHom Γ(X, U)).toAlgebra
    (∀ η : {η : genericPoints X // η.1 ∈ U}, X.residueField η.1.1) ≃ₐ[Γ(X, U)]
      minimalPrimeResidueFieldProduct Γ(X, U) :=
  hU.piResidueFieldAlgEquivMinimalPrimeResidueFieldProduct
    (fun η : {η : genericPoints X // η.1 ∈ U} => η.1.1) (fun η => η.2)
    (genericPointsInOpenEquivMinimalPrimes hU)
    (fun η => genericPointsInOpenEquivMinimalPrimes_asIdeal hU η)

/-- **Stacks Project, Tag 0C3B.** The sections of the normalization over the preimage of an
affine open `U` are the integral closure of `Γ(X, U)` in the product of the residue fields of the
minimal primes of `Γ(X, U)`.  No reducedness hypothesis is needed. -/
public noncomputable def normalizationSectionsRingEquivIntegralClosureMinimalPrimeResidueFields
    {X : Scheme.{u}}
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(X, U) (minimalPrimeResidueFieldProduct Γ(X, U)) :=
      (minimalPrimeResidueFieldProductHom Γ(X, U)).toAlgebra
    Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U) ≃+*
      integralClosure Γ(X, U) (minimalPrimeResidueFieldProduct Γ(X, U)) :=
  letI (η : {η : genericPoints X // η.1 ∈ U}) : Algebra Γ(X, U) (X.residueField η.1.1) :=
    (X.evaluation U η.1.1 η.2).hom.toAlgebra
  letI : Algebra Γ(X, U) (minimalPrimeResidueFieldProduct Γ(X, U)) :=
    (minimalPrimeResidueFieldProductHom Γ(X, U)).toAlgebra
  let e := hU.genericPointResidueFieldsAlgEquivMinimalPrimeResidueFieldProduct
  (normalizationSectionsRingEquivIntegralClosurePiResidueField hX U hU).trans
    e.mapIntegralClosure.toRingEquiv

end AlgebraicGeometry

end
