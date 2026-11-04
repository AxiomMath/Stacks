module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.Stalk
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationFiber
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.IntegralClosure.DedekindDomain
public import StacksFrontier.RingTheory.IntegralClosure.Pi

/-!
# The normalization stalk of a one-dimensional Nagata scheme is semilocal and Dedekind

Let `X` be a Nagata scheme and `ν : X^ν ⟶ X` its normalization.  The stalk
`A' = (ν_* 𝒪_{X^ν})_x` has finitely many maximal ideals, because the fibre of the finite
morphism `ν` over `x` is finite and its points are exactly those maximal ideals.  If moreover
`X` has dimension one, then `A'` is a finite product of Dedekind domains: it is the integral
closure of the local ring `A = 𝒪_{X,x}` in the product of the residue fields of the minimal
primes of `A`, and that integral closure splits as the product over the minimal primes of the
integral closures of the one-dimensional Noetherian domains `A ⧸ p`.

## Main results

* `integralClosure_minimalPrimeResidueFieldProduct_ringEquiv_pi`: the integral closure of a ring
  in the product of its minimal-prime residue fields is the product of the integral closures.
* `isFiniteProductOfDedekindDomains_integralClosure_minimalPrimeResidueFieldProduct`: for a
  Noetherian ring of dimension at most one that integral closure is a finite product of Dedekind
  domains.
* `AlgebraicGeometry.finite_maximalSpectrum_normalizationPushforwardStalk`: the normalization
  stalk of a Nagata scheme is semilocal.
* `AlgebraicGeometry.isFiniteProductOfDedekindDomains_normalizationPushforwardStalk`: in
  dimension one it is a finite product of Dedekind domains.

## Implementation notes

Semilocality is finiteness of `MaximalSpectrum`, and the product decomposition is the existing
predicate `IsDiscreteValuationRing.IsFiniteProductOfDedekindDomains`.  Neither conclusion needs
the point to be closed, and semilocality does not need the dimension hypothesis.

The integral closure of `A` in a finite product of `A`-algebras is computed factorwise, because
integrality of a tuple is integrality of each of its entries; over the residue field of a
minimal prime `p`, integrality over `A` is integrality over `A ⧸ p`, since `A ⧸ p` is integral
over `A`.

The two purely ring-theoretic results would sit more naturally in `StacksFrontier/RingTheory/`;
they are kept here because `minimalPrimeResidueFieldProduct`, over which they are stated, is
declared alongside the normalization stalk.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

open Stacks.NormalizationStalkAmbient

/-- Over an algebra on which an ideal acts trivially, integrality over the ring and over its
quotient by that ideal agree, because the quotient is integral over the ring. -/
public theorem isIntegral_quotient_iff (R K : Type*) [CommRing R] [Field K] (I : Ideal R)
    [Algebra (R ⧸ I) K] [Algebra R K] [IsScalarTower R (R ⧸ I) K]
    (hmap : (algebraMap (R ⧸ I) K).comp (Ideal.Quotient.mk I) = algebraMap R K)
    (x : K) : IsIntegral R x ↔ IsIntegral (R ⧸ I) x := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · apply RingHom.isIntegralElem.of_comp (Ideal.Quotient.mk I) (algebraMap (R ⧸ I) K)
    rwa [hmap]
  · have : Algebra.IsIntegral R (R ⧸ I) :=
      ⟨RingHom.isIntegral_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective⟩
    exact isIntegral_trans (R := R) x hx

/-- The integral closure of a ring in the product of the residue fields of its minimal primes
is the product over the minimal primes of the integral closures in those residue fields. -/
public noncomputable def integralClosure_minimalPrimeResidueFieldProduct_ringEquiv_pi
    (A : Type*) [CommRing A] [Finite (minimalPrimes A)] :
    integralClosure A (minimalPrimeResidueFieldProduct A) ≃+*
      ∀ p : minimalPrimes A,
        integralClosure (A ⧸ p.1) (@Ideal.ResidueField A _ p.1 p.2.1.1) := by
  classical
  letI (p : minimalPrimes A) : p.1.IsPrime := p.2.1.1
  letI : Algebra A (∀ p : minimalPrimes A, p.1.ResidueField) :=
    (RingHom.pi fun p : minimalPrimes A => algebraMap A p.1.ResidueField).toAlgebra
  have key (p : minimalPrimes A) (y : p.1.ResidueField) :
      letI : Algebra A p.1.ResidueField := (algebraMap A p.1.ResidueField).toAlgebra
      IsIntegral A y ↔ IsIntegral (A ⧸ p.1) y := by
    let : Algebra A p.1.ResidueField := (algebraMap A p.1.ResidueField).toAlgebra
    have hmap : (algebraMap (A ⧸ p.1) p.1.ResidueField).comp
        (Ideal.Quotient.mk p.1) = algebraMap A p.1.ResidueField :=
      RingHom.ext fun _ => rfl
    have : IsScalarTower A (A ⧸ p.1) p.1.ResidueField :=
      IsScalarTower.of_algebraMap_eq' hmap
    exact isIntegral_quotient_iff A p.1.ResidueField p.1 hmap y
  refine
    { toFun := fun x p => ⟨x.1 p, (key p (x.1 p)).mp
        ((isIntegral_pi_iff_const (R := A)
          (S := fun p : minimalPrimes A => p.1.ResidueField) x.1).mp x.2 p)⟩
      invFun := fun y => ⟨fun p => (y p).1,
        (isIntegral_pi_iff_const (R := A)
          (S := fun p : minimalPrimes A => p.1.ResidueField)
          (fun p => (y p).1)).2 fun p => (key p (y p).1).mpr (y p).2⟩
      left_inv := fun x => Subtype.ext (funext fun _ => rfl)
      right_inv := fun _ => funext fun _ => Subtype.ext rfl
      map_mul' := fun _ _ => funext fun _ => rfl
      map_add' := fun _ _ => rfl }

/-- For a nontrivial Noetherian ring of Krull dimension at most one, the integral closure in the
product of the residue fields of its minimal primes is a finite product of Dedekind domains. -/
@[ega "0 23.2.7" "partial", ega "0 23.2.8" "special case"]
public theorem isFiniteProductOfDedekindDomains_integralClosure_minimalPrimeResidueFieldProduct
    (A : Type*) [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Nontrivial A] :
    IsDiscreteValuationRing.IsFiniteProductOfDedekindDomains
      (integralClosure A (minimalPrimeResidueFieldProduct A)) := by
  classical
  have : Finite (minimalPrimes A) := minimalPrimes.finite_of_isNoetherianRing A
  have hD (p : minimalPrimes A) : IsDedekindDomain
      (integralClosure (A ⧸ p.1) (@Ideal.ResidueField A _ p.1 p.2.1.1)) := by
    have : p.1.IsPrime := p.2.1.1
    have : Ring.KrullDimLE 1 (A ⧸ p.1) := Ring.krullDimLE_iff.mpr
      ((ringKrullDim_quotient_le p.1).trans (Ring.krullDimLE_iff.mp inferInstance))
    have : Ring.DimensionLEOne (A ⧸ p.1) :=
      ⟨fun hq hqprime => Ring.krullDimLE_one_iff_of_isPrime_bot.mp inferInstance _ hq hqprime⟩
    exact (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
      (A ⧸ p.1) p.1.ResidueField p.1.ResidueField
      (integralClosure (A ⧸ p.1) p.1.ResidueField)).1
  let : Fintype (minimalPrimes A) := Fintype.ofFinite _
  let eFin : Fin (Fintype.card (minimalPrimes A)) ≃ minimalPrimes A :=
    (Fintype.equivFin (minimalPrimes A)).symm
  refine ⟨Fintype.card (minimalPrimes A),
    fun i => integralClosure (A ⧸ (eFin i).1)
      (@Ideal.ResidueField A _ (eFin i).1 (eFin i).2.1.1),
    fun _ => inferInstance, fun i => hD (eFin i),
    Fintype.card_pos_iff.mpr (Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal A)) bot_ne_top),
    ⟨(integralClosure_minimalPrimeResidueFieldProduct_ringEquiv_pi A).trans
      (RingEquiv.piCongrLeft _ eFin).symm⟩⟩

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.NormalizationQuotient

/-- **Stacks Project, Tag 0C1R.** The stalk of the pushforward of the structure sheaf of the
normalization of a Nagata scheme is semilocal: it has finitely many maximal ideals.

The point is not assumed closed, and the dimension hypothesis of the source is not used. -/
@[stacks 0C1R "semilocal_dedekind"]
public theorem finite_maximalSpectrum_normalizationPushforwardStalk
    (X : Scheme.{u}) (hNagata : IsNagataScheme X)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    Finite (MaximalSpectrum (normalizationPushforwardStalk X hX x)) := by
  have : IsFinite (Scheme.normalization X hX) := Scheme.isFinite_normalization hNagata hX
  have : Finite {y : Scheme.normalizationScheme X hX //
      y ∈ (Scheme.normalization X hX).base ⁻¹' ({x} : Set X)} :=
    ((Scheme.normalization X hX).finite_preimage_singleton x).to_subtype
  have : Finite {y : Scheme.normalizationScheme X hX //
      Scheme.normalization X hX y = x} :=
    Finite.of_equiv {y : Scheme.normalizationScheme X hX //
      y ∈ (Scheme.normalization X hX).base ⁻¹' ({x} : Set X)}
      (Equiv.subtypeEquivRight fun _ => by simp)
  exact Finite.of_equiv _ (normalizationFiberEquivMaximalSpectrum X hX x).choose

/-- **Stacks Project, Tag 0C1R.** On a Nagata scheme of dimension one, the stalk of the
pushforward of the structure sheaf of the normalization is a finite product of Dedekind
domains.

The point is not assumed closed. -/
@[stacks 0C1R "semilocal_dedekind"]
public theorem isFiniteProductOfDedekindDomains_normalizationPushforwardStalk
    (X : Scheme.{u}) (hNagata : IsNagataScheme X) (hdim : topologicalKrullDim X = 1)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    IsDiscreteValuationRing.IsFiniteProductOfDedekindDomains
      (normalizationPushforwardStalk X hX x) := by
  let : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  have : IsNoetherianRing (X.presheaf.stalk x) := (stalk_isNagataRing X hNagata x).1
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr
    ((ringKrullDim_stalk_le_topologicalKrullDim X x).trans hdim.le)
  have (p : minimalPrimes (X.presheaf.stalk x)) : p.1.IsPrime := p.2.1.1
  let : Algebra (X.presheaf.stalk x)
      (minimalPrimeResidueFieldProduct (X.presheaf.stalk x)) :=
    (minimalPrimeResidueFieldProductHom (X.presheaf.stalk x)).toAlgebra
  obtain ⟨n, D, hComm, hDed, hn, ⟨e⟩⟩ :=
    isFiniteProductOfDedekindDomains_integralClosure_minimalPrimeResidueFieldProduct
      (X.presheaf.stalk x)
  exact ⟨n, D, hComm, hDed, hn,
    ⟨(normalizationStalkAlgEquivIntegralClosureMinimalPrimes X hX x).toRingEquiv.trans e⟩⟩

end AlgebraicGeometry
