module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.RingTheory.Branches.MinimalPrimes
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
public import StacksCore.Tactic.StacksAttribute

/-!
# The total ring of fractions and its integral closure

Normalizing a reduced scheme over an affine open `Spec A` amounts to taking the integral
closure of `A` inside its total ring of fractions. This module assembles the ring theory that
computation needs.

Three steps. First, if every quasi-compact open of a scheme has finitely many irreducible
components, then a ring presenting an affine open has finitely many minimal primes. Second,
for a reduced ring with finitely many minimal primes the total ring of fractions is the
product, over those primes, of the fraction fields of the corresponding quotients. Third, the
integral closure of the ring in that product is the product of the integral closures of those
quotients in their fraction fields.

## Main results

* `AlgebraicGeometry.finite_minimalPrimes_of_affine_open`: a ring presenting an affine open of
  such a scheme has finitely many minimal primes.
* `minimalPrimes.totalFractionRing_algEquiv_pi_fractionRing_quotient`: the product
  decomposition of the total ring of fractions.
* `minimalPrimes.integralClosure_fractionRing_algEquiv_pi_quotient`: the product decomposition
  of the integral closure.

## Implementation notes

The identification `Spec A = U` is an isomorphism from `Spec A` to the open subscheme attached
to `U`, and finiteness of the irreducible components of an open is stated for its underlying
subtype. The conclusion uses the set `minimalPrimes A`, so it can be enumerated by a finite
type whenever a later result needs a list of the primes. The source assumes that the scheme is
reduced, but neither the argument nor the conclusion of the first result uses that, so it is
stated without it.

The products are indexed by the subtype `minimalPrimes A` rather than by a chosen enumeration.
Each factor carries its canonical `A`-algebra structure, through the quotient map and then the
fraction-ring map, so the equivalences record that the decompositions commute with the
canonical maps out of `A`. The geometric setting of the source supplies only reducedness and
finiteness of the minimal primes, so the last two results are stated for any ring with those
two properties.

## References

* [Stacks Project, Tag 035P](https://stacks.math.columbia.edu/tag/035P)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If every quasi-compact open of a scheme has finitely many irreducible components,
then a ring presenting an affine open of that scheme has finitely many minimal primes. -/
@[stacks 035P "minimal_primes"]
theorem finite_minimalPrimes_of_affine_open
    {X : Scheme.{u}}
    {A : Type u} [CommRing A]
    (hX : ∀ (V : X.Opens), IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (U : X.Opens) (e : Spec (.of A) ≅ (U : Scheme)) :
    (minimalPrimes A).Finite := by
  let f := e.hom.homeomorph
  have hU : IsAffineOpen U := .of_isIso e.inv
  have : Finite ↑(irreducibleComponents U) := (hX U hU.isCompact).to_subtype
  let ce := irreducibleComponentsEquivOfIsPreirreducibleFiber
    (f := f) f.continuous f.isOpenMap
      (fun x => (Set.subsingleton_singleton.preimage f.injective).isPreirreducible) f.surjective
  exact Set.finite_coe_iff.mp <|
    Finite.of_equiv _ (ce.toEquiv.trans (minimalPrimes.equivIrreducibleComponents A).symm.toEquiv)

end AlgebraicGeometry

namespace minimalPrimes

/-- The canonical `A`-algebra map from the quotient by a minimal prime of a reduced ring into
the localization at that prime. -/
private noncomputable def quotientToAtPrime
    {A : Type*} [CommRing A] {p : Ideal A} [p.IsPrime]
    (hp : p ∈ minimalPrimes A) [IsReduced A] :
    (A ⧸ p) →ₐ[A] Localization.AtPrime p :=
  Ideal.Quotient.liftₐ p
    { toRingHom := algebraMap A (Localization.AtPrime p)
      commutes' := fun _ => rfl }
    (fun x hx => algebraMap_eq_zero_of_mem_minimalPrime A p hp x hx)

private lemma quotientToAtPrime_injective
    {A : Type*} [CommRing A] {p : Ideal A} [p.IsPrime]
    (hp : p ∈ minimalPrimes A) [IsReduced A] :
    Function.Injective (quotientToAtPrime hp) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hzero : algebraMap A (Localization.AtPrime p) (x - y) = 0 :=
    (map_sub _ x y).trans (sub_eq_zero.mpr hxy)
  obtain ⟨s, hs⟩ := (algebraMap_eq_zero_iff_atPrime (R := A) p (x - y)).mp hzero
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem x y).2
    (mem_prime_of_smul_eq_zero A p (x - y) s s.property hs)

/-- The localization of a reduced ring at a minimal prime is the fraction field of the
quotient by that prime. -/
private theorem quotientToAtPrimeFractionRing
    {A : Type*} [CommRing A] {p : Ideal A} [p.IsPrime]
    (hp : p ∈ minimalPrimes A) [IsReduced A] :
    letI : Algebra (A ⧸ p) (Localization.AtPrime p) := (quotientToAtPrime hp).toAlgebra
    IsFractionRing (A ⧸ p) (Localization.AtPrime p) := by
  let : Algebra (A ⧸ p) (Localization.AtPrime p) := (quotientToAtPrime hp).toAlgebra
  let : Field (Localization.AtPrime p) :=
    (isField_localizationAtPrime_of_minimal A p hp).toField
  have : FaithfulSMul (A ⧸ p) (Localization.AtPrime p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (quotientToAtPrime_injective hp)
  refine @IsFractionRing.of_field (A ⧸ p) _ (Localization.AtPrime p) _ _ _ fun z => ?_
  obtain ⟨x, hx⟩ := IsLocalization.surj p.primeCompl z
  have hsm : algebraMap (A ⧸ p) (Localization.AtPrime p)
      (Ideal.Quotient.mk p (x.2 : A)) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr
      fun h => x.2.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  exact ⟨Ideal.Quotient.mk p x.1, Ideal.Quotient.mk p (x.2 : A), (eq_div_iff hsm).2 hx⟩

/-- The `A`-algebra structure on an `A ⧸ I`-algebra, through the quotient map. -/
private abbrev algebraOfQuotient {A : Type*} [CommRing A] (I : Ideal A) (S : Type*) [CommRing S]
    [Algebra (A ⧸ I) S] : Algebra A S :=
  ((algebraMap (A ⧸ I) S).comp (Ideal.Quotient.mk I)).toAlgebra

/-- The total ring of fractions of a reduced ring with finitely many minimal primes is the
product of the fraction fields of its minimal-prime quotients. -/
@[stacks 035P "total_fraction_ring", ega "II 6.5.1" "partial"]
theorem totalFractionRing_algEquiv_pi_fractionRing_quotient
    {A : Type*} [CommRing A] [IsReduced A] (hA : (minimalPrimes A).Finite) :
    letI : (p : minimalPrimes A) → Algebra A (FractionRing (A ⧸ (p : Ideal A))) :=
      fun p => ((algebraMap (A ⧸ (p : Ideal A)) (FractionRing (A ⧸ (p : Ideal A)))).comp
        (Ideal.Quotient.mk (p : Ideal A))).toAlgebra
    Nonempty (FractionRing A ≃ₐ[A]
      (∀ p : minimalPrimes A, FractionRing (A ⧸ (p : Ideal A)))) := by
  have : Finite (minimalPrimes A) := hA
  have : ∀ p : minimalPrimes A, (p : Ideal A).IsPrime :=
    fun p => p.property.left.left
  let : (p : minimalPrimes A) → Algebra A (FractionRing (A ⧸ (p : Ideal A))) :=
    fun p => algebraOfQuotient (p : Ideal A) _
  have : IsLocalization (nonZeroDivisors A)
      (∀ p : minimalPrimes A, Localization.AtPrime (p : Ideal A)) :=
    isLocalization_pi_localization_atPrime (fun p : minimalPrimes A => (p : Ideal A))
      (fun p => p.property) Subtype.val_injective (fun p hp => ⟨⟨p, hp⟩, rfl⟩)
  let e := IsLocalization.algEquiv (nonZeroDivisors A) (FractionRing A)
    (∀ p : minimalPrimes A, Localization.AtPrime (p : Ideal A))
  let eloc : (∀ p : minimalPrimes A, FractionRing (A ⧸ (p : Ideal A))) ≃ₐ[A]
      (∀ p : minimalPrimes A, Localization.AtPrime (p : Ideal A)) :=
    AlgEquiv.piCongrRight (fun p : minimalPrimes A => by
      let : Algebra (A ⧸ (p : Ideal A)) (Localization.AtPrime (p : Ideal A)) :=
        (quotientToAtPrime p.property).toAlgebra
      have : IsFractionRing (A ⧸ (p : Ideal A)) (Localization.AtPrime (p : Ideal A)) :=
        quotientToAtPrimeFractionRing p.property
      let f := IsLocalization.algEquiv (nonZeroDivisors (A ⧸ (p : Ideal A)))
        (FractionRing (A ⧸ (p : Ideal A))) (Localization.AtPrime (p : Ideal A))
      exact AlgEquiv.ofRingEquiv (f := f.toRingEquiv) fun x => f.commutes (Ideal.Quotient.mk _ x))
  exact ⟨e.trans eloc.symm⟩

/-- The integral closure in a finite product is the product of the integral closures. -/
@[ega "II 6.3.6" "special case", ega "II 6.4.7" "more general"]
private noncomputable def integralClosurePiEquiv
    (R : Type*) [CommRing R] {ι : Type*} [Finite ι] (S : ι → Type*)
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] :
    integralClosure R (∀ i, S i) ≃ₐ[R] ∀ i, integralClosure R (S i) :=
  { toFun := fun x i ↦ ⟨x.1 i, (isIntegral_pi_iff_const x.1).mp x.2 i⟩
    invFun := fun x ↦ ⟨fun i ↦ (x i).1, (isIntegral_pi_iff_const _).mpr fun i ↦ (x i).2⟩
    left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl
    map_mul' := fun _ _ ↦ rfl, map_add' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl }

/-- Integrality over a ring and over a quotient of it agree, when the algebra structures are
compatible. -/
private theorem isIntegral_quotient_iff
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) [Algebra R S] [Algebra (R ⧸ I) S]
    (h : ∀ r : R, algebraMap R S r = algebraMap (R ⧸ I) S (Ideal.Quotient.mk I r))
    (x : S) : IsIntegral R x ↔ IsIntegral (R ⧸ I) x := by
  have : IsScalarTower R (R ⧸ I) S := IsScalarTower.of_algebraMap_eq h
  have : Algebra.IsIntegral R (R ⧸ I) :=
    Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective
  exact ⟨IsIntegral.tower_top, isIntegral_trans x⟩

/-- The integral closure over a ring and over a quotient of it agree, when the algebra
structures are compatible. -/
private noncomputable def integralClosureQuotientEquiv
    (R S : Type*) [CommRing R] [CommRing S] (I : Ideal R) [Algebra R S]
    [Algebra (R ⧸ I) S] [Algebra R (integralClosure (R ⧸ I) S)]
    (h : ∀ r : R, algebraMap R S r = algebraMap (R ⧸ I) S (Ideal.Quotient.mk I r)) :
    (∀ r : R, ((algebraMap R (integralClosure (R ⧸ I) S) r :
      integralClosure (R ⧸ I) S) : S) = algebraMap R S r) →
    integralClosure R S ≃ₐ[R] integralClosure (R ⧸ I) S :=
  fun h' ↦
  { toFun := fun x ↦ ⟨x.1, (isIntegral_quotient_iff I h x.1).mp x.2⟩
    invFun := fun x ↦ ⟨x.1, (isIntegral_quotient_iff I h x.1).mpr x.2⟩
    left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl
    map_mul' := fun _ _ ↦ rfl, map_add' := fun _ _ ↦ rfl
    commutes' := fun r ↦ Subtype.ext (h' r).symm }

/-- The integral closure of a reduced ring in its total fraction ring is the product of the
integral closures of its minimal-prime quotients in their fraction fields. -/
@[stacks 035P "integral_closure_product", ega "II 6.4.7" "integral closure product"]
theorem integralClosure_fractionRing_algEquiv_pi_quotient
    {A : Type*} [CommRing A] [IsReduced A] (hA : (minimalPrimes A).Finite) :
    letI : (p : minimalPrimes A) →
        Algebra A
          (integralClosure (A ⧸ (p : Ideal A)) (FractionRing (A ⧸ (p : Ideal A)))) :=
      fun p =>
        ((algebraMap (A ⧸ (p : Ideal A))
          (integralClosure (A ⧸ (p : Ideal A))
            (FractionRing (A ⧸ (p : Ideal A))))).comp
          (Ideal.Quotient.mk (p : Ideal A))).toAlgebra
    Nonempty
      (integralClosure A (FractionRing A) ≃ₐ[A]
        (∀ p : minimalPrimes A,
          integralClosure (A ⧸ (p : Ideal A)) (FractionRing (A ⧸ (p : Ideal A))))) := by
  classical
  have : Finite (minimalPrimes A) := hA
  let (p : minimalPrimes A) : Algebra A (FractionRing (A ⧸ (p : Ideal A))) :=
    algebraOfQuotient (p : Ideal A) _
  let (p : minimalPrimes A) : Algebra A
      (integralClosure (A ⧸ (p : Ideal A)) (FractionRing (A ⧸ (p : Ideal A)))) :=
    algebraOfQuotient (p : Ideal A) _
  obtain ⟨e⟩ := totalFractionRing_algEquiv_pi_fractionRing_quotient hA
  let e' :=
    ((integralClosure A (FractionRing A)).equivMapOfInjective e.toAlgHom e.injective).trans
      (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv e))
  exact ⟨e'.trans ((integralClosurePiEquiv A _).trans
    (AlgEquiv.piCongrRight fun p : minimalPrimes A ↦
      integralClosureQuotientEquiv A (FractionRing (A ⧸ (p : Ideal A))) (p : Ideal A)
        (fun _ ↦ rfl) (fun _ ↦ rfl)))⟩

end minimalPrimes
