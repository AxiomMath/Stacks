module

public import StacksFrontier.RingTheory.IntegralClosure.DedekindDomain
public import StacksFrontier.RingTheory.IntegrallyClosed.ProductOfDomains
public import Mathlib.RingTheory.TensorProduct.Pi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite products of Dedekind domains

A Noetherian normal ring of Krull dimension at most one is a finite product of Dedekind domains,
and the integral closure of a Noetherian ring of dimension at most one in the residue field of a
prime is quasi-finite over it.

## Main definitions

* `Stacks.IsFiniteProductOfDedekindDomains`: a ring is isomorphic to a product of finitely many
  Dedekind domains.

## Main results

* `Stacks.isFiniteProductOfDedekindDomains_of_isNormalRing`: a Noetherian normal ring of Krull
  dimension at most one is a finite product of Dedekind domains.
* `Algebra.QuasiFinite.pi`: a finite product of quasi-finite algebras is quasi-finite.
* `Stacks.quasiFinite_integralClosure_residueField_quotient`: for a prime `p` of a Noetherian
  ring `A` of dimension at most one, the integral closure of `A ⧸ p` in the residue field of `p`
  is quasi-finite over `A`.

## Implementation notes

The predicate allows the empty product, that is the zero ring, which
`IsDiscreteValuationRing.IsFiniteProductOfDedekindDomains` excludes by requiring a positive
number of factors. The empty affine open of a scheme has the zero ring for its sections, so the
empty product cannot be excluded from a statement quantified over all affine opens.

The normal case rests on tag 030C in the form
`isIntegrallyClosed_tfae_of_finite_minimalPrimes`: a reduced ring with finitely many minimal
primes is normal exactly when the canonical map to the product of the quotients by its minimal
primes is bijective and each quotient is integrally closed. Over a Noetherian ring of dimension
at most one each of those quotients is a Noetherian integrally closed domain of dimension at
most one, that is a Dedekind domain.

Quasi-finiteness of the integral closure is Krull–Akizuki,
`IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite` (tag 09IG), applied
with the trivial extension `κ(p) / κ(p)` of the fraction field of `A ⧸ p`, composed with the
quasi-finiteness of the surjection `A → A ⧸ p`.

## References

* [Stacks Project, Tag 030C](https://stacks.math.columbia.edu/tag/030C)
* [Stacks Project, Tag 09IG](https://stacks.math.columbia.edu/tag/09IG)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Stacks

/-- The quotient of a ring of Krull dimension at most one by a prime has dimension at most one. -/
private theorem dimensionLEOne_quotient {R : Type*} [CommRing R] (hdim : Ring.KrullDimLE 1 R)
    (p : Ideal R) [p.IsPrime] : Ring.DimensionLEOne (R ⧸ p) :=
  have : Ring.KrullDimLE 1 (R ⧸ p) :=
    Ring.krullDimLE_iff.mpr ((ringKrullDim_quotient_le p).trans (Ring.krullDimLE_iff.mp hdim))
  ⟨fun hq hqp => hqp.isMaximal_of_ne_bot hq⟩

/-- A ring is a **finite product of Dedekind domains** if it is isomorphic to a product of
finitely many Dedekind domains. The empty product, the zero ring, is allowed. -/
def IsFiniteProductOfDedekindDomains (R : Type u) [CommRing R] : Prop :=
  ∃ (n : ℕ) (D : Fin n → Type u) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, IsDedekindDomain (D i)),
    Nonempty (R ≃+* ∀ i, D i)

/-- Being a finite product of Dedekind domains transports along a ring isomorphism. -/
theorem IsFiniteProductOfDedekindDomains.congr {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (h : IsFiniteProductOfDedekindDomains R) :
    IsFiniteProductOfDedekindDomains S := by
  obtain ⟨n, D, hcr, hded, ⟨f⟩⟩ := h
  exact ⟨n, D, hcr, hded, ⟨e.symm.trans f⟩⟩

/-- The zero ring is the empty product of Dedekind domains. -/
theorem isFiniteProductOfDedekindDomains_of_subsingleton (R : Type u) [CommRing R]
    [Subsingleton R] : IsFiniteProductOfDedekindDomains R := by
  let D : Fin 0 → Type u := fun i => i.elim0
  let hcr : ∀ i, CommRing (D i) := fun i => i.elim0
  have : Subsingleton (∀ i, D i) := inferInstance
  refine ⟨0, D, hcr, fun i => i.elim0, ⟨?_⟩⟩
  exact
    { toFun := fun _ => 0
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      map_add' := fun _ _ => Subsingleton.elim _ _ }

/-- A finite product of Dedekind domains is Noetherian. -/
@[ega "III 7.4.3" "partial"]
theorem IsFiniteProductOfDedekindDomains.isNoetherianRing {R : Type u} [CommRing R]
    (h : IsFiniteProductOfDedekindDomains R) : IsNoetherianRing R := by
  obtain ⟨n, D, hcr, hded, ⟨e⟩⟩ := h
  have : IsNoetherianRing (∀ i, D i) := inferInstance
  exact isNoetherianRing_of_ringEquiv _ e.symm

/-- **A Noetherian normal ring of dimension at most one is a finite product of Dedekind
domains.** By tag 030C it is the product of the quotients by its finitely many minimal primes,
and each of those is an integrally closed Noetherian domain of dimension at most one. -/
@[ega "III 7.4.3" "more general", ega "IV 5.13.5" "special case"]
theorem isFiniteProductOfDedekindDomains_of_isNormalRing {R : Type u} [CommRing R]
    [IsNoetherianRing R] (hdim : Ring.KrullDimLE 1 R) (hR : IsNormalRing R) :
    IsFiniteProductOfDedekindDomains R := by
  classical
  have : IsReduced R := hR.isReduced
  have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  have hfinite : Finite (minimalPrimes R) := hfin
  obtain ⟨hic, hbij⟩ :=
    ((isIntegrallyClosed_tfae_of_finite_minimalPrimes hfin).out 1 4).mp
      (isNormalRing_iff.mp hR)
  have hded : ∀ p ∈ minimalPrimes R, IsDedekindDomain (R ⧸ p) := by
    intro p hp
    have hpp : p.IsPrime := hp.1.1
    have := dimensionLEOne_quotient hdim p
    have : IsIntegrallyClosed (R ⧸ p) := hic p hp
    exact (isDedekindDomain_iff (R ⧸ p) (FractionRing (R ⧸ p))).2
      ⟨inferInstance, inferInstance, inferInstance,
        (isIntegrallyClosed_iff (FractionRing (R ⧸ p))).mp inferInstance⟩
  let ε := Finite.equivFin (minimalPrimes R)
  exact ⟨Nat.card (minimalPrimes R),
    fun k => R ⧸ ((ε.symm k : minimalPrimes R) : Ideal R),
    fun _ => inferInstance, fun k => hded _ (ε.symm k).2,
    ⟨(RingEquiv.ofBijective _ hbij).trans
      (RingEquiv.piCongrLeft (fun p : minimalPrimes R => R ⧸ (p : Ideal R)) ε.symm).symm⟩⟩

end Stacks

/-- **A finite product of quasi-finite algebras is quasi-finite.** The fibre of the product is
the product of the fibres. -/
instance Algebra.QuasiFinite.pi {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Algebra.QuasiFinite R (S i)] : Algebra.QuasiFinite R (∀ i, S i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  refine ⟨fun P hP => ?_⟩
  have hfin : Module.Finite P.ResidueField (∀ i, P.ResidueField ⊗[R] S i) :=
    Module.Finite.pi
  exact Module.Finite.equiv
    (Algebra.TensorProduct.piRight R P.ResidueField P.ResidueField S).symm.toLinearEquiv

namespace Stacks

/-- **The integral closure of `A ⧸ p` in the residue field of `p` is quasi-finite over `A`**, for
`p` a prime of a Noetherian ring `A` of Krull dimension at most one. This is Krull–Akizuki,
composed with the quasi-finiteness of the surjection `A → A ⧸ p`. -/
theorem quasiFinite_integralClosure_residueField_quotient (A : Type u) [CommRing A]
    [IsNoetherianRing A] (hdim : Ring.KrullDimLE 1 A) (p : Ideal A) [hp : p.IsPrime] :
    letI : Algebra A (integralClosure (A ⧸ p) p.ResidueField) :=
      ((algebraMap (A ⧸ p) (integralClosure (A ⧸ p) p.ResidueField)).comp
        (Ideal.Quotient.mk p)).toAlgebra
    Algebra.QuasiFinite A (integralClosure (A ⧸ p) p.ResidueField) := by
  let : Algebra A (integralClosure (A ⧸ p) p.ResidueField) :=
    ((algebraMap (A ⧸ p) (integralClosure (A ⧸ p) p.ResidueField)).comp
      (Ideal.Quotient.mk p)).toAlgebra
  have := dimensionLEOne_quotient hdim p
  have hqf : Algebra.QuasiFinite (A ⧸ p) (integralClosure (A ⧸ p) p.ResidueField) :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
      (A ⧸ p) p.ResidueField p.ResidueField (integralClosure (A ⧸ p) p.ResidueField)).2.2
  have : IsScalarTower A (A ⧸ p) (integralClosure (A ⧸ p) p.ResidueField) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite A (A ⧸ p) := inferInstance
  exact Algebra.QuasiFinite.trans A (A ⧸ p) (integralClosure (A ⧸ p) p.ResidueField)


/-- **A quotient of a quasi-finite algebra over a local ring is a finite extension of the
residue field.** The fibre `κ(𝔪) ⊗_A C` of a quasi-finite algebra is a finite `κ(𝔪)`-module,
hence a finite `A`-module, and `D` is a quotient of it. -/
theorem finite_residueField_of_quasiFinite {A C D : Type*} [CommRing A] [IsLocalRing A]
    [CommRing C] [Algebra A C] [Algebra.QuasiFinite A C] [CommRing D] [Algebra A D]
    [Algebra (IsLocalRing.ResidueField A) D]
    [IsScalarTower A (IsLocalRing.ResidueField A) D]
    (g : C →ₐ[A] D) (hg : Function.Surjective g) :
    Module.Finite (IsLocalRing.ResidueField A) D := by
  have eκ : (IsLocalRing.maximalIdeal A).ResidueField ≃ₐ[A] IsLocalRing.ResidueField A :=
    (AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective
      (algebraMap (A ⧸ IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal A).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal A)))
      fun a => (IsScalarTower.algebraMap_apply A (A ⧸ IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal A).ResidueField a).symm).symm
  have : Module.Finite (IsLocalRing.maximalIdeal A).ResidueField
      ((IsLocalRing.maximalIdeal A).Fiber C) :=
    Algebra.QuasiFinite.finite_fiber (IsLocalRing.maximalIdeal A)
  have : Module.Finite A (IsLocalRing.ResidueField A) := inferInstance
  have : Module.Finite A (IsLocalRing.maximalIdeal A).ResidueField :=
    Module.Finite.of_surjective eκ.symm.toLinearMap eκ.symm.surjective
  have : Module.Finite A ((IsLocalRing.maximalIdeal A).Fiber C) :=
    Module.Finite.trans (IsLocalRing.maximalIdeal A).ResidueField
      ((IsLocalRing.maximalIdeal A).Fiber C)
  let hlift := Algebra.TensorProduct.lift
    ((IsScalarTower.toAlgHom A (IsLocalRing.ResidueField A) D).comp eκ.toAlgHom) g
    fun _ _ => Commute.all _ _
  have hsurj : Function.Surjective hlift := by
    intro z
    obtain ⟨c, rfl⟩ := hg z
    refine ⟨(1 : (IsLocalRing.maximalIdeal A).ResidueField) ⊗ₜ c, ?_⟩
    show hlift ((1 : (IsLocalRing.maximalIdeal A).ResidueField) ⊗ₜ c) = g c
    simp [hlift, Algebra.TensorProduct.lift_tmul]
  have : Module.Finite A D := Module.Finite.of_surjective hlift.toLinearMap hsurj
  exact Module.Finite.of_restrictScalars_finite A (IsLocalRing.ResidueField A) D

end Stacks

end
