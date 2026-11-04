module

public import StacksFrontier.RingTheory.Etale.AffineLineCovering
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.IntegrallyClosed.ProductOfDomains
public import StacksFrontier.RingTheory.Polynomial.DerivationFiniteExtension

/-!
# The affine line has no nontrivial connected finite étale covering in characteristic zero

Let `k` be an algebraically closed field of characteristic zero. Every finite étale
`k[X]`-algebra `B` whose spectrum is connected is `k[X]` itself: the structure map
`k[X] → B` is bijective.

This is the input "`𝐀¹_k` has no nontrivial connected finite étale coverings" of Stacks,
Remark 05ZI, whose details the source omits.

The proof: `B` is a normal ring, being étale over the normal domain `k[X]`; a normal Noetherian
ring with connected spectrum is a domain (Lemma 030C). The derivation `d/dX` extends to `B`
(`Polynomial.AffineLineCovering.derivB`), with kernel `k`
(`Polynomial.AffineLineCovering.mem_range_of_derivB_eq_zero`), and a finite extension of `k[X]`
carrying such a derivation is `k[X]` (`Polynomial.surjective_algebraMap_of_derivation`, which
analyses the pole at infinity).

## Main results

* `PrimeSpectrum.eq_zero_or_eq_one_of_isIdempotentElem`: on a ring with connected spectrum the
  only idempotents are `0` and `1`.
* `IsNormalRing.isDomain_of_connectedSpace`: a Noetherian normal ring with connected spectrum is
  a domain.
* `Polynomial.AffineLineCovering.bijective_algebraMap_of_etale`: the statement above.
-/

@[expose] public section

open Polynomial

/-- On a ring with connected spectrum the only idempotents are `0` and `1`. -/
theorem PrimeSpectrum.eq_zero_or_eq_one_of_isIdempotentElem {R : Type*} [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hzero {f : R} (hf : IsIdempotentElem f) (h : PrimeSpectrum.basicOpen f = ⊥) : f = 0 := by
    obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_eq_bot_iff f).mp h
    rw [← hf.pow_succ_eq n, pow_succ, hn, zero_mul]
  have hcl : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases _root_.isClopen_iff.mp hcl with h | h
  · exact Or.inl (hzero he (SetLike.coe_injective h))
  · right
    have h1 : PrimeSpectrum.basicOpen (1 - e) = ⊥ := by
      have hm : PrimeSpectrum.basicOpen (e * (1 - e)) = ⊥ := by
        rw [mul_sub, mul_one, he.eq, sub_self, PrimeSpectrum.basicOpen_zero]
      have ht : PrimeSpectrum.basicOpen e = ⊤ := SetLike.coe_injective (h.trans (by simp))
      rw [PrimeSpectrum.basicOpen_mul, ht, top_inf_eq] at hm
      exact hm
    exact (sub_eq_zero.mp (hzero he.one_sub h1)).symm

/-- **A Noetherian normal ring with connected spectrum is a domain.** By Lemma 030C it is a finite
product of domains, and a product of two or more nonzero rings has nontrivial idempotents. -/
theorem IsNormalRing.isDomain_of_connectedSpace {R : Type*} [CommRing R] [IsNoetherianRing R]
    (h : IsNormalRing R) [ConnectedSpace (PrimeSpectrum R)] : IsDomain R := by
  have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  have : IsReduced R := h.isReduced
  obtain ⟨n, A, _, hdom, -, ⟨e⟩⟩ :=
    ((isIntegrallyClosed_tfae_of_finite_minimalPrimes
      (minimalPrimes.finite_of_isNoetherianRing R)).out 1 3).mp (isNormalRing_iff.mp h)
  have hsingle (i : Fin n) : (Pi.single i 1 : ∀ j, A j) = 1 := by
    have hid : IsIdempotentElem (e.symm (Pi.single i 1)) := by
      rw [IsIdempotentElem, ← map_mul, ← Pi.single_mul, one_mul]
    rcases PrimeSpectrum.eq_zero_or_eq_one_of_isIdempotentElem hid with h0 | h1
    · have := congrArg (fun f ↦ f i) (e.symm.injective (h0.trans (map_zero e.symm).symm))
      simp at this
    · exact e.symm.injective (h1.trans (map_one e.symm).symm)
  have hn : n = 1 := by
    rcases Nat.lt_or_ge n 1 with h0 | h1
    · have : Subsingleton (∀ j : Fin n, A j) := by
        have : IsEmpty (Fin n) := by rw [Nat.lt_one_iff.mp h0]; infer_instance
        infer_instance
      exact absurd (e.injective (Subsingleton.elim _ _)) zero_ne_one
    · by_contra hne
      have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
      have := congrArg (fun f ↦ f ⟨1, by omega⟩) (hsingle ⟨0, by omega⟩)
      simp [h01.symm] at this
  subst hn
  exact Function.Injective.isDomain ((RingEquiv.piUnique A).toRingHom.comp e.toRingHom)
    ((RingEquiv.piUnique A).injective.comp e.injective)

namespace Polynomial.AffineLineCovering

/-- **The affine line over an algebraically closed field of characteristic zero has no nontrivial
connected finite étale covering** (Stacks, Remark 05ZI, details omitted there). Every finite étale
`k[X]`-algebra `B` with connected spectrum is `k[X]`: the structure map `k[X] → B` is bijective. -/
theorem bijective_algebraMap_of_etale {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    (B : Type*) [CommRing B] [Algebra k[X] B] [Algebra.Etale k[X] B] [Module.Finite k[X] B]
    [ConnectedSpace (PrimeSpectrum B)] : Function.Bijective (algebraMap k[X] B) := by
  let : Algebra k B := ((algebraMap k[X] B).comp (algebraMap k k[X])).toAlgebra
  have : IsScalarTower k k[X] B := .of_algebraMap_eq fun _ ↦ rfl
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k[X] B
  have : IsDomain B := (IsNormalRing.of_etale_of_isDomain k[X] B).isDomain_of_connectedSpace
  have hinj : Function.Injective (algebraMap k[X] B) :=
    Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance
  have : FaithfulSMul k[X] B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine ⟨hinj, surjective_algebraMap_of_derivation (derivB k B) ?_
    fun z hz ↦ mem_range_of_derivB_eq_zero hz⟩
  rw [derivB_algebraMap, derivative_X, map_one]

end Polynomial.AffineLineCovering
