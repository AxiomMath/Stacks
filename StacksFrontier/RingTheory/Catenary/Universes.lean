module

public import StacksFrontier.RingTheory.Catenary.Basic

/-!
# Universal catenarity for algebras in an arbitrary universe

`Ring.IsUniversallyCatenary R`, for `R : Type u`, quantifies over the finite-type `R`-algebras
living in `Type u`. This file removes that restriction: a universally catenary ring has catenary
finite-type algebras in *every* universe, and the consequences of universal catenarity that
mention a second ring — passage to a finite-type algebra and to the target of a surjection — hold
with that ring in an arbitrary universe.

## Main results

* `Ring.IsCatenary.of_ringEquiv`: catenarity transfers along a ring isomorphism between rings in
  different universes.
* `Ring.IsUniversallyCatenary.isCatenary_of_finiteType`: a finite-type algebra over a universally
  catenary ring is catenary, with no restriction on its universe.
* `Ring.isUniversallyCatenary_iff_forall_finiteType`: universal catenarity is equivalent to the
  same condition stated for the algebras of any larger universe.
* `Ring.IsUniversallyCatenary.of_finiteType` and `Ring.IsUniversallyCatenary.of_surjective'`: the
  cross-universe forms of the two inheritance statements.

## Implementation notes

Catenarity of a ring is a condition on the poset `PrimeSpectrum R` alone — a bound on the lengths
of the `LTSeries` between a comparable pair, and equality of the lengths of those whose steps are
covering pairs. Both clauses are carried by a map of posets which is an order isomorphism, in
either universe, because `LTSeries.map` preserves length, head and last and an order isomorphism
preserves the covering relation (`apply_covBy_apply_iff`). That is the content of
`Ring.IsCatenary.of_orderIso`, and `Ring.IsCatenary.of_ringEquiv` is its instance at
`PrimeSpectrum.comapEquiv`.

With that in hand the universe restriction in the definition is not a restriction on the notion,
which is what the definition's own docstring asserts: a finite-type algebra `C` over `R : Type u`
is the target of a surjection from `R[X₁, …, X_n]`, so it is isomorphic to the quotient of that
polynomial ring by the kernel, and that quotient lives in `Type u` and is of finite type over `R`.
Applying the definition to the quotient and transferring along the isomorphism gives catenarity of
`C` itself.

The equivalence `Ring.isUniversallyCatenary_iff_forall_finiteType` is stated for the algebras of
`Type (max u v)` rather than of an unrelated `Type v`: its reverse direction instantiates the
hypothesis at `ULift.{v} C`, and no comparable model of a `Type u`-algebra exists in a universe
not containing `u`.

## References

* [Stacks Project, Tag 00NL](https://stacks.math.columbia.edu/tag/00NL)
-/

@[expose] public section

universe u v

namespace Ring

/-- Catenarity is a condition on the poset of primes, so it transfers along any order
isomorphism between the prime spectra, in particular between rings in different universes. -/
theorem IsCatenary.of_orderIso {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (e : PrimeSpectrum B ≃o PrimeSpectrum A) (hA : IsCatenary A) : IsCatenary B := by
  intro p q hpq
  obtain ⟨⟨N, hN⟩, ⟨n, hn⟩⟩ := hA (e p) (e q) (e.monotone hpq)
  refine ⟨⟨N, fun s hhead hlast => ?_⟩, ⟨n, fun s hhead hlast hcov => ?_⟩⟩
  · simpa using hN (s.map e e.strictMono) (by simp [hhead]) (by simp [hlast])
  · simpa using hn (s.map e e.strictMono) (by simp [hhead]) (by simp [hlast])
      fun i => (apply_covBy_apply_iff e).mpr (hcov i)

/-- Catenarity transfers along a ring isomorphism, whose source and target may live in different
universes. -/
theorem IsCatenary.of_ringEquiv {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (e : A ≃+* B) (hA : IsCatenary A) : IsCatenary B :=
  IsCatenary.of_orderIso (PrimeSpectrum.comapEquiv e.symm) hA

/-- **Universal catenarity is not restricted to the universe of the ring.** Every finite-type
algebra over a universally catenary ring is catenary, whatever universe it lives in: it is
isomorphic to a quotient of a polynomial ring over `R` in finitely many variables, which lives in
the universe of `R`. -/
theorem IsUniversallyCatenary.isCatenary_of_finiteType {R : Type u} [CommRing R]
    (hR : IsUniversallyCatenary R) (C : Type v) [CommRing C] [Algebra R C]
    [Algebra.FiniteType R C] : IsCatenary C := by
  obtain ⟨n, f, hf⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType R C›
  have hfr : Function.Surjective (f : MvPolynomial (Fin n) R →+* C) := hf
  set I : Ideal (MvPolynomial (Fin n) R) := RingHom.ker (f : MvPolynomial (Fin n) R →+* C) with hI
  have : Algebra.FiniteType R (MvPolynomial (Fin n) R ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ_surjective R I)
  exact IsCatenary.of_ringEquiv (RingHom.quotientKerEquivOfSurjective hfr) (hR _)

/-- A finite-type algebra over a universally catenary ring is universally catenary, with no
restriction on its universe. -/
theorem IsUniversallyCatenary.of_finiteType {R : Type u} {C : Type v} [CommRing R] [CommRing C]
    [Algebra R C] [Algebra.FiniteType R C] (hR : IsUniversallyCatenary R) :
    IsUniversallyCatenary C := by
  intro D _ _ _
  let _ : Algebra R D := ((algebraMap C D).comp (algebraMap R C)).toAlgebra
  have : IsScalarTower R C D := .of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType R D := Algebra.FiniteType.trans ‹Algebra.FiniteType R C› ‹_›
  exact hR.isCatenary_of_finiteType D

/-- **The target of a surjection out of a universally catenary ring is universally catenary**,
with no restriction on its universe. This is the cross-universe form of
`Ring.IsUniversallyCatenary.of_surjective`. -/
theorem IsUniversallyCatenary.of_surjective' {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : Function.Surjective f) (hA : IsUniversallyCatenary A) :
    IsUniversallyCatenary B := by
  let _ : Algebra A B := f.toAlgebra
  have : Algebra.FiniteType A B :=
    Algebra.FiniteType.of_surjective (Algebra.ofId A B) hf
  exact hA.of_finiteType

/-- Universal catenarity of `R : Type u` is equivalent to catenarity of every finite-type
`R`-algebra in `Type (max u v)`. The definition's universe restriction is therefore no
restriction on the notion. -/
theorem isUniversallyCatenary_iff_forall_finiteType {R : Type u} [CommRing R] :
    IsUniversallyCatenary R ↔
      ∀ (C : Type (max u v)) [CommRing C] [Algebra R C] [Algebra.FiniteType R C],
        IsCatenary C := by
  refine ⟨fun hR C _ _ _ => hR.isCatenary_of_finiteType C, fun h C _ _ _ => ?_⟩
  have e : ULift.{v} C ≃ₐ[R] C := ULift.algEquiv
  have : Algebra.FiniteType R (ULift.{v} C) := ‹Algebra.FiniteType R C›.equiv e.symm
  exact IsCatenary.of_ringEquiv e.toRingEquiv (h (ULift.{v} C))

end Ring

end
