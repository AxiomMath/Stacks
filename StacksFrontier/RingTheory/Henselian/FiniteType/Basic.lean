module

public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic.EtaleSection
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic.QuasiFiniteSplit
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic.ArtinianIdempotents
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic.ProductOfLocalRings

/-!
# Decomposition of a finite type algebra over a henselian local ring
-/

/-!
# Decomposition of a finite type algebra over a henselian local ring

Stacks Tag 04GJ (Lemma 10.153.5). Let `(R, 𝔪, κ)` be a henselian local ring and let `S` be
any finite type `R`-algebra. Then there exist a natural number `n`, commutative `R`-algebras
`A₁, …, A_n` (indexed by `i : Fin n`), each local and finite over `R`, and a commutative
`R`-algebra `B` such that `R → B` is not quasi-finite at any prime of `B` lying over `𝔪`,
together with an `R`-algebra isomorphism `S ≃ₐ[R] (Π i : Fin n, Aᵢ) × B`; that is, `S` is
isomorphic as an `R`-algebra to the product `A₁ × ⋯ × A_n × B`.

## Vocabulary

* A henselian local ring is `HenselianLocalRing R`, a finite type algebra is
  `Algebra.FiniteType R S`, a finite algebra is `Module.Finite R A`, and a local ring is
  `IsLocalRing A`.
* That `𝔮` lies over `𝔪` is `Ideal.LiesOver 𝔮 𝔪`, equivalently
  `𝔮.comap (algebraMap R B) = 𝔪`.
* Quasi-finiteness at a prime is `Algebra.QuasiFiniteAt R 𝔮`, defined as
  `Algebra.QuasiFinite R (Localization.AtPrime 𝔮)`. Thus `R → B` is not quasi-finite at any
  prime of `B` lying over `𝔪` exactly when `Algebra.QuasiFiniteAt R 𝔮` fails for every prime
  `𝔮` of `B` with `𝔮.comap (algebraMap R B) = 𝔪`.

## Formalization choices

* The finite product `A₁ × ⋯ × A_n` is encoded as the indexed product `Π i : Fin n, Aᵢ`, and
  the full decomposition as `(Π i : Fin n, Aᵢ) × B`. The number `n`, the family `A`, the
  algebra `B` and all their ring and algebra structures are existentially quantified;
  `n = 0` is allowed, in which case `S ≃ₐ[R] B`.
* "Isomorphic" is rendered as an `R`-algebra isomorphism `≃ₐ[R]`, packaged as
  `Nonempty (S ≃ₐ[R] (Π i, A i) × B)`.
* No finiteness, locality or nonzeroness condition is imposed on `B`; the only condition is
  the non-quasi-finiteness at primes over `𝔪`.
* The factor types `A i` and `B` live in universe `max u v` (where `R : Type u` and
  `S : Type v`) so that, for instance, copies of `S` itself are admissible factors.

## Parts

* `Basic/EtaleSection`: transport of non-quasi-finiteness, idempotent splittings, finiteness of
  the quasi-finite primes over `𝔪`, and henselian étale sections at a residue point.
* `Basic/QuasiFiniteSplit`: isolating idempotents and the split `S ≃ₐ[R] A × B`.
* `Basic/ArtinianIdempotents`: idempotents of the Artinian closed fibre of a module-finite algebra.
* `Basic/ProductOfLocalRings`: lifting idempotents, the product of local rings, and Tag 04GJ.
-/
