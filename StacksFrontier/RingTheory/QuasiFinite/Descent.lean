module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Descent of quasi-finiteness along faithfully flat ring maps

Let `R → T` be a faithfully flat ring map and let `S` be an `R`-algebra. This file shows that if
`T ⊗[R] S` is quasi-finite over `T`, then `S` is quasi-finite over `R`, and deduces the
corresponding `RingHom.CodescendsAlong` statement.

This completes the family of descent results of `Mathlib/RingTheory/Finiteness/Descent.lean` (for
`Module.Finite`, `Algebra.FiniteType` and `Algebra.FinitePresentation`) and of
`Mathlib/RingTheory/Etale/Descent.lean` (for smooth, unramified and étale algebras), from which
`Algebra.QuasiFinite` is absent.

## Main results

* `Algebra.QuasiFinite.of_quasiFinite_tensorProduct_of_faithfullyFlat`: quasi-finiteness of
  algebras descends along faithfully flat base change.
* `RingHom.QuasiFinite.codescendsAlong_faithfullyFlat`: the same statement in the form
  `RingHom.CodescendsAlong RingHom.QuasiFinite RingHom.FaithfullyFlat`, which is the shape
  consumed by `AlgebraicGeometry.HasRingHomProperty.descendsAlong_flat`.

## Implementation notes

`Algebra.QuasiFinite R S` asks that the fibre `κ(p) ⊗[R] S` be a finite `κ(p)`-module for every
prime `p` of `R`. Since `R → T` is faithfully flat, every such `p` is of the form `q.under R` for
a prime `q` of `T` (`Ideal.exists_isPrime_liesOver_of_faithfullyFlat`), and the fibre of
`T ⊗[R] S` at `q` is `κ(q) ⊗[κ(p)] (κ(p) ⊗[R] S)`; this is the identification already used in
the proof of `Algebra.QuasiFinite.baseChange`, and it is assembled from
`Algebra.TensorProduct.cancelBaseChange` on both sides. The `κ(p)`-algebra structure on `κ(q)` is
the one induced by `Localization.AtPrime.algebraOfLiesOver`, which is deliberately not an instance
in Mathlib and so has to be introduced by hand. Faithful flatness of `κ(p) → κ(q)` is automatic,
`κ(q)` being a nontrivial module over a field, so
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` applies.

## References

* [Stacks Project, Tag 02KO](https://stacks.math.columbia.edu/tag/02KO)
-/

@[expose] public section

open TensorProduct

universe u

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (T : Type*) [CommRing T] [Algebra R T]

/-- If `T` is a faithfully flat `R`-algebra and `T ⊗[R] S` is quasi-finite over `T`, then `S` is
quasi-finite over `R`. -/
lemma Algebra.QuasiFinite.of_quasiFinite_tensorProduct_of_faithfullyFlat
    [Module.FaithfullyFlat R T] [Algebra.QuasiFinite T (T ⊗[R] S)] :
    Algebra.QuasiFinite R S := by
  refine ⟨fun p hp ↦ ?_⟩
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := T) p
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  let e : q.Fiber (T ⊗[R] S) ≃ₐ[q.ResidueField]
      q.ResidueField ⊗[p.ResidueField] p.Fiber S :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  have : Module.Finite q.ResidueField (q.ResidueField ⊗[p.ResidueField] p.Fiber S) :=
    .of_surjective e.toLinearMap e.surjective
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat q.ResidueField

/-- Quasi-finiteness of ring homomorphisms codescends along faithfully flat ring maps: if
`R → T` is faithfully flat and `T → T ⊗[R] S` is quasi-finite, then `R → S` is quasi-finite. -/
lemma RingHom.QuasiFinite.codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.QuasiFinite RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.QuasiFinite.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.quasiFinite_algebraMap] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  exact .of_quasiFinite_tensorProduct_of_faithfullyFlat S

end
