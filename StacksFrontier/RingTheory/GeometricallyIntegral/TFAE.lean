module

import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

public import StacksFrontier.RingTheory.GeometricallyReduced.TFAE
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Criteria
public import StacksFrontier.RingTheory.GeometricallyIntegral.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric integrality is detected by the finite extensions, and by the algebraic closure

Let `k` be a field and let `S` be a `k`-algebra. By definition `S` is *geometrically integral
over `k`* when `S ⊗[k] k'` is a domain for every field extension `k'/k`. This condition is already
detected by the finite extensions of `k`, and even by the single extension `AlgebraicClosure k`.

At each test field `k'` the condition that `S ⊗[k] k'` be a domain splits into an irreducible and
a reduced half: the finite separable extensions and the algebraic closure detect irreducibility
of the spectrum (Lemma 037K), the finite purely inseparable extensions and the algebraic closure
detect reducedness (Lemma 030V).

## Main results

* `Algebra.isGeometricallyIntegral_tfae`: for a field `k` and a `k`-algebra `S` the following are
  equivalent: `S` is geometrically integral over `k`; `S ⊗[k] k'` is a domain for every field
  extension `k'/k`; `S ⊗[k] k'` is a domain for every finite extension `k'/k`; and
  `S ⊗[k] AlgebraicClosure k` is a domain.
* `Stacks.GeometricallyIntegral.Criteria.solution`: the same equivalence.

## Implementation notes

Item 1 is the predicate `Algebra.IsGeometricallyIntegral` (tag 05DX), which is Mathlib's
scheme-level `AlgebraicGeometry.GeometricallyIntegral` applied to `Spec S ⟶ Spec k`; item 2 is
the same condition as a statement about tensor products. Items 3 and 4 are the source's items (2)
and (3).

The tensor factors are in the source's order, `S ⊗[k] k'`. A finite extension is
`Module.Finite k k'`. The test fields `k'` are quantified over `Type u`, the universe of `k` and
`S`, as they are in `AlgebraicGeometry.geometrically`.

## References

* [Stacks Project, Tag 0FWF](https://stacks.math.columbia.edu/tag/0FWF)
-/

@[expose] public section

universe u

namespace Stacks.GeometricallyIntegral.Criteria

open TensorProduct

/-- A tensor product of algebras is a domain exactly when its spectrum is irreducible and the
tensor product of the same two factors *in the other order* is reduced. -/
private theorem isDomain_tensorProduct_iff_irreducibleSpace_and_isReduced {R A B : Type*}
    [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] :
    IsDomain (A ⊗[R] B) ↔
      IrreducibleSpace (PrimeSpectrum (A ⊗[R] B)) ∧ IsReduced (B ⊗[R] A) :=
  (isDomain_iff_irreducibleSpace_and_isReduced _).trans
    (and_congr_right' isReduced_tensorProduct_comm)

/-- **The finite extensions suffice.** If `S ⊗[k] k'` is a domain for every finite extension
`k'/k`, then `S ⊗[k] AlgebraicClosure k` is a domain. -/
private theorem isDomain_tensorProduct_algebraicClosure_of_finite (k S : Type u) [Field k]
    [CommRing S] [Algebra k S]
    (h : ∀ (k' : Type u) [Field k'] [Algebra k k'] [Module.Finite k k'], IsDomain (S ⊗[k] k')) :
    IsDomain (S ⊗[k] AlgebraicClosure k) := by
  have halves (k' : Type u) [Field k'] [Algebra k k'] [Module.Finite k k'] :
      IrreducibleSpace (PrimeSpectrum (S ⊗[k] k')) ∧ IsReduced (k' ⊗[k] S) :=
    isDomain_tensorProduct_iff_irreducibleSpace_and_isReduced.mp (h k')
  refine isDomain_tensorProduct_iff_irreducibleSpace_and_isReduced.mpr ⟨?_, ?_⟩
  · refine ((AlgebraicGeometry.geometricallyIrreducible_tfae k S (SeparableClosure k)
      (AlgebraicClosure k)).out 2 4).mp ?_
    intro k' _ _ _ _
    exact (halves k').1
  · refine ((Algebra.isGeometricallyReduced_tfae k (ringExpChar k) S
      (perfectClosure k (AlgebraicClosure k)) (AlgebraicClosure k)).out 1 4).mp ?_
    intro k' _ _ _ _
    exact (halves k').2

/-- **The algebraic closure suffices.** If `S ⊗[k] AlgebraicClosure k` is a domain, then
`S ⊗[k] k'` is a domain for every field extension `k'/k`. -/
@[ega "IV 4.3.9" "partial"]
private theorem isDomain_tensorProduct_of_algebraicClosure (k S : Type u) [Field k] [CommRing S]
    [Algebra k S] (h : IsDomain (S ⊗[k] AlgebraicClosure k)) (k' : Type u) [Field k']
    [Algebra k k'] : IsDomain (S ⊗[k] k') := by
  obtain ⟨hirr, hred⟩ := isDomain_tensorProduct_iff_irreducibleSpace_and_isReduced.mp h
  have hirr' : ∀ (K : Type u) [Field K] [Algebra k K],
      IrreducibleSpace (PrimeSpectrum (S ⊗[k] K)) :=
    ((AlgebraicGeometry.geometricallyIrreducible_tfae k S (SeparableClosure k)
      (AlgebraicClosure k)).out 1 4).mpr hirr
  have hred' : ∀ (K : Type u) [Field K] [Algebra k K], IsReduced (K ⊗[k] S) :=
    ((Algebra.isGeometricallyReduced_tfae k (ringExpChar k) S
      (perfectClosure k (AlgebraicClosure k)) (AlgebraicClosure k)).out 4 5).mp hred
  exact isDomain_tensorProduct_iff_irreducibleSpace_and_isReduced.mpr ⟨hirr' k', hred' k'⟩

/-- For a field `k` and a `k`-algebra `S` the following are equivalent: (1) `S` is geometrically
integral over `k`; (2) `S ⊗[k] k'` is a domain for every field extension `k'/k`; (3) `S ⊗[k] k'`
is a domain for every finite extension `k'/k`; (4) `S ⊗[k] AlgebraicClosure k` is a domain. -/
public theorem solution (k S : Type u) [Field k] [CommRing S] [Algebra k S] :
    List.TFAE
      [ Algebra.IsGeometricallyIntegral k S,
        ∀ (k' : Type u) [Field k'] [Algebra k k'], IsDomain (S ⊗[k] k'),
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [Module.Finite k k'], IsDomain (S ⊗[k] k'),
        IsDomain (S ⊗[k] AlgebraicClosure k) ] := by
  tfae_have 1 ↔ 2 := Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct k S
  tfae_have 2 → 3 := fun h k' _ _ _ ↦ h k'
  tfae_have 3 → 4 := isDomain_tensorProduct_algebraicClosure_of_finite k S
  tfae_have 4 → 2 := isDomain_tensorProduct_of_algebraicClosure k S
  tfae_finish

end Stacks.GeometricallyIntegral.Criteria

@[expose] public section

open TensorProduct

/-- **Stacks 0FWF.** Let `k` be a field and let `S` be a `k`-algebra. The following are
equivalent: (1) `S` is geometrically integral over `k`; (2) `S ⊗[k] k'` is a domain for every
field extension `k'/k`; (3) `S ⊗[k] k'` is a domain for every finite extension `k'/k`;
(4) `S ⊗[k] AlgebraicClosure k` is a domain. -/
@[stacks 0FWF]
public theorem Algebra.isGeometricallyIntegral_tfae (k S : Type u) [Field k] [CommRing S]
    [Algebra k S] :
    List.TFAE
      [ Algebra.IsGeometricallyIntegral k S,
        ∀ (k' : Type u) [Field k'] [Algebra k k'], IsDomain (S ⊗[k] k'),
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [Module.Finite k k'], IsDomain (S ⊗[k] k'),
        IsDomain (S ⊗[k] AlgebraicClosure k) ] :=
  Stacks.GeometricallyIntegral.Criteria.solution k S

end
