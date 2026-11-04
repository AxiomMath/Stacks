module

public import StacksFrontier.RingTheory.FormalFibres.Localization
public import StacksFrontier.RingTheory.LocalCohomology.CutoffCompletionSerre
public import StacksFrontier.RingTheory.Serre.RingEquiv

/-!
# Serre's condition on the formal fibres is invariant under an isomorphism of local rings

`Stacks.LocalCohomology.FormalFibersHavePropertySk A k` asks that every formal fibre
`A^∧ ⊗_A κ(𝔭)` of the local ring `A` be Noetherian and satisfy Serre's condition `(Sₖ)`. This
file proves that the predicate transports along an isomorphism `A ≃+* B` of local rings.

The reason the statement is wanted is that [Stacks, Tag 0BJY] imposes the condition on the
formal fibres of the local rings `𝒪_{X,z}` of a scheme, while every affine criterion in
`StacksFrontier/AlgebraicGeometry/LocalCohomology/PushforwardCoherence/` imposes it at
`Localization.AtPrime q` for a prime `q` of a ring of sections. Those two rings are isomorphic —
by `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk` and `IsLocalization.algEquiv` — and
never equal, so nothing could be carried between them.

## Main results

* `Stacks.LocalCohomology.formalFibersHavePropertySk_of_ringEquiv` — **the transport.**
* `Stacks.LocalCohomology.formalFibersHavePropertySk_iff_of_ringEquiv` — the resulting
  equivalence.

## Implementation notes

Three transports compose. An isomorphism of local rings induces one of the adic completions at
the maximal ideals, `Stacks.FormalFibres.completionRingEquiv`, compatible with the maps from the
uncompleted rings by `Stacks.FormalFibres.completionRingEquiv_algebraMap`; those two are exactly
the hypotheses of `Stacks.FormalFibres.exists_fiber_ringEquiv`, which produces an isomorphism of
the fibres over corresponding primes. `Ideal.Fiber` is the tensor product in the opposite order
from the one `FormalFibersHavePropertySk` is written with, so
`Algebra.TensorProduct.comm` intervenes on each side — the same step
`Stacks.FormalFibres.formalFibersHaveAt_iff` takes. Noetherianity moves across the composite by
`isNoetherianRing_of_ringEquiv` and Serre's condition by `propertySkRing_of_ringEquiv`.

The predicate `Stacks.FormalFibres.FormalFibersHaveAt`, which has its own transport
`Stacks.FormalFibres.formalFibersHaveAt_of_ringEquiv`, cannot be used instead: it is indexed by
a `RingMapProperty` and `PropertySkRing` uses a different notion of depth, with no comparison
between the two proved in the library — as recorded at
`StacksFrontier/RingTheory/FormalFibres/Examples.lean:103`.

## References

* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
* [Stacks Project, Tag 031P](https://stacks.math.columbia.edu/tag/031P)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Stacks.LocalCohomology

/-- **Serre's condition on the formal fibres is invariant under an isomorphism of local
rings.** If every formal fibre of `A` is Noetherian and satisfies `(Sₖ)`, and `A ≃+* B`, then
the same holds for `B`.

A prime `𝔭` of `B` pulls back to a prime of `A`; the isomorphism of adic completions
`Stacks.FormalFibres.completionRingEquiv` and its compatibility with the maps from the
uncompleted rings feed `Stacks.FormalFibres.exists_fiber_ringEquiv`, which gives an isomorphism
of the two fibres, and `Algebra.TensorProduct.comm` reconciles the order of the tensor factors
with the one this predicate is written in. -/
public lemma formalFibersHavePropertySk_of_ringEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (k : ℕ)
    (h : FormalFibersHavePropertySk A k) : FormalFibersHavePropertySk B k := by
  intro p hp
  obtain ⟨E, -⟩ := Stacks.FormalFibres.exists_fiber_ringEquiv e
    (Stacks.FormalFibres.completionRingEquiv e)
    (Stacks.FormalFibres.completionRingEquiv_algebraMap e) p
  obtain ⟨hNA, hSkA⟩ := h (p.comap e.toRingHom)
  let := hNA
  let φ : TensorProduct A (AdicCompletion (maximalIdeal A) A)
        (p.comap e.toRingHom).ResidueField ≃+*
      TensorProduct B (AdicCompletion (maximalIdeal B) B) p.ResidueField :=
    ((Algebra.TensorProduct.comm A (AdicCompletion (maximalIdeal A) A)
          (p.comap e.toRingHom).ResidueField).toRingEquiv.trans E).trans
      (Algebra.TensorProduct.comm B (AdicCompletion (maximalIdeal B) B)
        p.ResidueField).toRingEquiv.symm
  refine ⟨isNoetherianRing_of_ringEquiv _ φ, ?_⟩
  let := isNoetherianRing_of_ringEquiv _ φ
  exact propertySkRing_of_ringEquiv φ k hSkA

/-- **Serre's condition on the formal fibres is the same for two isomorphic local rings.** -/
public lemma formalFibersHavePropertySk_iff_of_ringEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (k : ℕ) :
    FormalFibersHavePropertySk A k ↔ FormalFibersHavePropertySk B k :=
  ⟨formalFibersHavePropertySk_of_ringEquiv e k,
    formalFibersHavePropertySk_of_ringEquiv e.symm k⟩

end Stacks.LocalCohomology

end
