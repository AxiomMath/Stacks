module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ProfiniteClosedSubset

/-!
# Two nested quotients cut out the same closed subset of the spectrum

Let `A` be a commutative ring and let `I p : Ideal A`. Inside `Spec (A ⧸ p)` the image of `I` cuts
out the closed subset `V(I (A ⧸ p))`, and inside `Spec (A ⧸ I)` the image of `p` cuts out
`V(p (A ⧸ I))`. Both are the primes of `A` containing `I ⊔ p`, viewed through a quotient: the first
is `Spec ((A ⧸ p) ⧸ I (A ⧸ p))` and the second is `Spec ((A ⧸ I) ⧸ p (A ⧸ I))`, and these two
double quotients are the *same* quotient `A ⧸ (I ⊔ p)` of `A`, since the two ways of killing `I`
and `p` one after the other kill exactly the same elements.

So the two closed subsets are homeomorphic, by the composite

`V(I (A ⧸ p)) ≃ₜ Spec ((A ⧸ p) ⧸ I (A ⧸ p)) ≃ₜ Spec ((A ⧸ I) ⧸ p (A ⧸ I)) ≃ₜ V(p (A ⧸ I))`,

whose outer two steps are `AlgebraicGeometry.ProEtale.zeroLocusHomeomorph` and whose middle step
is contraction along `DoubleQuot.quotQuotEquivComm`.

The point of the construction is the second result: the homeomorphism does not move a prime of `A`
around. A point of `V(I (A ⧸ p))` and its image in `V(p (A ⧸ I))` contract to one and the same
prime of `A`, namely the common prime of `A` containing `I ⊔ p` that both of them name. This is
what makes the homeomorphism usable as an identification of two descriptions of the set of primes
of `A` above `I ⊔ p`, rather than merely an abstract homeomorphism of spaces. It holds because
both quotient maps `A → (A ⧸ p) ⧸ I (A ⧸ p)` and `A → (A ⧸ I) ⧸ p (A ⧸ I)` are the two
`DoubleQuot.quotQuotMk`s, and `quotQuotEquivComm` is by construction the isomorphism
carrying one to the other.

## Main results

* `PrimeSpectrum.nestedQuotientZeroLocusHomeo`: the homeomorphism
  `V(I (A ⧸ p)) ≃ₜ V(p (A ⧸ I))`.
* `PrimeSpectrum.nestedQuotientZeroLocusHomeo_comap`: it commutes with contraction to `Spec A`.
-/

@[expose] public section

namespace PrimeSpectrum

variable {A : Type*} [CommRing A]

/-- **The zero locus of `I` in `Spec (A ⧸ p)` is homeomorphic to the zero locus of `p` in
`Spec (A ⧸ I)`.** Both are the spectrum of a double quotient of `A` by `I` and `p` taken in the two
orders, and those two rings are identified by `DoubleQuot.quotQuotEquivComm`. -/
noncomputable def nestedQuotientZeroLocusHomeo (I p : Ideal A) :
    ↥(zeroLocus ((I.map (Ideal.Quotient.mk p) : Ideal (A ⧸ p)) : Set (A ⧸ p))) ≃ₜ
      ↥(zeroLocus ((p.map (Ideal.Quotient.mk I) : Ideal (A ⧸ I)) : Set (A ⧸ I))) :=
  (AlgebraicGeometry.ProEtale.zeroLocusHomeomorph (I.map (Ideal.Quotient.mk p))).symm.trans
    ((homeomorphOfRingEquiv (DoubleQuot.quotQuotEquivComm I p)).symm.trans
      (AlgebraicGeometry.ProEtale.zeroLocusHomeomorph (p.map (Ideal.Quotient.mk I))))

/-- **`nestedQuotientZeroLocusHomeo` does not move the underlying prime of `A`.** A point `q` of
`V(I (A ⧸ p))` and its image in `V(p (A ⧸ I))` have the same contraction to `A`: both sides are the
contraction of `q`, read as a prime of the double quotient, along `DoubleQuot.quotQuotMk`,
and `DoubleQuot.quotQuotEquivComm` was built to carry one `quotQuotMk` to the other. -/
theorem nestedQuotientZeroLocusHomeo_comap (I p : Ideal A)
    (q : ↥(zeroLocus ((I.map (Ideal.Quotient.mk p) : Ideal (A ⧸ p)) : Set (A ⧸ p)))) :
    ((nestedQuotientZeroLocusHomeo I p q).1.asIdeal).comap (Ideal.Quotient.mk I) =
      q.1.asIdeal.comap (Ideal.Quotient.mk p) := by
  obtain ⟨r, rfl⟩ :=
    (AlgebraicGeometry.ProEtale.zeroLocusHomeomorph (I.map (Ideal.Quotient.mk p))).surjective q
  simp only [nestedQuotientZeroLocusHomeo, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  change (((r.asIdeal.comap (DoubleQuot.quotQuotEquivComm I p : _ →+* _)).comap
        (Ideal.Quotient.mk (p.map (Ideal.Quotient.mk I)))).comap (Ideal.Quotient.mk I)) =
      (r.asIdeal.comap (Ideal.Quotient.mk (I.map (Ideal.Quotient.mk p)))).comap
        (Ideal.Quotient.mk p)
  rw [Ideal.comap_comap, Ideal.comap_comap, Ideal.comap_comap,
    show (Ideal.Quotient.mk (p.map (Ideal.Quotient.mk I))).comp (Ideal.Quotient.mk I) =
      DoubleQuot.quotQuotMk I p from rfl,
    show (Ideal.Quotient.mk (I.map (Ideal.Quotient.mk p))).comp (Ideal.Quotient.mk p) =
      DoubleQuot.quotQuotMk p I from rfl,
    DoubleQuot.quotQuotEquivComm_comp_quotQuotMk]

end PrimeSpectrum

end
