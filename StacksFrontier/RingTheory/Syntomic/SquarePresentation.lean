module

public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.QuasiFinite.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Square presentations of quasi-finite algebras

A quasi-finite algebra has zero-dimensional fibres, so the dimension condition
`dim κ(p) ⊗_R S = n - c` of Stacks 00SP forces `c = n`: a relative global complete intersection
presentation of a quasi-finite algebra over a ring with a prime has as many relations as
variables.

## Main results

* `Algebra.Presentation.IsRelativeGlobalCompleteIntersection.card_eq`: a relative global complete
  intersection presentation of a quasi-finite algebra is square.
* `Algebra.exists_square_presentation`: a quasi-finite relative global complete intersection over
  a ring with a prime admits a square presentation.

## References

* [Stacks Project, Tag 00SP](https://stacks.math.columbia.edu/tag/00SP)
-/

@[expose] public section

/-- **The fibres of a quasi-finite algebra are zero-dimensional.** For a quasi-finite algebra
`S` over `R` and a prime `p` of `R` with nonzero fibre ring, the Krull dimension of
`κ(p) ⊗_R S` is `0`: that ring is finite-dimensional over `κ(p)`, hence artinian. -/
@[ega "0 16.1.1" "special case"]
theorem Algebra.QuasiFinite.ringKrullDim_fiber_eq_zero {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.QuasiFinite R S] (p : Ideal R) [p.IsPrime]
    [Nontrivial (p.Fiber S)] : ringKrullDim (p.Fiber S) = 0 :=
  ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
    (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp
      (inferInstanceAs (IsArtinianRing (p.Fiber S)))).2

/-- **A relative global complete intersection presentation of a quasi-finite algebra over a ring
with a prime is square.** The dimension condition of Stacks 00SP at the prime of `R` below a
prime `q` of `S` reads `0 + c = n`, because the fibre there is nonzero and, `S` being
quasi-finite over `R`, zero-dimensional. -/
theorem Algebra.Presentation.IsRelativeGlobalCompleteIntersection.card_eq
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.QuasiFinite R S] {n c : ℕ}
    {P : Algebra.Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) (q : Ideal S) [q.IsPrime] : c = n := by
  have hfib : Nontrivial ((q.under R).Fiber S) :=
    (PrimeSpectrum.primesOverOrderIsoFiber R S (q.under R) ⟨q, ⟨‹_›, inferInstance⟩⟩).nontrivial
  have hdim := hP.ringKrullDim_fiber_add_card_eq_card (q.under R) hfib
  rw [Algebra.QuasiFinite.ringKrullDim_fiber_eq_zero (q.under R), zero_add] at hdim
  simpa using hdim

/-- **A quasi-finite relative global complete intersection over a ring with a prime has a square
presentation.** Any presentation witnessing Stacks 00SP has as many relations as variables, by
`Algebra.Presentation.IsRelativeGlobalCompleteIntersection.card_eq`. -/
theorem Algebra.exists_square_presentation {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.QuasiFinite R S] [Algebra.IsRelativeGlobalCompleteIntersection R S]
    (q : Ideal S) [q.IsPrime] :
    ∃ (n : ℕ) (P : Algebra.Presentation R S (Fin n) (Fin n)),
      P.IsRelativeGlobalCompleteIntersection := by
  obtain ⟨n, c, P, hP⟩ := ‹Algebra.IsRelativeGlobalCompleteIntersection R S›.out
  have hnc : c = n := hP.card_eq q
  subst hnc
  exact ⟨c, P, hP⟩

end
