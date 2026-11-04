module

public import Mathlib.RingTheory.Ideal.Maps
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.ClosedPoint

/-!
# Rig-closedness transports along an isomorphism of rings

Whether a prime `q` of a ring cuts out a closed point of the complement of the vanishing locus
of an ideal `I` is an order-theoretic condition on the pair `(I, q)`: it says exactly that `q`
does not contain `I` and that no prime strictly above `q` avoids `I`
(`Rig.isClosedPointAway_iff_isMaximalAmongPrimesAvoiding`).  Contracting ideals along a
bijective ring homomorphism is an isomorphism of ideal lattices which preserves and reflects
primality, so it carries that condition back and forth.

This is what lets a rig-closedness statement be read across an identification of rings which is
an isomorphism rather than an equality — for instance across `A{σ}_{\{f\}} = A_{\{f\}}{σ}` in
the fourth paragraph of the proof of Stacks 0GGR, where the prime produced by Stacks 0GGG lives
on the completed principal localization of a restricted power series ring and has to be used on
the restricted power series ring over a completed principal localization.

## Main results

* `Rig.isClosedPointAwayFrom_comap_of_bijective`: rig-closedness transports along the
  contraction of ideals induced by a bijective ring homomorphism.

## Implementation notes

The statement is for a `RingHom` together with `Function.Bijective`, which is the form in which
the identifications of this development are available, rather than for a bundled `RingEquiv`.
The primality instance on the contracted ideal is Mathlib's `Ideal.comap_isPrime`, so it is
found by instance search and the statement needs no `letI`.

## References

* [Stacks Project, Tag 0GG9](https://stacks.math.columbia.edu/tag/0GG9)
* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
-/

@[expose] public section

namespace Rig

section

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **Rig-closedness transports along a bijective ring homomorphism.**  For a bijective
`φ : A → B`, an ideal `I` of `B` and a prime `q` of `B`, the contracted prime `q ∩ A` is a
closed point of the complement of the vanishing locus of `I ∩ A` exactly when `q` is one for
`I`. -/
public lemma isClosedPointAwayFrom_comap_of_bijective (φ : A →+* B)
    (hφ : Function.Bijective φ) (I q : Ideal B) [q.IsPrime] :
    Ideal.IsClosedPointAwayFrom (I.comap φ) (q.comap φ) ↔
      Ideal.IsClosedPointAwayFrom I q := by
  rw [isClosedPointAway_iff_isMaximalAmongPrimesAvoiding,
    isClosedPointAway_iff_isMaximalAmongPrimesAvoiding]
  have hle : ∀ J K : Ideal B, J.comap φ ≤ K.comap φ ↔ J ≤ K :=
    Ideal.comap_le_comap_iff_of_surjective φ hφ.2
  constructor
  · rintro ⟨havoid, hmax⟩
    refine ⟨fun hIq => havoid (Ideal.comap_mono hIq), fun P hP hqP hIP => ?_⟩
    exact Ideal.comap_injective_of_surjective φ hφ.2
      (hmax (P.comap φ) (Ideal.comap_isPrime φ P) (Ideal.comap_mono hqP)
        fun h => hIP ((hle I P).mp h))
  · rintro ⟨havoid, hmax⟩
    refine ⟨fun hIq => havoid ((hle I q).mp hIq), fun p hp hqp hIp => ?_⟩
    have hPcomap : (p.map φ).comap φ = p := Ideal.comap_map_of_bijective φ hφ
    have hPprime : (p.map φ).IsPrime :=
      Ideal.map_isPrime_of_surjective hφ.2
        (le_of_eq_of_le ((RingHom.injective_iff_ker_eq_bot φ).mp hφ.1) bot_le)
    have hqP : q ≤ p.map φ := (hle q (p.map φ)).mp (hqp.trans hPcomap.ge)
    have hIP : ¬ I ≤ p.map φ := fun h => hIp ((Ideal.comap_mono h).trans hPcomap.le)
    exact hPcomap.symm.trans (congrArg (Ideal.comap φ) (hmax (p.map φ) hPprime hqP hIP))

end

end Rig

end
