module

public import Mathlib.RingTheory.Unramified.Locus
public import StacksFrontier.RingTheory.Unramified.LocalHom

/-!
# Unramified at a prime and unramified homomorphisms of local rings

Let `A → B` be of finite type and let `q` be a prime of `B` lying over the prime `p` of `A`.
This file proves Lemma 039G: `A → B` is unramified at `q` if and only if `A_p → B_q` is an
unramified homomorphism of local rings in the sense of Definition 024M
(`RingHom.IsUnramifiedLocalHom`).

## Main results

* `Algebra.exists_unramified_away_iff_isUnramifiedLocalHom_algebraMap`: Lemma 039G.

## Implementation notes

*No Noetherian hypothesis.* The source makes Definition 024M for Noetherian local rings only, and
Lemma 039G assumes `A` Noetherian so that `A_p` and `B_q` are Noetherian local rings to which the
definition applies. Neither the three conditions of the definition nor the proof of the lemma use
the Noetherian property, and `RingHom.IsUnramifiedLocalHom` is defined for all local rings (on
Noetherian local rings it is the source's definition verbatim). Lemma 039G is therefore proved
with no Noetherian hypothesis on `A`: this is a generalization of the source's statement, not a
weakening.

*Unramified at a prime.* The source says that `A → B` is unramified at `q` if there is a `g ∉ q`
with `A → B_g` unramified (Definition 00UT (3)), and that is how the left-hand side of Lemma 039G
is written: `∃ g ∉ q, Algebra.Unramified A (Localization.Away g)`. The proof passes through
Mathlib's `Algebra.IsUnramifiedAt A q`, the formal unramifiedness of `B_q`, which for an algebra
of finite type is the same condition (`Algebra.exists_unramified_of_isUnramifiedAt` and
`Algebra.basicOpen_subset_unramifiedLocus_iff`).

*The map `A_p → B_q` is pinned.* The algebra structure of `Localization.AtPrime q` over
`Localization.AtPrime p` is a hypothesis together with
`Localization.AtPrime.IsLiesOverAlgebra p q`, which says that its algebra map is the localization
`Localization.localRingHom p q (algebraMap A B)` of the given map, as in Mathlib's
`Algebra.isUnramifiedAt_iff_map_eq`. These two hypotheses also provide, through a Mathlib
instance, that this algebra map is a local homomorphism, which Definition 024M requires; it is
not an extra hypothesis.

*From 024M to formal unramifiedness.* By `RingHom.isUnramifiedLocalHom_algebraMap_iff`, the
structure map `A_p → B_q` is an unramified homomorphism of local rings exactly when `B_q` is
formally unramified and essentially of finite type over `A_p`; the second condition holds since
`B` is of finite type over `A`, and the first is equivalent to the formal unramifiedness of `B_q`
over `A`, because `A_p` is a localization of `A`.

## References

* [Stacks 039G](https://stacks.math.columbia.edu/tag/039G), Lemma 41.3.2, in Section 41.3
  "Unramified morphisms" (Section 024L). The proof is the discussion preceding it, which combines
  Lemmas 00UW and 02FM with Definition 024M.
-/

@[expose] public section

namespace Algebra

/-- **Stacks 039G.** Let `A → B` be of finite type and let `q` be a prime of `B` lying over the
prime `p` of `A`. Then `A → B` is unramified at `q` (there is `g ∉ q` with `A → B_g` unramified)
if and only if `A_p → B_q` is an unramified homomorphism of local rings. The source assumes `A`
Noetherian, which is not needed. -/
@[stacks 039G "Without the Noetherian hypothesis on `A`, which is used in the source only to
make Definition 024M applicable to `A_p → B_q`; `RingHom.IsUnramifiedLocalHom` is defined for
all local rings. See the module docstring."]
theorem exists_unramified_away_iff_isUnramifiedLocalHom_algebraMap {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (p : Ideal A) [p.IsPrime] (q : Ideal B)
    [q.IsPrime] [q.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    (∃ g ∉ q, Algebra.Unramified A (Localization.Away g)) ↔
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)).IsUnramifiedLocalHom := by
  have : EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) := .of_comp A _ _
  have key : (∃ g ∉ q, Algebra.Unramified A (Localization.Away g)) ↔ IsUnramifiedAt A q := by
    refine ⟨fun ⟨g, hg, h⟩ ↦ ?_, fun _ ↦ exists_unramified_of_isUnramifiedAt q⟩
    exact basicOpen_subset_unramifiedLocus_iff.mpr h.formallyUnramified
      ((PrimeSpectrum.mem_basicOpen (x := ⟨q, ‹_›⟩) g).mpr hg)
  rw [key, RingHom.isUnramifiedLocalHom_algebraMap_iff, and_iff_left this]
  exact ⟨fun _ ↦ .of_restrictScalars A _ _,
    fun _ ↦ FormallyUnramified.comp _ (Localization.AtPrime p) _⟩

end Algebra
