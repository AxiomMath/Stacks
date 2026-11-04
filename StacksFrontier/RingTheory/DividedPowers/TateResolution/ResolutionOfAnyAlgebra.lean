module

public import StacksFrontier.RingTheory.NaiveCotangent.Complex
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TateColimitResolution

/-! # Every algebra has a Tate resolution

Every `R`-algebra `S` admits a polynomial presentation `φ : R[xᵢ] → S` together with a Tate
resolution of `S` along `φ`. This is the existence form of Tag 09PN, with the presentation
quantified over; `DividedPowers.TateResolution.tateResolution` resolves a prescribed
surjection.

No hypothesis on `R` or `S` is needed: the construction of
`DividedPowers.TateResolution.tateResolution` adjoins *all* cycles of each degree as variables
and so needs neither a Noetherian base nor a finite-type algebra. Those hypotheses enter only
for the finiteness half of the tag, which asks the resolution to be degreewise finite.

## Main results

* `DividedPowers.TateResolution.exists_tateResolution` — every `R`-algebra `S` admits a
  polynomial presentation carrying a Tate resolution, with the variables of the presentation
  indexed in the universe of `S`.

## Implementation notes

The presentation used is the tautological one, indexing the variables by the elements of `S`
themselves: `R[X_s : s ∈ S] → S`, `X_s ↦ s`. A Tate resolution of `S` along a presentation
indexed by `σ` has its carrier in the join of the universes of `R`, of `S` and of `σ`, so an
index type in the universe of `S` keeps the whole resolution in the universe of `R` and `S`. A
finite presentation of a finite-type algebra indexes its variables by `Fin n` in `Type 0`, and
would have to be transported up before it could be used.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u

/-- **Existence of a Tate resolution.** Every `R`-algebra `S` admits a surjection onto it from
a polynomial ring over `R` whose variables are indexed in the universe of `S`, together with a
Tate resolution of `S` along that surjection.

The surjection is the tautological one `R[X_s : s ∈ S] → S`, `X_s ↦ s`, which is what keeps the
index type in the universe of `S`; `DividedPowers.TateResolution.tateResolution` then resolves
it. -/
public theorem exists_tateResolution (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    ∃ (σ : Type u) (φ : MvPolynomial σ R →ₐ[R] S),
      Function.Surjective φ ∧ Nonempty (Resolution R S σ φ) :=
  have hsurj : Function.Surjective (MvPolynomial.aeval (R := R) (id : S → S)) :=
    Stacks.CommAlg.NaiveCotangentComplex.canonical_presentation_surjective
  ⟨S, _, hsurj, ⟨tateResolution _ hsurj⟩⟩

end DividedPowers.TateResolution

end
