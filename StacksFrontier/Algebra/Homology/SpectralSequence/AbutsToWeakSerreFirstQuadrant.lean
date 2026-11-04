module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToWeakSerre

/-!
# The first quadrant form of Stacks 0132 part (4)

`CategoryTheory.SpectralSequence.AbutsTo.prop_of_prop_page` concludes that a weak Serre
subcategory `P` of an abelian category contains every term of the abutment of a spectral
sequence, from the hypothesis that it contains the term of one page at *every* bidegree of
`ℤ × ℤ`.  A first quadrant spectral sequence is not presented that way.  What is known about one
is two separate things: its page vanishes outside the first quadrant, and its terms inside the
first quadrant are identified with objects indexed by `ℕ × ℕ`.  Neither alone is the hypothesis
asked for, and assembling them is a step each first quadrant consumer would have to repeat.

`CategoryTheory.SpectralSequence.AbutsTo.prop_of_prop_page_firstQuadrant` takes the hypothesis in
those two pieces instead.  The vanishing clause is stated with the disjunction `p < 0 ∨ q < 0`
over `ℤ × ℤ`, and the membership clause over `ℕ × ℕ`, which is how the Čech spectral sequences of
this development record them: the first quadrant clause of a spectral sequence of abelian sheaves
quantifies over `ℤ` because the spectral sequence does, while the identification of the first
page with the higher direct images along the terms of a Čech nerve is indexed by `ℕ`, there being
no term of the nerve in negative degree.

A weak Serre subcategory contains the zero object and is closed under isomorphisms, so the
vanishing clause supplies `P` outside the first quadrant and the two pieces together give the
hypothesis of `CategoryTheory.SpectralSequence.AbutsTo.prop_of_prop_page` on all of `ℤ × ℤ`.
Beyond that repackaging there is no mathematical content here; in particular the first quadrant
is not what makes the result true. Abutment already asserts both an infinity page at every
bidegree and a finite filtration of each `H n`, which is everything the argument in
`StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToWeakSerre` consumes.

## Main results

* `CategoryTheory.SpectralSequence.AbutsTo.prop_of_prop_page_firstQuadrant`: a weak Serre
  subcategory containing the terms of one page of a first quadrant spectral sequence at the
  nonnegative bidegrees contains every term of its abutment.

## References

* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Stacks 0132 part (4) for a first quadrant spectral sequence.**  Let `E` be a cohomological
spectral sequence of an abelian category which abuts to a graded object `H`, let `P` be a weak
Serre subcategory, and let `r` be a page of `E`.  If the terms of `E_r` vanish outside the first
quadrant and those at the nonnegative bidegrees lie in `P`, then every `H n` lies in `P`.

This is `CategoryTheory.SpectralSequence.AbutsTo.prop_of_prop_page` with its hypothesis on the
page split into the two clauses a first quadrant spectral sequence provides: `P` contains the
zero object and is closed under isomorphisms, so the vanishing clause gives `P` at the bidegrees
the other clause does not reach. -/
@[stacks 0132 "part (4), for a first-quadrant `CohomologicalSpectralSequence` presented by
  `SpectralSequence.AbutsTo`, with the page hypothesis split into vanishing outside the first
  quadrant and membership at the nonnegative bidegrees"]
theorem AbutsTo.prop_of_prop_page_firstQuadrant {r₀ : ℤ}
    {E : CohomologicalSpectralSequence C r₀} {H : ℤ → C} (hE : AbutsTo E H)
    (P : ObjectProperty C) [P.IsWeakSerreClass] {r : ℤ} (hr : r₀ ≤ r)
    (hzero : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r hr).X (p, q)))
    (hP : ∀ p q : ℕ, P ((E.page r hr).X ((p : ℤ), (q : ℤ)))) (n : ℤ) : P (H n) := by
  refine hE.prop_of_prop_page P hr (fun pq => ?_) n
  obtain ⟨p, q⟩ := pq
  by_cases hp : 0 ≤ p
  · by_cases hq : 0 ≤ q
    · rw [← Int.toNat_of_nonneg hp, ← Int.toNat_of_nonneg hq]
      exact hP p.toNat q.toNat
    · exact P.prop_of_isZero (hzero p q (Or.inr (by omega)))
  · exact P.prop_of_isZero (hzero p q (Or.inl (by omega)))

end CategoryTheory.SpectralSequence

end
