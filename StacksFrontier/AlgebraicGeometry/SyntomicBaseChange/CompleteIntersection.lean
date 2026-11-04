module

public import StacksFrontier.RingTheory.CompleteIntersection.Criteria

/-!
# The two spellings of Definition 00SD agree in a single universe

The draft carries two renderings of Stacks Definition 00SD, a complete intersection over a field:
`IsCompleteIntersectionLocalRing`, whose auxiliary regular local ring is quantified in
`Type (max u v)` and which asks separately that the equations lie in the maximal ideal, and
`IsCompleteIntersection`, whose auxiliary ring is quantified in the universe of the base field
and which leaves that condition to `RingTheory.Sequence.IsRegular`.  When the base field and the
algebra live in the same universe the two quantify over the same types, and the extra condition is
a consequence: a regular sequence spans a proper ideal, and a proper ideal of a local ring is
contained in the maximal ideal.

## Main results

* `isCompleteIntersectionLocalRing_iff_isCompleteIntersection`: the two predicates agree.

## References

* [Stacks 00SD](https://stacks.math.columbia.edu/tag/00SD), Definition 10.135.5.
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence

universe u

namespace Stacks.SyntomicBaseChange

/-- A regular sequence in a ring spans a proper ideal: the quotient by it is nonzero. -/
theorem ofList_ne_top_of_isRegular {R : Type*} [CommRing R] {fs : List R}
    (h : IsRegular R fs) : Ideal.ofList fs ≠ ⊤ := fun hc ↦
  h.top_ne_smul (by simp [hc])

/-- **The two renderings of Definition 00SD agree.** For a field `k` and a `k`-algebra `S` in the
same universe, `S` is a complete intersection over `k` in the sense of
`IsCompleteIntersectionLocalRing` if and only if it is one in the sense of
`IsCompleteIntersection`.

Only the condition that the equations lie in the maximal ideal of the auxiliary ring has to be
supplied, and it follows from regularity of the sequence: `Ideal.ofList fs` is proper, hence
contained in the maximal ideal. -/
theorem isCompleteIntersectionLocalRing_iff_isCompleteIntersection (k : Type u) [Field k]
    (S : Type u) [CommRing S] [Algebra k S] :
    IsCompleteIntersectionLocalRing k S ↔ IsCompleteIntersection k S := by
  constructor
  · rintro ⟨R, hR, hRa, hRr, hRe, fs, -, hreg, ⟨e⟩⟩
    exact ⟨R, hR, hRa, hRr, hRe, fs, hreg, ⟨e⟩⟩
  · rintro ⟨R, hR, hRa, hRr, hRe, fs, hreg, ⟨e⟩⟩
    refine ⟨R, hR, hRa, hRr, hRe, fs, fun x hx ↦ ?_, hreg, ⟨e⟩⟩
    exact le_maximalIdeal (ofList_ne_top_of_isRegular hreg) (Ideal.subset_span hx)

end Stacks.SyntomicBaseChange
