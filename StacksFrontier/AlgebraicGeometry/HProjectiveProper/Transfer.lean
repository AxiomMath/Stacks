module

public import StacksFrontier.AlgebraicGeometry.HProjectiveProper.Basic

/-!
# H-projectivity transfers along a closed immersion over the base

A morphism `f : X ⟶ S` is *H-projective* when it factors as a closed immersion into relative
projective space `ℙⁿ_S` followed by the structure morphism, for some `n`. This file records that
the notion passes from a target to a source along a closed immersion over `S`, and in particular
along an isomorphism over `S`: compose the given closed immersion into `ℙⁿ_S` with the new one.

The isomorphism case is the step of [Stacks, Tag 0A27] which disposes of a curve whose
compactification has empty complement — there `X = X̄` and H-projectivity of `X̄` is transported
back to `X` — and the closed-immersion case is the step by which a closed subscheme of an
H-projective scheme is H-projective, used throughout the compactification argument of
[Stacks, Tag 0BXW].

## Main results

* `AlgebraicGeometry.exists_isClosedImmersion_projectiveSpaceOver_of_isClosedImmersion`:
  H-projectivity over `S` passes to the source of a closed immersion over `S`.
* `AlgebraicGeometry.exists_isClosedImmersion_projectiveSpaceOver_of_iso`: H-projectivity over `S`
  is invariant under isomorphism over `S`.

## Implementation notes

**H-projectivity is taken as the explicit existential, not as a named predicate**, exactly as in
`StacksFrontier.AlgebraicGeometry.HProjectiveProper.Basic`. The predicate itself belongs to the
Morphisms of Schemes chapter ([Stacks, Tag 01W8]) and does not exist in this repository under any
name; when it is introduced these results apply to it after unfolding, with no restatement.

No attribute is attached: neither statement is a Stacks tag. They are the transfer steps that
[Stacks, Tags 0A27 and 0BXW] use without naming.

## References

* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 0BXW](https://stacks.math.columbia.edu/tag/0BXW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- **H-projectivity passes to the source of a closed immersion over the base.** If `Y` admits a
closed immersion into `ℙⁿ_S` over `S` and `j : X ⟶ Y` is a closed immersion over `S`, then `X`
admits one too, namely `j` composed with it. -/
public theorem exists_isClosedImmersion_projectiveSpaceOver_of_isClosedImmersion
    {X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (j : X ⟶ Y) [IsClosedImmersion j]
    (hj : j ≫ g = f)
    (h : ∃ (n : ℕ) (i : Y ⟶ projectiveSpaceOver n S),
          IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver n S ↘ S) = g) :
    ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
      IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver n S ↘ S) = f := by
  obtain ⟨n, i, hi, hcomp⟩ := h
  refine ⟨n, j ≫ i, inferInstance, ?_⟩
  rw [Category.assoc, hcomp, hj]

/-- **H-projectivity over the base is invariant under isomorphism over the base.** An isomorphism
is a closed immersion, so this is a special case of
`exists_isClosedImmersion_projectiveSpaceOver_of_isClosedImmersion`. -/
public theorem exists_isClosedImmersion_projectiveSpaceOver_of_iso
    {X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y) (he : e.hom ≫ g = f)
    (h : ∃ (n : ℕ) (i : Y ⟶ projectiveSpaceOver n S),
          IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver n S ↘ S) = g) :
    ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
      IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver n S ↘ S) = f :=
  exists_isClosedImmersion_projectiveSpaceOver_of_isClosedImmersion e.hom he h

end AlgebraicGeometry

end
