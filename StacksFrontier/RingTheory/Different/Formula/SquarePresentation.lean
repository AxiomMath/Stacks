module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.Relative

/-!
# Square presentations of quasi-finite algebras

A presentation `B = A[x_i, i ∈ ι]/(f_j, j ∈ σ)` with as many relations as variables is called
*square*. For a quasi-finite algebra every square presentation is a relative global complete
intersection presentation (Definition 00SP): the fibre `κ(p) ⊗_A B` over a prime `p` of `A` is a
quasi-finite algebra over the field `κ(p)`, hence artinian, hence of Krull dimension
`0 = #ι - #σ`.

This is the input to the standard presentation of a localized complete intersection: the algebra
`A[x_1, …, x_n, 1/h]/(f_1, …, f_n)` is presented by the `n + 1` variables `x, x_1, …, x_n` and
the `n + 1` relations `x h - 1, f_1, …, f_n`, which is square.

## Main results

* `Algebra.Presentation.isRelativeGlobalCompleteIntersection_of_card_eq`: a square presentation
  of a quasi-finite algebra is a relative global complete intersection presentation.
* `Algebra.IsRelativeGlobalCompleteIntersection.of_card_eq`: a quasi-finite algebra with a square
  presentation is a relative global complete intersection.

## Implementation notes

Quasi-finiteness is the weakest hypothesis under which the argument runs; in particular it is
weaker than `Module.Finite A B`. No positivity assumption on the number of variables is needed,
so the empty presentation is covered.

## References

* [Stacks Project, Tag 00SP](https://stacks.math.columbia.edu/tag/00SP)
* [Stacks Project, Tag 0BWD](https://stacks.math.columbia.edu/tag/0BWD)
-/

@[expose] public section

universe u v

namespace Algebra.Presentation

/-- A presentation `B = A[x_i, i ∈ ι]/(f_j, j ∈ σ)` of a quasi-finite algebra with as many
relations as variables is a relative global complete intersection presentation (Definition
00SP). Every nonempty fibre `κ(p) ⊗_A B` is quasi-finite over the field `κ(p)`, hence artinian,
so its Krull dimension is `0 = #ι - #σ`. -/
theorem isRelativeGlobalCompleteIntersection_of_card_eq {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.QuasiFinite A B] {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.Presentation A B ι σ) (hcard : Nat.card σ = Nat.card ι) :
    P.IsRelativeGlobalCompleteIntersection :=
  ⟨fun p _ _ => by
    have : IsArtinianRing (p.Fiber B) := inferInstance
    rw [ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance]
    simp [hcard]⟩

end Algebra.Presentation

/-- A quasi-finite algebra presented by as many relations as variables is a relative global
complete intersection (Definition 00SP). -/
theorem Algebra.IsRelativeGlobalCompleteIntersection.of_card_eq {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.QuasiFinite A B] {ι σ : Type*} [Finite ι]
    [Finite σ] (P : Algebra.Presentation A B ι σ) (hcard : Nat.card σ = Nat.card ι) :
    Algebra.IsRelativeGlobalCompleteIntersection A B :=
  Algebra.IsRelativeGlobalCompleteIntersection.of_presentation P
    (hP := P.isRelativeGlobalCompleteIntersection_of_card_eq hcard)

end
