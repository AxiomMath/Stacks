module

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.QuasiFinite
public import StacksFrontier.RingTheory.CompleteIntersection.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# A square presentation of a quasi-finite algebra is a relative global complete intersection

Let `A → B` be quasi-finite and let `P` present `B` over `A` with as many relations as variables,
`B = A[x_1, …, x_n]/(f_1, …, f_n)`. Then `P` is a relative global complete intersection
presentation (Definition 00SP): every nonempty fibre `κ(p) ⊗_A B` is a finite-dimensional algebra
over the field `κ(p)`, hence artinian, hence of Krull dimension `0 = n - n`.

## Main results

* `Algebra.Presentation.instIsRelativeGlobalCompleteIntersectionOfQuasiFinite`: a presentation of
  a quasi-finite algebra indexed by `Fin n` and `Fin n` is a relative global complete intersection
  presentation.
* `Algebra.isRelativeGlobalCompleteIntersection_of_quasiFinite`: a quasi-finite algebra with such a
  presentation is a relative global complete intersection.

## References

* [Stacks Project, Tag 0FL9](https://stacks.math.columbia.edu/tag/0FL9), Remark 50.18.3
* [Stacks Project, Tag 00SP](https://stacks.math.columbia.edu/tag/00SP), Definition 10.136.5
* [Stacks Project, Tag 00PL](https://stacks.math.columbia.edu/tag/00PL), Definition 10.122.3
-/

@[expose] public section

namespace Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.QuasiFinite A B]

add_to_stacks 0FL9 "the relative global complete intersection: the source's `A → B` \
  quasi-finite is `Algebra.QuasiFinite A B`, which for an algebra with a finite presentation is \
  its Definition 00PL, and `B = A[x_1, …, x_n]/(f_1, …, f_n)` is a presentation with \
  `Nat.card σ = Nat.card ι`"
  Algebra.Presentation.isRelativeGlobalCompleteIntersection_of_quasiFinite

/-- A presentation `B = A[x_1, …, x_n]/(f_1, …, f_n)` of a quasi-finite `A`-algebra by as many
relations as variables is a relative global complete intersection presentation (Definition 00SP):
every nonempty fibre `κ(p) ⊗_A B` is finite-dimensional over the field `κ(p)`, hence of Krull
dimension `0 = n - n`. -/
instance Presentation.instIsRelativeGlobalCompleteIntersectionOfQuasiFinite {n : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin n)) :
    P.IsRelativeGlobalCompleteIntersection :=
  P.isRelativeGlobalCompleteIntersection_of_quasiFinite rfl

/-- A quasi-finite `A`-algebra `B` admitting a presentation
`B = A[x_1, …, x_n]/(f_1, …, f_n)` by as many relations as variables is a relative global
complete intersection over `A` (Definition 00SP). -/
@[stacks 0FL9 "the source's `B` is a relative global complete intersection over `A`, at the level
of the algebra; the presentation-level form, which is what the rest of the remark uses, is
`Algebra.Presentation.isRelativeGlobalCompleteIntersection_of_quasiFinite`"]
theorem isRelativeGlobalCompleteIntersection_of_quasiFinite {n : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin n)) :
    Algebra.IsRelativeGlobalCompleteIntersection A B :=
  ⟨n, n, P, inferInstance⟩

end Algebra

end
