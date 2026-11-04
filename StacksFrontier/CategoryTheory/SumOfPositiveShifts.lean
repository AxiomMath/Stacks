module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
public import StacksFrontier.Homology.DerivedCategory.ShiftSummandApproximation

/-!
# A finite biproduct of positive shifts of one object

The first sentence of [Stacks, Tag 09IN] is the observation that the proof of
[Stacks, Tag 09IM] produces its lift `R` with

`R|_U = P ⊕ P^{⊕n_1}[1] ⊕ ⋯ ⊕ P^{⊕n_m}[m]`

"for some `m ≥ 0` and `n_j ≥ 0`" — the complement of `P` in `R|_U` is a finite biproduct of
*positive* shifts of `P` — and that in consequence the highest degree cohomology sheaf of `R|_U`
is that of `P`.

This file is that shape, as a predicate, with the two facts about it the remark uses: it is
stable under non-negative shifts, and it forces the cohomology to vanish at and above any degree
above which `P`'s does.

## Main definitions and results

* `Stacks.SumOfPositiveShifts.IsSumOfPositiveShifts`: the predicate.
* `Stacks.SumOfPositiveShifts.IsSumOfPositiveShifts.shift_nonneg`: stability under a non-negative
  shift. The iteration of [Stacks, Tag 09IN] uses the case `n = 1`, the complement of one stage
  being the shift of the complement the previous stage produced.
* `Stacks.SumOfPositiveShifts.IsSumOfPositiveShifts.trans`: a finite biproduct of positive shifts
  of a finite biproduct of positive shifts of `P` is one of `P`. This is what makes the shape an
  invariant of the *iteration* of [Stacks, Tag 09IN], where the construction is applied afresh
  with the previous complement in the role of `P`.
* `Stacks.SumOfPositiveShifts.IsSumOfPositiveShifts.closure`: a property holding at `P` and at
  every zero object and stable under shifts, binary biproducts and isomorphism holds at every
  finite biproduct of positive shifts of `P`.
* `Stacks.SumOfPositiveShifts.isZero_homology_of_isSumOfPositiveShifts`: **the "in particular" of
  the remark's first sentence.** A finite biproduct of positive shifts of `P` has no cohomology at
  or above a degree above which `P` has none.

## Implementation notes

**Why the predicate is an inductive family and not an indexed biproduct.** The displayed equation
of the remark is an isomorphism, and the only invariant content of the right-hand side is "built
from the `P⟦j⟧` with `j ≥ 1` by finitely many binary biproducts". Stating that as four closure
rules — a single positive shift, a zero object for the empty biproduct, binary biproducts, and
transport along an isomorphism — captures both the `m` summands and the multiplicities `n_j` with
no bookkeeping of indices.

The distribution of the shift over binary biproducts is
`CategoryTheory.Functor.biprodIsoOfAdditive`, from
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietoris.lean`. Mathlib's
`CategoryTheory.Functor.mapBiprod` would need `CategoryTheory.Limits.PreservesBinaryBiproduct` for
the shift functor, which instance search does not find.

## References

* [Stacks Project, Tag 09IN](https://stacks.math.columbia.edu/tag/09IN)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category

namespace Stacks.SumOfPositiveShifts

section Predicate

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [HasBinaryBiproducts D]

/-- **`Q` is a finite biproduct of positive shifts of `P`.** This is the shape
`P^{⊕n_1}⟦1⟧ ⊞ ⋯ ⊞ P^{⊕n_m}⟦m⟧` that the first sentence of [Stacks, Tag 09IN] asserts for the
complement of `P` in `R|_U`, "for some `m ≥ 0` and `n_j ≥ 0`": a single `P⟦j⟧` with `j ≥ 1` is
one, a zero object is one — the empty biproduct, which is the case `m = 0` — binary biproducts of
such are such, which covers both the `m` summands and the multiplicities `n_j`, and the whole
thing is taken up to isomorphism, which is the only sense in which the displayed equation of the
remark can hold. -/
inductive IsSumOfPositiveShifts (P : D) : D → Prop
  | shift (j : ℤ) (hj : 1 ≤ j) : IsSumOfPositiveShifts P (P⟦j⟧)
  | zero {Q : D} (hQ : IsZero Q) : IsSumOfPositiveShifts P Q
  | biprod {Q₁ Q₂ : D} (h₁ : IsSumOfPositiveShifts P Q₁) (h₂ : IsSumOfPositiveShifts P Q₂) :
      IsSumOfPositiveShifts P (Q₁ ⊞ Q₂)
  | of_iso {Q Q' : D} (e : Q ≅ Q') (h : IsSumOfPositiveShifts P Q) :
      IsSumOfPositiveShifts P Q'

omit [HasZeroObject D] in
/-- **A non-negative shift of a finite biproduct of positive shifts of `P` is again one.** The
shift of a single `P⟦j⟧` is `P⟦j + n⟧`, still a positive shift; the shift distributes over binary
biproducts because it is additive, by `CategoryTheory.Functor.biprodIsoOfAdditive`; and it carries
a zero object to a zero object, the identity of the image being the image of the identity.

The iteration of [Stacks, Tag 09IN] needs the case `n = 1`: the complement of the next stage is
the shift of the complement the construction has just produced. -/
theorem IsSumOfPositiveShifts.shift_nonneg {P Q : D} (h : IsSumOfPositiveShifts P Q) (n : ℤ)
    (hn : 0 ≤ n) : IsSumOfPositiveShifts P (Q⟦n⟧) := by
  induction h with
  | shift j hj => exact .of_iso ((shiftFunctorAdd D j n).app P) (.shift (j + n) (by lia))
  | zero hQ =>
    exact .zero ((shiftFunctor D n).map_isZero hQ)
  | biprod _ _ ih₁ ih₂ =>
    exact .of_iso (Functor.biprodIsoOfAdditive (shiftFunctor D n) _ _).symm (.biprod ih₁ ih₂)
  | of_iso e _ ih => exact .of_iso ((shiftFunctor D n).mapIso e) ih

omit [HasZeroObject D] in
/-- **A finite biproduct of positive shifts of a finite biproduct of positive shifts of `P` is
one of `P`.** Every closure rule but the first is inherited verbatim, and a positive shift of a
biproduct of positive shifts of `P` is again one by
`Stacks.SumOfPositiveShifts.IsSumOfPositiveShifts.shift_nonneg`.

This is what makes the shape an invariant of the *iteration* of [Stacks, Tag 09IN], as opposed to
of the single induction of [Stacks, Tag 09IM]: at each stage the construction is applied afresh
with the previous complement in the role of `P`, and the complement it returns is a biproduct of
positive shifts of *that*. -/
theorem IsSumOfPositiveShifts.trans {P Q R : D} (h : IsSumOfPositiveShifts P Q)
    (h' : IsSumOfPositiveShifts Q R) : IsSumOfPositiveShifts P R := by
  induction h' with
  | shift j hj => exact h.shift_nonneg j (by lia)
  | zero hQ => exact .zero hQ
  | biprod _ _ ih₁ ih₂ => exact .biprod ih₁ ih₂
  | of_iso e _ ih => exact .of_iso e ih

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] in
/-- **A closure principle for the shape.** A property of objects which holds at `P` and at every
zero object and is stable under shifts, binary biproducts and isomorphism holds at every finite
biproduct of positive shifts of `P`.

Perfectness and cohomological support are two such properties, which is how the iteration of
[Stacks, Tag 09IN] knows that the complement it feeds back into [Stacks, Tag 09IM] is again a
legitimate input to it. -/
theorem IsSumOfPositiveShifts.closure {P Q : D} (h : IsSumOfPositiveShifts P Q) (S : D → Prop)
    (hP : S P) (hshift : ∀ A : D, S A → ∀ j : ℤ, S (A⟦j⟧))
    (hzero : ∀ A : D, IsZero A → S A) (hbiprod : ∀ A B : D, S A → S B → S (A ⊞ B))
    (hiso : ∀ A B : D, (A ≅ B) → S A → S B) : S Q := by
  induction h with
  | shift j _ => exact hshift P hP j
  | zero hQ => exact hzero _ hQ
  | biprod _ _ ih₁ ih₂ => exact hbiprod _ _ ih₁ ih₂
  | of_iso e _ ih => exact hiso _ _ e ih

omit [HasZeroObject D] in
/-- **The complement reproduces itself across one step of the affine-cover induction.** The
two-open step of [Stacks, Tag 09IM] replaces the lift `A` over the open reached so far by
`A ⊞ A⟦1⟧`; if `A` restricted to `U` is `P ⊞ J`, the new restriction is
`(P ⊞ J) ⊞ (P ⊞ J)⟦1⟧`, whose complement of `P` is `J ⊞ (P ⊞ J)⟦1⟧`. This is again a finite
biproduct of positive shifts of `P`: the shift distributes over the biproduct, `P⟦1⟧` is a positive
shift by definition and `J⟦1⟧` is one by
`Stacks.SumOfPositiveShifts.IsSumOfPositiveShifts.shift_nonneg`.

So the shape of the first sentence of [Stacks, Tag 09IN] is an invariant of the induction that
proves [Stacks, Tag 09IM], which is exactly what the remark asserts about it. -/
theorem IsSumOfPositiveShifts.biprod_shift_self {P J : D} (h : IsSumOfPositiveShifts P J) :
    IsSumOfPositiveShifts P (J ⊞ (P ⊞ J)⟦(1 : ℤ)⟧) :=
  .biprod h (.of_iso (Functor.biprodIsoOfAdditive (shiftFunctor D (1 : ℤ)) P J).symm
    (.biprod (.shift 1 le_rfl) (h.shift_nonneg 1 (by norm_num))))

end Predicate

/-! ### The cohomological consequence -/

section Homology

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **The first sentence of [Stacks, Tag 09IN], read cohomologically.** A finite biproduct of
positive shifts of `P` has no cohomology in any degree at or above a bound above which `P` has
none: a summand `P⟦j⟧` with `j ≥ 1` has `H^i(P⟦j⟧) = H^{i + j}(P)`, which vanishes for `i ≥ b`,
and `DerivedCategory.isZero_homology_biprod_of_isZero` adds the summands up.

Together with `DerivedCategory.approximatesFrom_biprod_inl_iff` this is the remark's "in
particular", that the highest degree cohomology sheaf of `P ⊞ Q` is that of `P`. -/
theorem isZero_homology_of_isSumOfPositiveShifts {P : DerivedCategory C} {b : ℤ}
    (hP : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor C i).obj P))
    {Q : DerivedCategory C} (h : IsSumOfPositiveShifts P Q) (i : ℤ) (hi : b ≤ i) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj Q) := by
  induction h with
  | shift j hj => exact DerivedCategory.isZero_homology_shift_of_one_le P b hP j hj i hi
  | zero hQ => exact (DerivedCategory.homologyFunctor C i).map_isZero hQ
  | biprod _ _ ih₁ ih₂ => exact DerivedCategory.isZero_homology_biprod_of_isZero ih₁ ih₂
  | of_iso e _ ih => exact ih.of_iso ((DerivedCategory.homologyFunctor C i).mapIso e).symm

end Homology

end Stacks.SumOfPositiveShifts

end
