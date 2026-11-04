module

public import Mathlib.CategoryTheory.Triangulated.Generators
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories

/-!
# Bounded-shift operations on full subcategories along an exact functor

Let `F : C ⥤ D` be an exact functor of pretriangulated categories, let `P` be a property of
objects of `C` and let `Q` be one of `D`, and suppose `F` carries the objects of `P` into `Q`.
This file proves that `F` then carries the explicit subcategory `smd(add(P[c, d])^{⋆ n})` of `C`
into the subcategory `smd(add(Q[c, d])^{⋆ n})` of `D`, **with the same shift interval `[c, d]`
and the same number `n` of extensions on both sides**.

This is the functoriality statement of Derived Categories, Remark 13.35.5
([Stacks, Tag 0FX5]), in the form in which the explicit subcategories of
[Stacks, Tag 0FX9] are stated: the shifts used are restricted to a window `[c, d]`, and the
window is tracked through the conclusion.

## The argument

Each of the four closure operations making up `smd(add(−[c, d])^{⋆ n})` transfers separately,
and the proof is just their composition.

* *Shifts.* An object `X` of `P[c, d]` has `X⟦i⟧ ≅ Y` with `Y ∈ P` and `i ∈ [c, d]`. The
  commutation isomorphism of `F` with the shift turns this into `(F X)⟦i⟧ ≅ F Y`, with
  `F Y ∈ Q` by hypothesis and the *same* `i`. This is the only step that touches the interval,
  and it preserves it on the nose; no shift outside `[c, d]` is ever produced.
* *Finite direct sums.* The inverse image under `F` of a subcategory closed under binary
  products is again closed under binary products, because `X ⨯ Y` is the middle vertex of a
  distinguished triangle with vanishing third map, which `F` carries to a distinguished triangle
  with vanishing third map, hence to a split one.
* *Extensions.* An extension `A ⟶ X ⟶ B ⟶ A⟦1⟧` is carried by `F` to a distinguished triangle
  `F A ⟶ F X ⟶ F B ⟶ (F A)⟦1⟧`, so `X ∈ A ⋆ B` gives `F X ∈ F(A) ⋆ F(B)`; iterating gives the
  same count `n` of extensions on both sides.
* *Direct summands.* The inverse image under `F` of a subcategory stable under retracts is
  stable under retracts, a functor carrying a retract diagram to a retract diagram.

## Main results

* `retractClosure_extensionProductIter_biSup_shift_inverseImage_of_le` (in the
  `Stacks.TriangulatedGenerators` namespace): **[Stacks, Tag 0FX5]** for the bounded-shift form,
  along an exact functor.

## Implementation notes

The shifted family `P[c, d]` is spelled `⨆ i ∈ Set.Icc c d, P.isoClosure.shift i`, as in
`StacksFrontier/CategoryTheory/Triangulated/Generators.lean`; `ObjectProperty.shift` is the inverse
image under the shift functor, and the `isoClosure` is what makes the family insensitive to `P`
not being closed under isomorphisms. The source's `smd` is
`CategoryTheory.ObjectProperty.retractClosure`, `add` is
`CategoryTheory.ObjectProperty.binaryProductsClosure` and `⋆` iterated `n` times is
`CategoryTheory.ObjectProperty.extensionProductIter`.

The `stacks` attribute carries a clause, because [Stacks, Tag 0FX5] is a remark asserting that
*all* of the constructions of Derived Categories, Section 13.35 are functorial along an exact
functor; what is proved here is the one assertion the applications use, for the bounded form of
the subcategories `Cₙ = smd(add(E[c, d])^{⋆ n})`.

Neither `[IsTriangulated C]` nor `[IsTriangulated D]` is assumed: no step needs the octahedral
property, since the iterated extension product is taken in the fixed bracketing of
`CategoryTheory.ObjectProperty.extensionProductIter_succ` and never reassociated.

The unbounded-shift form of the same transfer, with `P.shiftClosure ℤ` in place of `P[c, d]`,
is `Stacks.TriangulatedGenerators.triangEnvelopeIter_inverseImage_of_le`; it cannot supply this
statement, since passing through `ObjectProperty.triangEnvelopeIter` forgets the interval and
`CategoryTheory.ObjectProperty.triangEnvelopeIter_eq_iSup_retractClosure_extensionProductIter`
([Stacks, Tag 0FX9]) only recovers *some* window `[-m, m]`, with no bound on `m`.

## References

* [Stacks Project, Tag 0FX5](https://stacks.math.columbia.edu/tag/0FX5)
* [Stacks Project, Tag 0FX9](https://stacks.math.columbia.edu/tag/0FX9)
* [Stacks Project, Tag 0FX4](https://stacks.math.columbia.edu/tag/0FX4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

namespace Stacks.TriangulatedGenerators

/-! ### Transfer of the closure operations along a functor -/

section Shifts

variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D) [F.CommShift ℤ]

/-- The shifts of `P` in a window transfer along a functor commuting with the shift **into the
same window**: if `X⟦i⟧ ≅ Y` with `Y` in `P` and `i ∈ [c, d]`, then the commutation isomorphism
of `F` with the shift gives `(F X)⟦i⟧ ≅ F Y` with `F Y` in `Q` and the same `i`. -/
private lemma biSup_shift_isoClosure_inverseImage_of_le {P : ObjectProperty C}
    {Q : ObjectProperty D} (h : ∀ ⦃X : C⦄, P X → Q (F.obj X)) (c d : ℤ) :
    (⨆ i ∈ Set.Icc c d, P.isoClosure.shift i) ≤
      (⨆ i ∈ Set.Icc c d, Q.isoClosure.shift i).inverseImage F := by
  refine iSup₂_le fun i hi X hX => ?_
  obtain ⟨Y, hY, ⟨e⟩⟩ := hX
  simp only [prop_inverseImage_iff, prop_iSup_iff]
  exact ⟨i, hi, F.obj Y, h hY, ⟨((F.commShiftIso i).app X).symm ≪≫ F.mapIso e⟩⟩

end Shifts

section Transfer

variable {C D : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

/-- The extension product transfers along an exact functor: an extension of an object of `A₂` by
an object of `A₁` is carried to an extension of an object of `B₂` by an object of `B₁`, since an
exact functor carries a distinguished triangle to a distinguished triangle. -/
private lemma extensionProduct_inverseImage_of_le {A₁ A₂ : ObjectProperty C}
    {B₁ B₂ : ObjectProperty D} (h₁ : A₁ ≤ B₁.inverseImage F) (h₂ : A₂ ≤ B₂.inverseImage F) :
    extensionProduct A₁ A₂ ≤ (extensionProduct B₁ B₂).inverseImage F := by
  rintro X ⟨Y, Z, f, g, w, hT, hY, hZ⟩
  exact ⟨F.obj Y, F.obj Z, F.map f, F.map g, _, F.map_distinguished _ hT, h₁ _ hY, h₂ _ hZ⟩

/-- Iterated extension products transfer along an exact functor, **with the same number of
extensions on both sides**: `n` extensions of objects of `A` are carried to `n` extensions of
objects of `B`. -/
private lemma extensionProductIter_inverseImage_of_le {A : ObjectProperty C}
    {B : ObjectProperty D} (h : A ≤ B.inverseImage F) (n : ℕ) :
    A.extensionProductIter n ≤ (B.extensionProductIter n).inverseImage F := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simp only [extensionProductIter_succ]
    exact extensionProduct_inverseImage_of_le F h ih

/-- **The bounded-shift form of `smd(add(P[c, d])^{⋆ n})` is functorial along an exact functor.**
Let `F : C ⥤ D` be an exact functor of pretriangulated categories, let `P` be a property of
objects of `C` and `Q` one of `D`, and suppose `F` carries every object satisfying `P` to one
satisfying `Q`. Then `F` carries `smd(add(P[c, d])^{⋆ n})` into `smd(add(Q[c, d])^{⋆ n})`: the
shift interval `[c, d]` and the number `n` of extensions are the same on both sides.

This is Derived Categories, Remark 13.35.5 ([Stacks, Tag 0FX5]) for this one of the section's
constructions, namely the explicit subcategories `Cₙ = smd(add(E[c, d])^{⋆ n})` built from a
bounded range of shifts as in [Stacks, Tag 0FX9]. Tracking the interval is the content: the
unbounded-shift form `Stacks.TriangulatedGenerators.triangEnvelopeIter_inverseImage_of_le`,
stated with `ObjectProperty.triangEnvelopeIter`, gives no control on which shifts of `Q` the
image uses. -/
@[stacks 0FX5 "for the bounded-shift form `smd(add(P[c, d])^{⋆ n})`, along an exact functor"]
theorem retractClosure_extensionProductIter_biSup_shift_inverseImage_of_le
    {P : ObjectProperty C} {Q : ObjectProperty D} (h : ∀ ⦃X : C⦄, P X → Q (F.obj X))
    (c d : ℤ) (n : ℕ) :
    ((⨆ i ∈ Set.Icc c d, P.isoClosure.shift i).binaryProductsClosure.extensionProductIter n
      ).retractClosure ≤
      ((((⨆ i ∈ Set.Icc c d, Q.isoClosure.shift i).binaryProductsClosure.extensionProductIter n
        ).retractClosure).inverseImage F) := by
  have hadd := isClosedUnderBinaryProducts_inverseImage F
    (⨆ i ∈ Set.Icc c d, Q.isoClosure.shift i).binaryProductsClosure
  have hsmd := isStableUnderRetracts_inverseImage
    (((⨆ i ∈ Set.Icc c d, Q.isoClosure.shift i).binaryProductsClosure.extensionProductIter n
      ).retractClosure) F
  rw [retractClosure_le_iff]
  refine (extensionProductIter_inverseImage_of_le F (limitsClosure_le ?_) n).trans
    fun X hX => le_retractClosure _ _ hX
  exact (biSup_shift_isoClosure_inverseImage_of_le F h c d).trans
    fun X hX => le_limitsClosure _ _ _ hX

end Transfer

end Stacks.TriangulatedGenerators

end

