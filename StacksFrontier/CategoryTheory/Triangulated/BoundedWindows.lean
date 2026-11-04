module

public import Mathlib.Tactic.Ring
public import StacksFrontier.CategoryTheory.Triangulated.ExactFunctorBoundedOperations

/-!
# Windows of shifts under the closure operations

Let `C` be a pretriangulated category and `E` a property of its objects. Write `E[c, d]` for the
family of the shifts `E⟦-i⟧` with `i` in the window `[c, d]`, and `smd`, `add` and `⋆ n` for the
closure under direct summands, under finite direct sums and under `n` extensions. This file
computes what the closure operations do to the window:

* shifting `smd(add(E[c, d]))` by `j` translates its window to `[c + j, d + j]`;
* a nested `smd(add(−))` is absorbed and the two windows add up,
  `smd(add(smd(add(E[c, d]))[c', d'])^{⋆ n}) ≤ smd(add(E[c + c', d + d'])^{⋆ n})`;
* `smd(add(E[c, d])^{⋆ n})` grows with the window and with `n`.

This is the arithmetic of Derived Categories, Section 13.35 — [Stacks, Tag 0FX2] for the inner
`smd` crossing the extension product, [Stacks, Tag 0FX4] for the tower `smd(add(−)^{⋆ n})` being
closed under direct sums and summands — in the bounded-window form of [Stacks, Tag 0FX9], where
the window is tracked through the conclusion. It is the step at which the proof of
[Stacks, Tag 0FZ7] turns the two windows it has, the one coming from the diagonal and the one
coming from the cohomology of the sheaf, into the single window of its conclusion.

## Main results

* `TriangulatedGenerators.retractClosure_extensionProductIter_biSup_shift_le_of_retractClosure`
  (also called `retractClosure_extensionProductIter_biSup_shift_retractClosure_le`): the
  window-tracking absorption of a nested `smd(add(−))`.

## Implementation notes

`smd`, `add` and `⋆ n` are `CategoryTheory.ObjectProperty.retractClosure`,
`CategoryTheory.ObjectProperty.binaryProductsClosure` and
`CategoryTheory.ObjectProperty.extensionProductIter`, and `E[c, d]` is
`⨆ i ∈ Set.Icc c d, E.isoClosure.shift i`. `ObjectProperty.shift j` is the inverse image under
`⟦j⟧`, so a member of `E.isoClosure.shift j` is isomorphic to some `E⟦-j⟧`; the `isoClosure` is
what makes the family insensitive to `E` not being closed under isomorphisms.

## References

* [Stacks Project, Tag 0FX2](https://stacks.math.columbia.edu/tag/0FX2)
* [Stacks Project, Tag 0FX4](https://stacks.math.columbia.edu/tag/0FX4)
* [Stacks Project, Tag 0FX9](https://stacks.math.columbia.edu/tag/0FX9)
* [Stacks Project, Tag 0FZ7](https://stacks.math.columbia.edu/tag/0FZ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

namespace Stacks.TriangulatedGenerators

section BoundedWindows

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- A shift of a property of objects stable under retracts is stable under retracts: the shift,
being a functor, carries a retract diagram to a retract diagram. -/
private lemma isStableUnderRetracts_shift (R : ObjectProperty C) [R.IsStableUnderRetracts]
    (j : ℤ) : (R.shift j).IsStableUnderRetracts where
  of_retract h hY := R.prop_of_retract (h.map (shiftFunctor C j)) hY

/-- A shift of a property of objects closed under binary products and isomorphisms is closed
under binary products: the shift is an equivalence, so it preserves binary products. -/
private lemma isClosedUnderBinaryProducts_shift (R : ObjectProperty C)
    [R.IsClosedUnderBinaryProducts] [R.IsClosedUnderIsomorphisms] (j : ℤ) :
    (R.shift j).IsClosedUnderBinaryProducts := by
  refine isClosedUnderBinaryProducts_of_prop_prod _ ?_
  intro A B hA hB
  exact R.prop_of_iso (PreservesLimitPair.iso (shiftFunctor C j) A B).symm
    (R.prop_prod _ _ hA hB)

/-- **Shifting `smd(add(E[c, d]))` translates its window.** If `Y⟦j⟧` is a direct summand of a
finite direct sum of shifts `E⟦-i⟧` with `i ∈ [c, d]`, and `j` lies in `[c', d']`, then `Y`
itself is a direct summand of a finite direct sum of shifts `E⟦-i⟧` with `i ∈ [c + c', d + d']`.

The mechanism is that `Z⟦-j⟧⟦i + j⟧ ≅ Z⟦i⟧`, so shifting by `-j` moves an object of `E[c, d]`
into `E[c + j, d + j]`; the two outer closure operations transfer because the inverse image of a
retract-stable property under a functor is retract-stable and the shift preserves binary
products. -/
private lemma shift_le_retractClosure_binaryProductsClosure (E : ObjectProperty C)
    (c d c' d' j : ℤ) (hj : j ∈ Set.Icc c' d') :
    (((⨆ i ∈ Set.Icc c d, E.isoClosure.shift i).binaryProductsClosure).retractClosure).shift j ≤
      (⨆ i ∈ Set.Icc (c + c') (d + d'),
        E.isoClosure.shift i).binaryProductsClosure.retractClosure := by
  have hprod := isClosedUnderBinaryProducts_retractClosure
    (⨆ i ∈ Set.Icc (c + c') (d + d'), E.isoClosure.shift i).binaryProductsClosure
  have h1 := isStableUnderRetracts_shift
    ((⨆ i ∈ Set.Icc (c + c') (d + d'),
      E.isoClosure.shift i).binaryProductsClosure.retractClosure) (-j)
  have h2 := isClosedUnderBinaryProducts_shift
    ((⨆ i ∈ Set.Icc (c + c') (d + d'),
      E.isoClosure.shift i).binaryProductsClosure.retractClosure) (-j)
  have key : ((⨆ i ∈ Set.Icc c d, E.isoClosure.shift i).binaryProductsClosure).retractClosure ≤
      ((⨆ i ∈ Set.Icc (c + c') (d + d'),
        E.isoClosure.shift i).binaryProductsClosure.retractClosure).shift (-j) := by
    rw [retractClosure_le_iff]
    refine limitsClosure_le (iSup₂_le fun i hi Z hZ => ?_)
    have heq : (E.isoClosure.shift (i + j)).shift (-j) = E.isoClosure.shift i :=
      E.isoClosure.shift_shift (-j) (i + j) i (by ring)
    have hmem : ((E.isoClosure.shift (i + j)).shift (-j)) Z := by rw [heq]; exact hZ
    simp only [Set.mem_Icc] at hi hj
    exact le_retractClosure _ _ (le_limitsClosure _ _ _
      ((prop_iSup_iff _ _).2 ⟨i + j, (prop_iSup_iff _ _).2
        ⟨Set.mem_Icc.2 ⟨by omega, by omega⟩, hmem⟩⟩))
  intro Y hY
  exact ObjectProperty.prop_of_iso _ (shiftShiftNeg Y j) (key _ hY)

/-- If `P` lies in `smd(add(Q))`, then `smd(add(P)^{⋆ n})` lies in `smd(add(Q)^{⋆ n})`. -/
private lemma retractClosure_extensionProductIter_le_of_le_retractClosure {P Q : ObjectProperty C}
    (h : P ≤ Q.binaryProductsClosure.retractClosure) (n : ℕ) :
    (P.binaryProductsClosure.extensionProductIter n).retractClosure ≤
      (Q.binaryProductsClosure.extensionProductIter n).retractClosure := by
  have := isClosedUnderBinaryProducts_retractClosure Q.binaryProductsClosure
  refine (monotone_retractClosure (monotone_extensionProductIter
    (limitsClosure_le h) n)).trans ?_
  rw [retractClosure_extensionProductIter_retractClosure]

/-- **A nested `smd(add(−))` is absorbed, and the two windows add up.** For a property of
objects `E` of a triangulated category, every direct summand of an `n`-fold extension of finite
direct sums of shifts, by `[c', d']`, of objects of `smd(add(E[c, d]))` is a direct summand of an
`n`-fold extension of finite direct sums of objects of `E[c + c', d + d']`:
`smd(add(smd(add(E[c, d]))[c', d'])^{⋆ n}) ≤ smd(add(E[c + c', d + d'])^{⋆ n})`.

This is the bounded-window form of the absorption used throughout Derived Categories, Section
13.35 — [Stacks, Tag 0FX2] for the inner `smd` crossing the extension product, and
[Stacks, Tag 0FX4] for the tower `smd(add(−)^{⋆ n})` being closed under direct sums and
summands — together with the translation of the window by a shift. It is the step at which the
proof of [Stacks, Tag 0FZ7] turns the two windows it has, the one coming from the diagonal and
the one coming from the cohomology of the sheaf, into the single window of its conclusion. -/
theorem retractClosure_extensionProductIter_biSup_shift_le_of_retractClosure (E : ObjectProperty C)
    (c d c' d' : ℤ) (n : ℕ) :
    ((⨆ j ∈ Set.Icc c' d',
        ((⨆ i ∈ Set.Icc c d,
          E.isoClosure.shift i).binaryProductsClosure).retractClosure.isoClosure.shift j
      ).binaryProductsClosure.extensionProductIter n).retractClosure ≤
      ((⨆ i ∈ Set.Icc (c + c') (d + d'),
        E.isoClosure.shift i).binaryProductsClosure.extensionProductIter n).retractClosure := by
  refine retractClosure_extensionProductIter_le_of_le_retractClosure (iSup₂_le fun j hj => ?_) n
  rw [ObjectProperty.isoClosure_eq_self]
  exact shift_le_retractClosure_binaryProductsClosure E c d c' d' j hj

/-- The subcategory `smd(add(E[c, d])^{⋆ n})` grows with the window and with the number of
extensions: widening `[c, d]` is monotonicity of the four closure operations, and raising `n`
uses that `smd(add(E[c₀, d₀]))` contains a zero object, so that an object of a stage of the tower
is an extension of it by an object of `add(E[c₀, d₀])`. -/
private lemma retractClosure_extensionProductIter_biSup_mono (E : ObjectProperty C)
    {c d c₀ d₀ : ℤ} (hc : c₀ ≤ c) (hd : d ≤ d₀) {n n₀ : ℕ} (hn : n ≤ n₀)
    (hne : (⨆ i ∈ Set.Icc c₀ d₀, E.isoClosure.shift i).Nonempty) :
    ((⨆ i ∈ Set.Icc c d, E.isoClosure.shift i).binaryProductsClosure.extensionProductIter n
      ).retractClosure ≤
      ((⨆ i ∈ Set.Icc c₀ d₀, E.isoClosure.shift i).binaryProductsClosure.extensionProductIter n₀
        ).retractClosure := by
  have := hne
  have hwin : (⨆ i ∈ Set.Icc c d, E.isoClosure.shift i) ≤
      ⨆ i ∈ Set.Icc c₀ d₀, E.isoClosure.shift i :=
    iSup₂_le fun i hi => le_iSup₂_of_le i (Set.Icc_subset_Icc hc hd hi) le_rfl
  refine (retractClosure_extensionProductIter_le_of_le_retractClosure
    (hwin.trans ((le_limitsClosure _ _).trans (le_retractClosure _))) n).trans ?_
  rw [← retractClosure_extensionProductIter_retractClosure,
    ← retractClosure_extensionProductIter_retractClosure (n := n₀)]
  exact monotone_retractClosure (monotone'_extensionProductIter _ hn)

/-- Alternative name for `retractClosure_extensionProductIter_biSup_shift_le_of_retractClosure`.
-/
alias retractClosure_extensionProductIter_biSup_shift_retractClosure_le :=
  retractClosure_extensionProductIter_biSup_shift_le_of_retractClosure

end BoundedWindows

end Stacks.TriangulatedGenerators

end
