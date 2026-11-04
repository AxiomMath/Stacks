module

public import Mathlib.CategoryTheory.Shift.CommShift
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.RingTheory.Dualizing.InvertibleTransport

/-!
# Shifts of invertible objects of a monoidal category

Let `C` be a monoidal category carrying a shift by an additive group `M`, and suppose the shift
commutes with the tensor product in each variable separately, i.e. every `X ⊗ -` and every
`- ⊗ Y` is equipped with a `CategoryTheory.Functor.CommShift M` structure. Then a shift of an
invertible object (`CategoryTheory.MonoidalCategory.IsInvertible`, Stacks 0FFN) is again
invertible: an inverse of `X⟦n⟧` is `X'⟦-n⟧` for `X'` an inverse of `X`.

## Main definitions

* `CategoryTheory.MonoidalCategory.shiftTensorIso`: `(X⟦n⟧) ⊗ Y ≅ (X ⊗ Y)⟦n⟧`, read off from the
  commutation of `- ⊗ Y` with the shift.
* `CategoryTheory.MonoidalCategory.tensorShiftIso`: `X ⊗ (Y⟦n⟧) ≅ (X ⊗ Y)⟦n⟧`, read off from the
  commutation of `X ⊗ -` with the shift.
* `CategoryTheory.MonoidalCategory.HasInverse.shift`: the two-sided tensor inverse `X'⟦-n⟧` of
  `X⟦n⟧` built from a two-sided tensor inverse `X'` of `X`.

## Main results

* `CategoryTheory.MonoidalCategory.IsInvertible.shift`: a shift of an invertible object is
  invertible.
* `CategoryTheory.MonoidalCategory.isInvertible_shift_iff`: `X⟦n⟧` is invertible if and only if
  `X` is.

## Implementation notes

The hypothesis is stated as the pair of instance arguments
`[∀ X : C, (tensorLeft X).CommShift M]` and `[∀ Y : C, (tensorRight Y).CommShift M]` rather than
as a shift–tensor compatibility typeclass, because no such typeclass exists: Mathlib has nothing
relating `MonoidalCategory` to `HasShift` (its only files mentioning both concern the internal
encoding of `HasShift` as a monoidal functor out of `Discrete M`), and the shape this library
already uses for the derived tensor product is exactly this pair of per-variable `CommShift`
fields — see `commShift_left`/`commShift_right` of
`StacksFrontier/Homology/Tor/DerivedTensor.lean`, and the same pair in
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`. A consumer holding
`(curriedTensor C).CommShift₂ h` for any `CategoryTheory.CommShift₂Setup` also satisfies both,
since `commShiftObj` and `commShiftFlipObj` are instance fields of that class; in particular
`CommShift₂Int` suffices.

Only the per-variable commutations are used, never the sign coherence between them: the
construction shifts the first variable up by `n` and the second down by `n`, and the two
commutation isomorphisms are applied one after the other rather than simultaneously, so no
Koszul sign intervenes. That is why the statement does not require `CommShift₂` and is available
for any `CommShift₂Setup`, whose `ε` never appears.

Transport of invertibility along an isomorphism is `Dualizing.isInvertible_of_iso`, reused here
rather than re-proved; it is a general fact about monoidal categories and would sit more
naturally beside `CategoryTheory.MonoidalCategory.IsInvertible` itself than under
`StacksFrontier/RingTheory/Dualizing/`.

## References

* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]
  {M : Type*} [AddGroup M] [HasShift C M]

section Iso

variable [∀ X : C, (tensorLeft X).CommShift M] [∀ Y : C, (tensorRight Y).CommShift M]

/-- Shifting the left tensor factor: `(X⟦n⟧) ⊗ Y ≅ (X ⊗ Y)⟦n⟧`, the component at `X` of the
commutation of `- ⊗ Y` with the shift by `n`. -/
def shiftTensorIso (X Y : C) (n : M) : (X⟦n⟧) ⊗ Y ≅ (X ⊗ Y)⟦n⟧ :=
  ((tensorRight Y).commShiftIso n).app X

/-- Shifting the right tensor factor: `X ⊗ (Y⟦n⟧) ≅ (X ⊗ Y)⟦n⟧`, the component at `Y` of the
commutation of `X ⊗ -` with the shift by `n`. -/
def tensorShiftIso (X Y : C) (n : M) : X ⊗ (Y⟦n⟧) ≅ (X ⊗ Y)⟦n⟧ :=
  ((tensorLeft X).commShiftIso n).app Y

/-- Shifting the two tensor factors in opposite directions leaves the tensor product unchanged:
`(X⟦n⟧) ⊗ (Y⟦-n⟧) ≅ X ⊗ Y`. The first variable is shifted out, then the second, then the two
shifts cancel; no sign coherence between the two commutations is used. -/
def shiftTensorShiftNegIso (X Y : C) (n : M) : (X⟦n⟧) ⊗ (Y⟦-n⟧) ≅ X ⊗ Y :=
  shiftTensorIso X (Y⟦-n⟧) n ≪≫
    (shiftFunctor C n).mapIso (tensorShiftIso X Y (-n)) ≪≫
      (shiftFunctorCompIsoId C (-n) n (by simp)).app (X ⊗ Y)

/-- The mirror image of `shiftTensorShiftNegIso`, cancelling the shifts in the other order:
`(X⟦-n⟧) ⊗ (Y⟦n⟧) ≅ X ⊗ Y`. -/
def shiftNegTensorShiftIso (X Y : C) (n : M) : (X⟦-n⟧) ⊗ (Y⟦n⟧) ≅ X ⊗ Y :=
  tensorShiftIso (X⟦-n⟧) Y n ≪≫
    (shiftFunctor C n).mapIso (shiftTensorIso X Y (-n)) ≪≫
      (shiftFunctorCompIsoId C (-n) n (by simp)).app (X ⊗ Y)

end Iso

section Invertible

variable [∀ X : C, (tensorLeft X).CommShift M] [∀ Y : C, (tensorRight Y).CommShift M]

/-- A two-sided tensor inverse of `X⟦n⟧`, namely `X'⟦-n⟧` for `X'` a two-sided tensor inverse
of `X`. Both trivializations are obtained by cancelling the two opposite shifts against each
other and then applying the corresponding trivialization for `X`. -/
def HasInverse.shift {X : C} (h : HasInverse X) (n : M) : HasInverse (X⟦n⟧) where
  inv := h.inv⟦-n⟧
  isoLeft := shiftTensorShiftNegIso X h.inv n ≪≫ h.isoLeft
  isoRight := shiftNegTensorShiftIso h.inv X n ≪≫ h.isoRight

/-- **A shift of an invertible object is invertible.** If `X` is invertible in the sense of
Stacks 0FFN then so is `X⟦n⟧`, an inverse being `X'⟦-n⟧` for `X'` an inverse of `X`. -/
theorem IsInvertible.shift {X : C} (h : IsInvertible X) (n : M) : IsInvertible (X⟦n⟧) :=
  let ⟨h⟩ := h
  ⟨h.shift n⟩

/-- Invertibility is unaffected by shifting: `X⟦n⟧` is invertible exactly when `X` is. The
backward direction shifts `X⟦n⟧` by `-n` and transports along the cancellation of the two
shifts. -/
theorem isInvertible_shift_iff (X : C) (n : M) : IsInvertible (X⟦n⟧) ↔ IsInvertible X :=
  ⟨fun h => Dualizing.isInvertible_of_iso
      ((shiftFunctorCompIsoId C n (-n) (by simp)).app X) (h.shift (-n)),
    fun h => h.shift n⟩

end Invertible

end CategoryTheory.MonoidalCategory

end
