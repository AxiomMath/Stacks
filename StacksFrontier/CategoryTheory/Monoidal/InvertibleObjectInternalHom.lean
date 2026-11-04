module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectDual

/-!
# The internal Hom out of an invertible object

Let `C` be a monoidal closed category and `L` an object of `C` with a two-sided tensor inverse
`L'`. Then the internal Hom out of `L` is tensoring with `L'`:

  `𝓗om(L, X) ≅ L' ⊗ X`,

naturally in `X`; in particular the dual `L^∨ = 𝓗om(L, 𝟙)` of an invertible object is its inverse
`L^{⊗ -1}`. Both functors are right adjoint to `L ⊗ -`, the second because `L'` and `L` form an
exact pairing.

## Main definitions

* `CategoryTheory.MonoidalCategory.HasInverse.ihomIso`: `ihom L ≅ tensorLeft L'`.
* `CategoryTheory.MonoidalCategory.HasInverse.ihomUnitIso`: `𝓗om(L, 𝟙) ≅ L'`.
* `CategoryTheory.MonoidalCategory.HasInverse.ihomUnitHasInverse`: the dual `𝓗om(L, 𝟙)` is
  invertible, with inverse `L`.

## References

* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0ESD](https://stacks.math.columbia.edu/tag/0ESD)
-/

@[expose] public noncomputable section

namespace CategoryTheory.MonoidalCategory

open MonoidalClosed

variable {C : Type*} [Category C] [MonoidalCategory C]

namespace HasInverse

variable [MonoidalClosed C] {L : C} (h : HasInverse L)

/-- **The internal Hom out of an invertible object is tensoring with its inverse**: both are
right adjoint to `L ⊗ -`. -/
def ihomIso : ihom L ≅ tensorLeft h.inv :=
  letI : ExactPairing h.inv L :=
    HasInverse.exactPairing h.hasInverseInv
  (ihom.adjunction L).rightAdjointUniq (tensorLeftAdjunction h.inv L)

/-- **The dual of an invertible object is its inverse**: `𝓗om(L, 𝟙) ≅ L'`. -/
def ihomUnitIso : (ihom L).obj (𝟙_ C) ≅ h.inv :=
  h.ihomIso.app (𝟙_ C) ≪≫ ρ_ h.inv

/-- The dual of an invertible object is invertible. -/
def ihomUnitHasInverse : HasInverse ((ihom L).obj (𝟙_ C)) :=
  { inv := L
    isoLeft := whiskerRightIso h.ihomUnitIso L ≪≫ h.isoRight
    isoRight := whiskerLeftIso L h.ihomUnitIso ≪≫ h.isoLeft }

end HasInverse

end CategoryTheory.MonoidalCategory
