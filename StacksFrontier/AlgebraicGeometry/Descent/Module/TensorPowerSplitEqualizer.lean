module

public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
public import StacksFrontier.AlgebraicGeometry.Descent.Module.AugmentedDescentComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The split equalizer of the first three tensor powers

Let `R → A` be a map of commutative rings and write `Sₙ` for the `n`-fold tensor power of `A`
over `R`. The coface maps `δ¹₁ : S₁ → S₂` and `δ²₁, δ²₂ : S₂ → S₃`, which insert a `1` into the
indicated tensor slot, form a split equalizer

`S₁ --δ¹₁--> S₂ ⇉ S₃`

of commutative `R`-algebras. The splittings are the two codegeneracy maps `σ⁰₀` and `σ¹₀`,
which multiply a pair of adjacent tensor slots together.

## Main definitions

* `Stacks.Descent.tensorMulAdjacent` is the codegeneracy map `σⁿᵢ`, multiplying the `i`-th and
  `(i + 1)`-st tensor slots of `A^{⊗(n + 2)}`.

## Main results

* `Stacks.Descent.isSplitEqualizerTensorInsertOne` is the split equalizer.

## Implementation notes

The tensor powers and the insertion maps `δⁿᵢ` are
`Stacks.Descent.tensorPowerAlg` and `Stacks.Descent.tensorInsertOne`, so `Sₙ` is
`tensorPowerAlg R A (n - 1)` and the source's `δⁿᵢ` is `tensorInsertOne R A (n - 1) i`.
Both the insertion maps and the codegeneracy maps are determined by their restrictions to the
tensor slots, so every compatibility below reduces along
`Stacks.Descent.tensorPowerAlg_hom_ext` to an identity between composites of `Fin.succAbove` and
`Fin.predAbove`, with no manipulation of elements.

The source deduces this diagram from the split equalizer attached to a module descent datum,
Tag 08WZ, by instantiating at the canonical descent datum of the base ring. We prove it
directly from the same two splittings instead, which avoids transporting the arrows of that
diagram along the unitors `S ⊗_{S, δ} S₂ ≅ S₂` and `S ⊗_{S, δ₁₂} S₃ ≅ S₃`.

The split equalizer is given as data rather than as a `Nonempty`, and it lives in commutative
`R`-algebras: all five arrows are `R`-algebra maps. Since split equalizers are absolute it
transports to `R`-modules, or to `A`-modules, along the relevant forgetful functor.

## References

* [Stacks Project, Tag 08WZ](https://stacks.math.columbia.edu/tag/08WZ)
* [Stacks Project, Tag 08X3](https://stacks.math.columbia.edu/tag/08X3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Descent

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

/-- Multiplication of the `i`-th and `(i + 1)`-st tensor slots, the map
`A^{⊗(n + 2)} ⟶ A^{⊗(n + 1)}` carrying the `j`-th slot to the `i.predAbove j`-th one. For
`n = 0` and `n = 1` these are the maps `σ⁰₀ (a₀ ⊗ a₁) = a₀a₁` and
`σ¹₀ (a₀ ⊗ a₁ ⊗ a₂) = a₀a₁ ⊗ a₂` of the source. -/
noncomputable def tensorMulAdjacent (n : ℕ) (i : Fin (n + 1)) :
    tensorPowerAlg R A (n + 1) ⟶ tensorPowerAlg R A n :=
  tensorSlotDesc R A (n + 1) fun j => tensorSlot R A n (i.predAbove j)

/-- Multiplying the `i`-th and `(i + 1)`-st slots together merges the two slots on either side
of the pivot and shifts the later ones down. -/
@[simp]
lemma tensorSlot_comp_tensorMulAdjacent (n : ℕ) (i : Fin (n + 1)) (j : Fin (n + 2)) :
    tensorSlot R A (n + 1) j ≫ tensorMulAdjacent R A n i =
      tensorSlot R A n (i.predAbove j) :=
  tensorSlot_comp_tensorSlotDesc R A (n + 1) _ j

/-- **Stacks Project, Tag 08X3.** The diagram `S₁ --δ¹₁--> S₂ ⇉ S₃` of tensor powers of `A`
over `R`, whose parallel arrows are `δ²₂` and `δ²₁`, is a split equalizer of commutative
`R`-algebras. Its splittings are the codegeneracy maps `σ⁰₀` and `σ¹₀`. -/
@[stacks 08X3]
noncomputable def isSplitEqualizerTensorInsertOne :
    IsSplitEqualizer (tensorInsertOne R A 1 2) (tensorInsertOne R A 1 1)
      (tensorInsertOne R A 0 1) where
  leftRetraction := tensorMulAdjacent R A 0 0
  rightRetraction := tensorMulAdjacent R A 1 0
  condition := by
    refine tensorPowerAlg_hom_ext R A 0 fun j => ?_
    obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) j 0
    rw [← Category.assoc, ← Category.assoc, tensorSlot_comp_tensorInsertOne,
      tensorSlot_comp_tensorInsertOne, tensorSlot_comp_tensorInsertOne]
    rfl
  ι_leftRetraction := by
    refine tensorPowerAlg_hom_ext R A 0 fun j => ?_
    obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) j 0
    rw [← Category.assoc, tensorSlot_comp_tensorInsertOne,
      tensorSlot_comp_tensorMulAdjacent, Category.comp_id]
    rfl
  bottom_rightRetraction := by
    refine tensorPowerAlg_hom_ext R A 1 fun j => ?_
    rw [← Category.assoc, tensorSlot_comp_tensorInsertOne,
      tensorSlot_comp_tensorMulAdjacent, Category.comp_id]
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) j 0
      rfl
  top_rightRetraction := by
    refine tensorPowerAlg_hom_ext R A 1 fun j => ?_
    rw [← Category.assoc, ← Category.assoc, tensorSlot_comp_tensorInsertOne,
      tensorSlot_comp_tensorMulAdjacent, tensorSlot_comp_tensorMulAdjacent]
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) j 0
      rfl

end Stacks.Descent
