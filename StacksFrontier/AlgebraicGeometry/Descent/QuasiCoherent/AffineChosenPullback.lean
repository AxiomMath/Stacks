module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Chosen pullbacks of a morphism of affine schemes with itself

For an `R`-algebra `B` the fibre square of `Spec B ⟶ Spec R` with itself is `Spec (B ⊗[R] B)`,
and the threefold fibre product is `Spec (B ⊗[R] B ⊗[R] B)`.  This file packages both as
`CategoryTheory.Limits.ChosenPullback` and `CategoryTheory.Limits.ChosenPullback₃`.

## Main definitions

* `Stacks.Descent.specTensorChosenPullback`: `Spec (B ⊗[R] B)` as a chosen pullback of
  `Spec B ⟶ Spec R` with itself, with projections `Spec` of `b ↦ b ⊗ 1` and `b ↦ 1 ⊗ b`.
* `Stacks.Descent.specTensorChosenPullback₃`: `Spec (B ⊗[R] B ⊗[R] B)` as the compatible chosen
  threefold wide pullback.

## Implementation notes

The twofold square is `AlgebraicGeometry.isPullback_SpecMap_of_isPushout` applied to Mathlib's
`CommRingCat.isPushout_tensorProduct`.

The threefold one is *not* obtained from a third tensor-product pushout: the chosen pullback it
has to provide is the pullback of `Spec (B ⊗[R] B) ⟶ Spec B` along `b ↦ 1 ⊗ b` and of
`Spec (B ⊗[R] B) ⟶ Spec B` along `b ↦ b ⊗ 1`, and presenting `(B ⊗[R] B) ⊗[B] (B ⊗[R] B)` as a
pushout in `CommRingCat` would need two different `Algebra B (B ⊗[R] B)` instances on one
carrier.  Instead the square is obtained by *pasting*: `CategoryTheory.IsPullback.of_right`
against the pushout square of `B ⊗[R] (B ⊗[R] B)` over `R` on the left and the twofold square on
the right.  Only ring-map identities between pure tensors are then needed, and all of them hold
by `Algebra.TensorProduct.ext`.

The threefold tensor product is written right-associated, `B ⊗[R] (B ⊗[R] B)`, because that is
the shape `CommRingCat.isPushout_tensorProduct R B (B ⊗[R] B)` produces.

## References

* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Stacks.Descent

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-! ### The ring maps between the iterated tensor powers -/

/-- The structure map `R ⟶ B` of an `R`-algebra, in `CommRingCat`. -/
abbrev algHom : CommRingCat.of R ⟶ CommRingCat.of B :=
  CommRingCat.ofHom (algebraMap R B)

/-- The inclusion `b ↦ b ⊗ 1` of the first factor of `B ⊗[R] B`. -/
abbrev tensorInl : CommRingCat.of B ⟶ CommRingCat.of (B ⊗[R] B) :=
  CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom

/-- The inclusion `b ↦ 1 ⊗ b` of the second factor of `B ⊗[R] B`. -/
abbrev tensorInr : CommRingCat.of B ⟶ CommRingCat.of (B ⊗[R] B) :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := B)).toRingHom

/-- The inclusion `b₀ ⊗ b₁ ↦ b₀ ⊗ (b₁ ⊗ 1)` of the first two factors of the threefold tensor
power. -/
abbrev tensorMap₀₁ :
    CommRingCat.of (B ⊗[R] B) ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) :=
  CommRingCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id R B) (Algebra.TensorProduct.includeLeft
      (R := R) (S := R) (A := B) (B := B))).toRingHom

/-- The inclusion `b₀ ⊗ b₂ ↦ b₀ ⊗ (1 ⊗ b₂)` of the outer two factors of the threefold tensor
power. -/
abbrev tensorMap₀₂ :
    CommRingCat.of (B ⊗[R] B) ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) :=
  CommRingCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id R B) (Algebra.TensorProduct.includeRight
      (R := R) (A := B) (B := B))).toRingHom

/-- The inclusion `b₁ ⊗ b₂ ↦ 1 ⊗ (b₁ ⊗ b₂)` of the last two factors of the threefold tensor
power. -/
abbrev tensorMap₁₂ :
    CommRingCat.of (B ⊗[R] B) ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) :=
  CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := B ⊗[R] B)).toRingHom

/-- The inclusion `b ↦ b ⊗ (1 ⊗ 1)` of the first factor of the threefold tensor power. -/
abbrev tensorIncl₀ : CommRingCat.of B ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) :=
  CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B) (B := B ⊗[R] B))

/-- The inclusion `b ↦ 1 ⊗ (b ⊗ 1)` of the middle factor of the threefold tensor power. -/
abbrev tensorIncl₁ : CommRingCat.of B ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) :=
  CommRingCat.ofHom
    ((Algebra.TensorProduct.includeRight (R := R) (A := B) (B := B ⊗[R] B)).comp
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := B))).toRingHom

/-- The inclusion `b ↦ 1 ⊗ (1 ⊗ b)` of the last factor of the threefold tensor power. -/
abbrev tensorIncl₂ : CommRingCat.of B ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) :=
  CommRingCat.ofHom
    ((Algebra.TensorProduct.includeRight (R := R) (A := B) (B := B ⊗[R] B)).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := B))).toRingHom

/-- The structure map `R ⟶ B` followed by `b ↦ b ⊗ 1` is the structure map of `B ⊗[R] B`. -/
@[simp]
theorem algHom_comp_tensorInl :
    algHom R B ≫ tensorInl R B = CommRingCat.ofHom (algebraMap R (B ⊗[R] B)) := by
  ext r
  exact (Algebra.TensorProduct.algebraMap_apply (R := R) (S := R) (A := B) (B := B) r).symm

/-- `b ↦ 1 ⊗ b` followed by `Stacks.Descent.tensorMap₀₁` is `b ↦ 1 ⊗ (b ⊗ 1)`. -/
@[simp]
theorem tensorInr_comp_tensorMap₀₁ :
    tensorInr R B ≫ tensorMap₀₁ R B = tensorIncl₁ R B := by
  ext b
  simp

/-- `b ↦ b ⊗ 1` followed by `Stacks.Descent.tensorMap₁₂` is `b ↦ 1 ⊗ (b ⊗ 1)`. -/
@[simp]
theorem tensorInl_comp_tensorMap₁₂ :
    tensorInl R B ≫ tensorMap₁₂ R B = tensorIncl₁ R B := by
  ext b
  rfl

/-- `b ↦ b ⊗ 1` followed by `Stacks.Descent.tensorMap₀₁` is `b ↦ b ⊗ (1 ⊗ 1)`. -/
@[simp]
theorem tensorInl_comp_tensorMap₀₁ :
    tensorInl R B ≫ tensorMap₀₁ R B = tensorIncl₀ R B := by
  ext b
  simp [Algebra.TensorProduct.one_def]

/-- `b ↦ 1 ⊗ b` followed by `Stacks.Descent.tensorMap₁₂` is `b ↦ 1 ⊗ (1 ⊗ b)`. -/
@[simp]
theorem tensorInr_comp_tensorMap₁₂ :
    tensorInr R B ≫ tensorMap₁₂ R B = tensorIncl₂ R B := by
  ext b
  rfl

/-- `b ↦ b ⊗ 1` followed by `Stacks.Descent.tensorMap₀₂` is `b ↦ b ⊗ (1 ⊗ 1)`. -/
@[simp]
theorem tensorInl_comp_tensorMap₀₂ :
    tensorInl R B ≫ tensorMap₀₂ R B = tensorIncl₀ R B := by
  ext b
  simp [Algebra.TensorProduct.one_def]

/-- `b ↦ 1 ⊗ b` followed by `Stacks.Descent.tensorMap₀₂` is `b ↦ 1 ⊗ (1 ⊗ b)`. -/
@[simp]
theorem tensorInr_comp_tensorMap₀₂ :
    tensorInr R B ≫ tensorMap₀₂ R B = tensorIncl₂ R B := by
  ext b
  simp [Algebra.TensorProduct.includeRight_apply]

/-- The structure map of `B ⊗[R] B` followed by `Stacks.Descent.tensorMap₀₂` is the structure
map of `B ⊗[R] (B ⊗[R] B)`. -/
@[simp]
theorem algebraMap_comp_tensorMap₀₂ :
    CommRingCat.ofHom (algebraMap R (B ⊗[R] B)) ≫ tensorMap₀₂ R B =
      CommRingCat.ofHom (algebraMap R (B ⊗[R] (B ⊗[R] B))) := by
  ext r
  exact ((Algebra.TensorProduct.map (AlgHom.id R B)
    (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := B))).commutes r)

/-! ### The chosen pullbacks -/

/-- `Spec B ×_{Spec R} Spec B` is `Spec (B ⊗[R] B)`. -/
theorem isPullback_specTensor :
    IsPullback (Spec.map (tensorInl R B)) (Spec.map (tensorInr R B))
      (Spec.map (algHom R B)) (Spec.map (algHom R B)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R B B)

/-- `Spec B ×_{Spec R} Spec (B ⊗[R] B)` is `Spec (B ⊗[R] (B ⊗[R] B))`. -/
theorem isPullback_specTensorTriple :
    IsPullback (Spec.map (tensorIncl₀ R B)) (Spec.map (tensorMap₁₂ R B))
      (Spec.map (algHom R B)) (Spec.map (CommRingCat.ofHom (algebraMap R (B ⊗[R] B)))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R B (B ⊗[R] B))

/-- `Spec (B ⊗[R] B) ×_{Spec B} Spec (B ⊗[R] B)`, fibred along `Spec` of `b ↦ 1 ⊗ b` and of
`b ↦ b ⊗ 1`, is `Spec (B ⊗[R] (B ⊗[R] B))`. -/
theorem isPullback_specTensorMid :
    IsPullback (Spec.map (tensorMap₀₁ R B)) (Spec.map (tensorMap₁₂ R B))
      (Spec.map (tensorInr R B)) (Spec.map (tensorInl R B)) := by
  refine IsPullback.of_right (h₁₂ := Spec.map (tensorInl R B)) ?_ ?_
    (isPullback_specTensor R B)
  · rw [← Spec.map_comp, ← Spec.map_comp, tensorInl_comp_tensorMap₀₁, algHom_comp_tensorInl]
    exact isPullback_specTensorTriple R B
  · rw [← Spec.map_comp, ← Spec.map_comp, tensorInr_comp_tensorMap₀₁,
      tensorInl_comp_tensorMap₁₂]

/-- **`Spec (B ⊗[R] B)` as a chosen pullback of `Spec B ⟶ Spec R` with itself.** -/
def specTensorChosenPullback : ChosenPullback (Spec.map (algHom R B)) (Spec.map (algHom R B)) where
  pullback := Spec (CommRingCat.of (B ⊗[R] B))
  p₁ := Spec.map (tensorInl R B)
  p₂ := Spec.map (tensorInr R B)
  condition := (isPullback_specTensor R B).w
  isLimit := (isPullback_specTensor R B).isLimit
  p := Spec.map (CommRingCat.ofHom (algebraMap R (B ⊗[R] B)))
  hp₁ := by rw [← Spec.map_comp, algHom_comp_tensorInl]

/-- The first projection of `Stacks.Descent.specTensorChosenPullback` is `Spec` of
`b ↦ b ⊗ 1`. -/
@[simp]
theorem specTensorChosenPullback_p₁ :
    (specTensorChosenPullback R B).p₁ = Spec.map (tensorInl R B) := rfl

/-- The second projection of `Stacks.Descent.specTensorChosenPullback` is `Spec` of
`b ↦ 1 ⊗ b`. -/
@[simp]
theorem specTensorChosenPullback_p₂ :
    (specTensorChosenPullback R B).p₂ = Spec.map (tensorInr R B) := rfl

/-- The structure morphism of `Stacks.Descent.specTensorChosenPullback` to `Spec R` is `Spec` of
the structure map of `B ⊗[R] B`. -/
@[simp]
theorem specTensorChosenPullback_p :
    (specTensorChosenPullback R B).p =
      Spec.map (CommRingCat.ofHom (algebraMap R (B ⊗[R] B))) := rfl

/-- **`Spec (B ⊗[R] (B ⊗[R] B))` as the chosen threefold wide pullback** of `Spec B ⟶ Spec R`,
compatible with `Stacks.Descent.specTensorChosenPullback`. -/
def specTensorChosenPullback₃ :
    ChosenPullback₃ (specTensorChosenPullback R B) (specTensorChosenPullback R B)
      (specTensorChosenPullback R B) where
  chosenPullback :=
    { pullback := Spec (CommRingCat.of (B ⊗[R] (B ⊗[R] B)))
      p₁ := Spec.map (tensorMap₀₁ R B)
      p₂ := Spec.map (tensorMap₁₂ R B)
      condition := (isPullback_specTensorMid R B).w
      isLimit := (isPullback_specTensorMid R B).isLimit
      p := Spec.map (tensorIncl₁ R B)
      hp₁ := by
        change Spec.map (tensorMap₀₁ R B) ≫ Spec.map (tensorInr R B) = _
        rw [← Spec.map_comp, tensorInr_comp_tensorMap₀₁] }
  p := Spec.map (CommRingCat.ofHom (algebraMap R (B ⊗[R] (B ⊗[R] B))))
  p₁ := Spec.map (tensorIncl₀ R B)
  p₃ := Spec.map (tensorIncl₂ R B)
  l :=
    { f := Spec.map (tensorMap₀₂ R B)
      f_p₁ := by
        change Spec.map (tensorMap₀₂ R B) ≫ Spec.map (tensorInl R B) = _
        rw [← Spec.map_comp, tensorInl_comp_tensorMap₀₂]
      f_p₂ := by
        change Spec.map (tensorMap₀₂ R B) ≫ Spec.map (tensorInr R B) = _
        rw [← Spec.map_comp, tensorInr_comp_tensorMap₀₂]
      f_p := by
        change Spec.map (tensorMap₀₂ R B) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (B ⊗[R] B))) = _
        rw [← Spec.map_comp, algebraMap_comp_tensorMap₀₂] }
  hp₁ := by
    change Spec.map (tensorMap₀₁ R B) ≫ Spec.map (tensorInl R B) = _
    rw [← Spec.map_comp, tensorInl_comp_tensorMap₀₁]
  hp₃ := by
    change Spec.map (tensorMap₁₂ R B) ≫ Spec.map (tensorInr R B) = _
    rw [← Spec.map_comp, tensorInr_comp_tensorMap₁₂]

end Stacks.Descent

end

end
