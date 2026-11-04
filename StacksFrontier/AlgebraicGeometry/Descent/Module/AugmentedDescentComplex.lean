module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.AmitsurAcyclic
import StacksCore.Tactic.StacksAttribute

/-!
# The augmented descent complex of a ring map

Let `R → A` be a map of commutative rings and let `M` be an `R`-module. The augmented descent
complex of `M` along `R → A` is the cochain complex

`0 → M → A ⊗[R] M → A ⊗[R] A ⊗[R] M → ⋯`,

whose term in degree `n + 1` is `A^{⊗(n + 1)} ⊗[R] M`, whose differential in degree `n + 1` is
the alternating sum of the `n + 2` maps inserting a `1` into one of the `A`-slots, and whose
augmentation in degree zero is `m ↦ 1 ⊗ₜ m`.

The cosimplicial `R`-algebra `(A/R)•` of the section is the Čech conerve of `R → A`, an abstract
wide pushout; this file gives it its concrete description as a tensor power. The degree-`n` part
is `A^{⊗(n + 1)}`, the `i`-th Čech coprojection is the inclusion of the `i`-th tensor slot, and
the `i`-th coface map inserts a `1` into the `i`-th slot. Tensoring with `M` and taking the
alternating sum of the coface maps then produces the complex above.

## Main definitions

* `Stacks.Descent.tensorPowerAlg` is the `(n + 1)`-fold tensor power `A^{⊗(n + 1)}` of `A`
  over `R`, as a commutative `R`-algebra.
* `Stacks.Descent.tensorPowerIncludeLeft`, `Stacks.Descent.tensorPowerIncludeRight` and
  `Stacks.Descent.tensorPowerLMap` are the inclusions of the leading and the non-leading tensor
  factors of `A^{⊗(n + 2)}` and the action of `A ⊗[R] -` on a map of tensor powers.
* `Stacks.Descent.tensorSlot` is the inclusion of the `j`-th tensor slot, and
  `Stacks.Descent.tensorSlotDesc` the algebra map out of a tensor power determined by its
  restrictions to the slots.
* `Stacks.Descent.tensorPowerCechIso` identifies `A^{⊗(n + 1)}` with the degree-`n` part of the
  Čech conerve of `R → A`.
* `Stacks.Descent.tensorInsertOne` is the insertion of a `1` into the `i`-th slot of
  `A^{⊗(n + 1)}`.
* `Stacks.Descent.augmentedAmitsurCosimplicial` is the augmented cosimplicial module
  `(A/R)• ⊗[R] M`.
* `Stacks.Descent.augmentedDescentComplex` is the augmented descent complex itself, and
  `Stacks.Descent.augmentedDescentComplexXIso` identifies its term in degree `n + 1` with
  `A^{⊗(n + 1)} ⊗[R] M`.

## Main results

* `Stacks.Descent.tensorSlot_comp_tensorPowerCechHom`: the `j`-th Čech coprojection of `(A/R)ₙ`
  is the inclusion of the `j`-th tensor slot of `A^{⊗(n + 1)}`.
* `Stacks.Descent.tensorPowerCechIso_hom_comp_map_delta`: the `i`-th coface map of `(A/R)•` is
  the insertion of a `1` into the `i`-th tensor slot.
* `Stacks.Descent.tensorInsertOne_zero`, `Stacks.Descent.tensorInsertOne_zero_one` and
  `Stacks.Descent.tensorInsertOne_succ` compute the insertion maps recursively, so every coface
  map is an explicit map of tensor powers; `Stacks.Descent.tensorInsertOne_zero_apply`,
  `Stacks.Descent.tensorInsertOne_zero_one_apply` and
  `Stacks.Descent.tensorInsertOne_succ_tmul` are the same statements on elements.
* `Stacks.Descent.augmentedDescentComplex_X_zero` and
  `Stacks.Descent.augmentedDescentComplex_X_succ` give the terms of the complex.
* `Stacks.Descent.augmentedDescentComplex_d_zero_one_apply` and
  `Stacks.Descent.augmentedDescentComplex_d_zero_one_eq`: the augmentation is `m ↦ 1 ⊗ₜ m`.
* `Stacks.Descent.augmentedDescentComplex_d_succ_succ` and
  `Stacks.Descent.augmentedDescentComplexXIso_d`: the differential in degree `n + 1` is the
  alternating sum of the `n + 2` slot insertions tensored with the identity of `M`;
  `Stacks.Descent.augmentedDescentComplexXIso_zero_d` is its lowest-degree instance
  `x ⊗ₜ m ↦ 1 ⊗ₜ x ⊗ₜ m - x ⊗ₜ 1 ⊗ₜ m`.

## Implementation notes

The tensor power is formed with the new factor on the left, so that `A^{⊗(n + 2)}` is
`A ⊗[R] A^{⊗(n + 1)}`; this matches the shift isomorphism
`Stacks.Descent.cechShiftIso` of the Čech conerve. Maps out of a tensor power are built with
`Stacks.Descent.tensorSlotDesc` rather than by hand, which turns both the comparison with the
Čech conerve and the slot insertions into one-line consequences of the universal property, and
makes `Stacks.Descent.tensorPowerAlg_hom_ext` the only extensionality principle needed.

The complex is the alternating coface map complex of the Čech conerve tensored with `M`,
augmented by `M` in degree zero along `Mathlib`'s `CochainComplex.augment`; the augmentation
condition is the general fact `AlgebraicTopology.extendedAlternatingCofaceMapComplex`. The ring,
the algebra and the coefficient module therefore live in one universe, unlike
`AlgebraicTopology.amitsurExtendedCochainComplex`, which lifts them into a common universe and
so cannot have `M` itself as its degree-zero term.

## References

* [Stacks Project, Tag 023K](https://stacks.math.columbia.edu/tag/023K)
* [Stacks Project, Tag 023I](https://stacks.math.columbia.edu/tag/023I)
* [Stacks Project, Tag 023J](https://stacks.math.columbia.edu/tag/023J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Arrow
open AlgebraicTopology
open scoped TensorProduct

universe u v

namespace Stacks.Descent

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

/-- The `(n + 1)`-fold tensor power `A ⊗[R] ⋯ ⊗[R] A` of `A` over `R`, as a commutative
`R`-algebra. The new factor is added on the left. -/
noncomputable def tensorPowerAlg : ℕ → CommAlgCat.{u} R
  | 0 => CommAlgCat.of R A
  | n + 1 => CommAlgCat.of R (A ⊗[R] (tensorPowerAlg n : Type u))

/-- The first tensor power of `A` is `A`. -/
lemma tensorPowerAlg_zero : tensorPowerAlg R A 0 = CommAlgCat.of R A :=
  rfl

/-- The `(n + 2)`-fold tensor power of `A` is `A ⊗[R] A^{⊗(n + 1)}`. -/
lemma tensorPowerAlg_succ (n : ℕ) :
    tensorPowerAlg R A (n + 1) = CommAlgCat.of R (A ⊗[R] (tensorPowerAlg R A n : Type u)) :=
  rfl

/-- The inclusion `x ↦ 1 ⊗ₜ x` of `A^{⊗(n + 1)}` into the non-leading tensor factors of
`A^{⊗(n + 2)}`. -/
noncomputable def tensorPowerIncludeRight (n : ℕ) :
    tensorPowerAlg R A n ⟶ tensorPowerAlg R A (n + 1) :=
  CommAlgCat.ofHom Algebra.TensorProduct.includeRight

/-- The inclusion `a ↦ a ⊗ₜ 1` of `A` as the leading tensor factor of `A^{⊗(n + 2)}`. -/
noncomputable def tensorPowerIncludeLeft (n : ℕ) :
    CommAlgCat.of R A ⟶ tensorPowerAlg R A (n + 1) :=
  CommAlgCat.ofHom Algebra.TensorProduct.includeLeft

/-- `A ⊗[R] -` applied to a map of tensor powers: the map of `A^{⊗(n + 2)}` into `A^{⊗(m + 2)}`
fixing the leading tensor factor and acting as `f` on the remaining ones. -/
noncomputable def tensorPowerLMap {n m : ℕ} (f : tensorPowerAlg R A n ⟶ tensorPowerAlg R A m) :
    tensorPowerAlg R A (n + 1) ⟶ tensorPowerAlg R A (m + 1) :=
  CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R A) f.hom)

/-- `tensorPowerIncludeRight` on an element. -/
@[simp]
lemma tensorPowerIncludeRight_apply (n : ℕ) (x : (tensorPowerAlg R A n : Type u)) :
    (tensorPowerIncludeRight R A n).hom x = (1 : A) ⊗ₜ[R] x :=
  rfl

/-- `tensorPowerIncludeLeft` on an element. -/
@[simp]
lemma tensorPowerIncludeLeft_apply (n : ℕ) (a : A) :
    (tensorPowerIncludeLeft R A n).hom a = a ⊗ₜ[R] (1 : (tensorPowerAlg R A n : Type u)) :=
  rfl

/-- `tensorPowerLMap` on a pure tensor. -/
@[simp]
lemma tensorPowerLMap_tmul {n m : ℕ} (f : tensorPowerAlg R A n ⟶ tensorPowerAlg R A m) (a : A)
    (x : (tensorPowerAlg R A n : Type u)) :
    (tensorPowerLMap R A f).hom (a ⊗ₜ[R] x) = a ⊗ₜ[R] f.hom x :=
  rfl

/-- The inclusion of the `j`-th tensor slot `A → A^{⊗(n + 1)}`. -/
noncomputable def tensorSlot : (n : ℕ) → Fin (n + 1) → (CommAlgCat.of R A ⟶ tensorPowerAlg R A n)
  | 0, _ => 𝟙 (CommAlgCat.of R A)
  | n + 1, i =>
      i.cases (tensorPowerIncludeLeft R A n) fun j => tensorSlot n j ≫ tensorPowerIncludeRight R A n

/-- The zeroth slot of `A^{⊗(n + 2)}` is its leading tensor factor. -/
@[simp]
lemma tensorSlot_succ_zero (n : ℕ) :
    tensorSlot R A (n + 1) 0 = tensorPowerIncludeLeft R A n :=
  rfl

/-- The `(j + 1)`-st slot of `A^{⊗(n + 2)}` is the `j`-th slot of `A^{⊗(n + 1)}`, placed in the
non-leading tensor factors. -/
@[simp]
lemma tensorSlot_succ_succ (n : ℕ) (j : Fin (n + 1)) :
    tensorSlot R A (n + 1) j.succ =
      tensorSlot R A n j ≫ tensorPowerIncludeRight R A n :=
  rfl

/-- Precomposing with the only tensor slot of `A^{⊗1}` does nothing. -/
private lemma tensorSlot_zero_comp {T : CommAlgCat.{u} R} (j : Fin 1)
    (g : tensorPowerAlg R A 0 ⟶ T) : tensorSlot R A 0 j ≫ g = g := by
  obtain rfl := Fin.eq_zero j
  exact Category.id_comp g

/-- The algebra map out of `A^{⊗(n + 1)}` determined by its restrictions `f j` to the slots. -/
noncomputable def tensorSlotDesc {T : CommAlgCat.{u} R} :
    (n : ℕ) → (Fin (n + 1) → (CommAlgCat.of R A ⟶ T)) → (tensorPowerAlg R A n ⟶ T)
  | 0, f => f 0
  | n + 1, f =>
      ConcreteCategory.ofHom (Algebra.TensorProduct.lift (f 0).hom
        (tensorSlotDesc n fun j => f j.succ).hom fun _ _ => Commute.all _ _)

/-- Restricting `tensorSlotDesc` to the non-leading tensor factors drops the zeroth slot. -/
@[simp]
lemma tensorPowerIncludeRight_comp_tensorSlotDesc {T : CommAlgCat.{u} R} (n : ℕ)
    (f : Fin (n + 2) → (CommAlgCat.of R A ⟶ T)) :
    tensorPowerIncludeRight R A n ≫ tensorSlotDesc R A (n + 1) f =
      tensorSlotDesc R A n fun j => f j.succ :=
  CommAlgCat.hom_ext
    (Algebra.TensorProduct.lift_comp_includeRight' _ _ fun _ _ => Commute.all _ _)

/-- `tensorSlotDesc` restricts to the given map on each tensor slot. -/
@[simp]
lemma tensorSlot_comp_tensorSlotDesc {T : CommAlgCat.{u} R} :
    ∀ (n : ℕ) (f : Fin (n + 1) → (CommAlgCat.of R A ⟶ T)) (j : Fin (n + 1)),
      tensorSlot R A n j ≫ tensorSlotDesc R A n f = f j
  | 0, f, j => by
      exact (tensorSlot_zero_comp R A j _).trans (by rw [Fin.eq_zero j]; rfl)
  | n + 1, f, j => by
      induction j using Fin.cases with
      | zero =>
        exact CommAlgCat.hom_ext
          (Algebra.TensorProduct.lift_comp_includeLeft _ _ fun _ _ => Commute.all _ _)
      | succ j =>
        rw [tensorSlot_succ_succ, Category.assoc, tensorPowerIncludeRight_comp_tensorSlotDesc,
          tensorSlot_comp_tensorSlotDesc n (fun j => f j.succ) j]

/-- Two algebra maps out of `A^{⊗(n + 1)}` agree as soon as they agree on every tensor slot. -/
lemma tensorPowerAlg_hom_ext {T : CommAlgCat.{u} R} :
    ∀ (n : ℕ) {g₁ g₂ : tensorPowerAlg R A n ⟶ T}
      (_ : ∀ j, tensorSlot R A n j ≫ g₁ = tensorSlot R A n j ≫ g₂), g₁ = g₂
  | 0, g₁, g₂, h => by
      exact (tensorSlot_zero_comp R A 0 g₁).symm.trans ((h 0).trans (tensorSlot_zero_comp R A 0 g₂))
  | n + 1, g₁, g₂, h => by
      have hr : tensorPowerIncludeRight R A n ≫ g₁ = tensorPowerIncludeRight R A n ≫ g₂ := by
        refine tensorPowerAlg_hom_ext n fun j => ?_
        rw [← Category.assoc, ← Category.assoc, ← tensorSlot_succ_succ]
        exact h j.succ
      refine CommAlgCat.hom_ext (Algebra.TensorProduct.ext ?_ ?_)
      · exact congrArg CommAlgCat.Hom.hom (h 0)
      · exact congrArg CommAlgCat.Hom.hom hr

/-- The comparison `A^{⊗(n + 1)} ⟶ (A/R)ₙ` sending the `j`-th tensor slot to the `j`-th Čech
coprojection. -/
noncomputable def tensorPowerCechHom (n : ℕ) :
    tensorPowerAlg R A n ⟶ (algebraArrow R A).cechConerve.obj (.mk n) :=
  tensorSlotDesc R A n fun j => cechι (f := algebraArrow R A) (.mk n) j

/-- `tensorPowerCechHom` sends the `j`-th tensor slot to the `j`-th Čech coprojection. -/
@[simp]
lemma tensorSlot_comp_tensorPowerCechHom (n : ℕ) (j : Fin (n + 1)) :
    tensorSlot R A n j ≫ tensorPowerCechHom R A n = cechι (f := algebraArrow R A) (.mk n) j :=
  tensorSlot_comp_tensorSlotDesc R A n _ j

/-- The comparison `(A/R)ₙ ⟶ A^{⊗(n + 1)}` sending the `j`-th Čech coprojection to the `j`-th
tensor slot. -/
noncomputable def cechTensorPowerHom (n : ℕ) :
    (algebraArrow R A).cechConerve.obj (.mk n) ⟶ tensorPowerAlg R A n :=
  WidePushout.desc (arrows := cechLegs (algebraArrow R A) (.mk n))
    (ConcreteCategory.ofHom (Algebra.ofId R _)) (fun j => tensorSlot R A n j)
    fun _ => algebraArrow_left_hom_ext R A _ _

/-- `cechTensorPowerHom` sends the `j`-th Čech coprojection to the `j`-th tensor slot. -/
@[simp]
lemma cechι_comp_cechTensorPowerHom (n : ℕ) (j : Fin (n + 1)) :
    cechι (f := algebraArrow R A) (.mk n) j ≫ cechTensorPowerHom R A n = tensorSlot R A n j :=
  WidePushout.ι_desc _ _ _ _ j

/-- **The degree-`n` part of the Čech conerve of `R → A` is the `(n + 1)`-fold tensor power of
`A` over `R`**, by the identification of the Čech coprojections with the tensor slots. -/
noncomputable def tensorPowerCechIso (n : ℕ) :
    tensorPowerAlg R A n ≅ (algebraArrow R A).cechConerve.obj (.mk n) where
  hom := tensorPowerCechHom R A n
  inv := cechTensorPowerHom R A n
  hom_inv_id := by
    refine tensorPowerAlg_hom_ext R A n fun j => ?_
    rw [← Category.assoc, tensorSlot_comp_tensorPowerCechHom, cechι_comp_cechTensorPowerHom,
      Category.comp_id]
  inv_hom_id := by
    refine cech_hom_ext (f := algebraArrow R A) fun j => ?_
    rw [← Category.assoc, cechι_comp_cechTensorPowerHom, tensorSlot_comp_tensorPowerCechHom,
      Category.comp_id]

/-- Insertion of a `1` into the `i`-th slot of `A^{⊗(n + 1)}`, the map `A^{⊗(n + 1)} ⟶
A^{⊗(n + 2)}` carrying the `j`-th slot to the `i.succAbove j`-th one. -/
noncomputable def tensorInsertOne (n : ℕ) (i : Fin (n + 2)) :
    tensorPowerAlg R A n ⟶ tensorPowerAlg R A (n + 1) :=
  tensorSlotDesc R A n fun j => tensorSlot R A (n + 1) (i.succAbove j)

/-- Insertion of a `1` into the `i`-th slot skips that slot and shifts the others past it. -/
@[simp]
lemma tensorSlot_comp_tensorInsertOne (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    tensorSlot R A n j ≫ tensorInsertOne R A n i = tensorSlot R A (n + 1) (i.succAbove j) :=
  tensorSlot_comp_tensorSlotDesc R A n _ j

/-- **Inserting a `1` into the zeroth slot is `x ↦ 1 ⊗ₜ x`.** -/
@[simp]
lemma tensorInsertOne_zero (n : ℕ) :
    tensorInsertOne R A n 0 = tensorPowerIncludeRight R A n := by
  refine tensorPowerAlg_hom_ext R A n fun j => ?_
  rw [tensorSlot_comp_tensorInsertOne, Fin.succAbove_zero, tensorSlot_succ_succ]

/-- `tensorPowerLMap` commutes with the inclusion of the non-leading tensor factors. -/
lemma tensorPowerIncludeRight_comp_tensorPowerLMap {n m : ℕ}
    (f : tensorPowerAlg R A n ⟶ tensorPowerAlg R A m) :
    tensorPowerIncludeRight R A n ≫ tensorPowerLMap R A f =
      f ≫ tensorPowerIncludeRight R A m :=
  CommAlgCat.hom_ext (Algebra.TensorProduct.map_comp_includeRight _ _)

/-- `tensorPowerLMap` is the identity on the leading tensor factor. -/
lemma tensorPowerIncludeLeft_comp_tensorPowerLMap {n m : ℕ}
    (f : tensorPowerAlg R A n ⟶ tensorPowerAlg R A m) :
    tensorPowerIncludeLeft R A n ≫ tensorPowerLMap R A f = tensorPowerIncludeLeft R A m :=
  CommAlgCat.hom_ext
    ((Algebra.TensorProduct.map_comp_includeLeft _ _).trans (AlgHom.comp_id _))

/-- **In degree zero, inserting a `1` into the first slot is `a ↦ a ⊗ₜ 1`.** -/
@[simp]
lemma tensorInsertOne_zero_one : tensorInsertOne R A 0 1 = tensorPowerIncludeLeft R A 0 := by
  refine tensorPowerAlg_hom_ext R A 0 fun j => ?_
  obtain rfl := Fin.eq_zero j
  rw [tensorSlot_comp_tensorInsertOne, Fin.one_succAbove_zero, tensorSlot_succ_zero]
  exact (tensorSlot_zero_comp R A 0 _).symm

/-- **Inserting a `1` into the `(i + 1)`-st slot of `A^{⊗(n + 2)}`** fixes the leading tensor
factor and inserts a `1` into the `i`-th slot of the remaining factors. -/
lemma tensorInsertOne_succ (n : ℕ) (i : Fin (n + 2)) :
    tensorInsertOne R A (n + 1) i.succ = tensorPowerLMap R A (tensorInsertOne R A n i) := by
  refine tensorPowerAlg_hom_ext R A (n + 1) fun j => ?_
  rw [tensorSlot_comp_tensorInsertOne]
  induction j using Fin.cases with
  | zero =>
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]), Fin.castSucc_zero,
      tensorSlot_succ_zero, tensorSlot_succ_zero, tensorPowerIncludeLeft_comp_tensorPowerLMap]
  | succ j =>
    rw [Fin.succ_succAbove_succ, tensorSlot_succ_succ, tensorSlot_succ_succ, Category.assoc,
      tensorPowerIncludeRight_comp_tensorPowerLMap, ← Category.assoc,
      tensorSlot_comp_tensorInsertOne]

/-- Inserting a `1` into the zeroth slot, on an element. -/
lemma tensorInsertOne_zero_apply (n : ℕ) (x : (tensorPowerAlg R A n : Type u)) :
    (tensorInsertOne R A n 0).hom x = (1 : A) ⊗ₜ[R] x := by
  rw [tensorInsertOne_zero, tensorPowerIncludeRight_apply]

/-- In degree zero, inserting a `1` into the first slot, on an element. -/
lemma tensorInsertOne_zero_one_apply (x : (tensorPowerAlg R A 0 : Type u)) :
    (tensorInsertOne R A 0 1).hom x = x ⊗ₜ[R] (1 : (tensorPowerAlg R A 0 : Type u)) := by
  rw [tensorInsertOne_zero_one]
  rfl

/-- Inserting a `1` into the `(i + 1)`-st slot, on a pure tensor. -/
lemma tensorInsertOne_succ_tmul (n : ℕ) (i : Fin (n + 2)) (a : A)
    (x : (tensorPowerAlg R A n : Type u)) :
    (tensorInsertOne R A (n + 1) i.succ).hom (a ⊗ₜ[R] x) =
      a ⊗ₜ[R] (tensorInsertOne R A n i).hom x := by
  rw [tensorInsertOne_succ, tensorPowerLMap_tmul]

/-- **The coface maps of `(A/R)•` insert a `1`.** Under the identification of the Čech conerve
with the tensor powers of `A`, the `i`-th coface map `(A/R)ₙ → (A/R)_{n + 1}` is the insertion of
a `1` into the `i`-th tensor slot. -/
theorem tensorPowerCechIso_hom_comp_map_delta (n : ℕ) (i : Fin (n + 2)) :
    (tensorPowerCechIso R A n).hom ≫
        (algebraArrow R A).cechConerve.map (SimplexCategory.δ i) =
      tensorInsertOne R A n i ≫ (tensorPowerCechIso R A (n + 1)).hom := by
  refine tensorPowerAlg_hom_ext R A n fun j => ?_
  have hδ : (SimplexCategory.δ i).toOrderHom j = i.succAbove j := rfl
  rw [← Category.assoc, ← Category.assoc]
  change tensorSlot R A n j ≫ tensorPowerCechHom R A n ≫ _ =
    (tensorSlot R A n j ≫ tensorInsertOne R A n i) ≫ tensorPowerCechHom R A (n + 1)
  rw [← Category.assoc, tensorSlot_comp_tensorPowerCechHom, cechι_comp_map, hδ,
    tensorSlot_comp_tensorInsertOne, tensorSlot_comp_tensorPowerCechHom]

variable (M : Type (max u v)) [AddCommGroup M] [Module R M]

/-- The augmented cosimplicial `R`-module `(A/R)• ⊗[R] M` of Lemma 023I: the Čech conerve of
`R → A`, augmented by `R` and tensored with the coefficient module. -/
noncomputable def augmentedAmitsurCosimplicial :
    CosimplicialObject.Augmented (ModuleCat.{max u v} R) :=
  (CosimplicialObject.Augmented.whiskeringObj _ _ (tensorModuleFunctor R M)).obj
    (algebraArrow R A).augmentedCechConerve

/-- **Equation 023K: the augmented descent complex** `0 → M → A ⊗[R] M → A ⊗[R] A ⊗[R] M → ⋯`
of the ring map `R → A` with coefficients in `M`. It is the alternating coface map complex of
`(A/R)• ⊗[R] M`, augmented by `M` along `m ↦ 1 ⊗ₜ m`. -/
@[stacks 023K "the augmented complex 0 → M → A ⊗ M → A ⊗ A ⊗ M → ⋯"]
noncomputable def augmentedDescentComplex : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  extendedAlternatingCofaceMapComplex (augmentedAmitsurCosimplicial R A M) (ModuleCat.of R M)
    (ModuleCat.ofHom (TensorProduct.lid R M).symm.toLinearMap)

/-- The degree-zero term of the augmented descent complex is the coefficient module. -/
@[simp]
lemma augmentedDescentComplex_X_zero :
    (augmentedDescentComplex R A M).X 0 = ModuleCat.of R M :=
  rfl

/-- The degree-`(n + 1)` term of the augmented descent complex is `(A/R)ₙ ⊗[R] M`. -/
@[simp]
lemma augmentedDescentComplex_X_succ (n : ℕ) :
    (augmentedDescentComplex R A M).X (n + 1) =
      ModuleCat.of R (((algebraArrow R A).cechConerve.obj (.mk n) : Type u) ⊗[R] M) :=
  rfl

/-- **The degree-`(n + 1)` term of the augmented descent complex is `A^{⊗(n + 1)} ⊗[R] M`.** -/
@[stacks 023K "its degree-(n+1) term is A^{⊗(n+1)} ⊗_R M"]
noncomputable def augmentedDescentComplexXIso (n : ℕ) :
    ModuleCat.of R ((tensorPowerAlg R A n : Type u) ⊗[R] M) ≅
      (augmentedDescentComplex R A M).X (n + 1) :=
  (tensorModuleFunctor R M).mapIso (tensorPowerCechIso R A n)

/-- `augmentedDescentComplexXIso` acts on a pure tensor through the comparison of `A^{⊗(n + 1)}`
with the degree-`n` part of the Čech conerve. -/
lemma augmentedDescentComplexXIso_hom_tmul (n : ℕ) (x : (tensorPowerAlg R A n : Type u)) (m : M) :
    (augmentedDescentComplexXIso R A M n).hom (x ⊗ₜ[R] m) =
      (tensorPowerCechHom R A n).hom x ⊗ₜ[R] m :=
  rfl

/-- The augmentation of the augmented descent complex is `m ↦ 1 ⊗ₜ m`. -/
lemma augmentedDescentComplex_d_zero_one_apply (m : M) :
    (augmentedDescentComplex R A M).d 0 1 m =
      (1 : ((algebraArrow R A).cechConerve.obj (.mk 0) : Type u)) ⊗ₜ[R] m := by
  change (cechHead (f := algebraArrow R A) (.mk 0)).hom 1 ⊗ₜ[R] m = _
  rw [map_one]

/-- The identification of the degree-`(n + 1)` term with `A^{⊗(n + 1)} ⊗[R] M` matches the
elements `1 ⊗ₜ m`. -/
lemma augmentedDescentComplexXIso_hom_one_tmul (n : ℕ) (m : M) :
    (augmentedDescentComplexXIso R A M n).hom ((1 : (tensorPowerAlg R A n : Type u)) ⊗ₜ[R] m) =
      (1 : ((algebraArrow R A).cechConerve.obj (.mk n) : Type u)) ⊗ₜ[R] m := by
  rw [augmentedDescentComplexXIso_hom_tmul, map_one]

/-- **The augmentation of the augmented descent complex is `m ↦ 1 ⊗ₜ m`**, read in the
identification of the degree-one term with `A ⊗[R] M`. -/
lemma augmentedDescentComplex_d_zero_one_eq (m : M) :
    (augmentedDescentComplex R A M).d 0 1 m =
      (augmentedDescentComplexXIso R A M 0).hom
        ((1 : (tensorPowerAlg R A 0 : Type u)) ⊗ₜ[R] m) :=
  (augmentedDescentComplex_d_zero_one_apply R A M m).trans
    (augmentedDescentComplexXIso_hom_one_tmul R A M 0 m).symm

/-- Away from the augmentation, the differential of the augmented descent complex is the
alternating sum of the coface maps of `(A/R)• ⊗[R] M`. -/
lemma augmentedDescentComplex_d_succ_succ (n : ℕ) :
    (augmentedDescentComplex R A M).d (n + 1) (n + 2) =
      AlternatingCofaceMapComplex.objD (amitsurCosimplicial R A M) n :=
  extendedAlternatingCofaceMapComplex_d_succ_succ _ _ _ n

/-- The identification of the terms with tensor powers carries the `i`-th coface map of
`(A/R)• ⊗[R] M` to the insertion of a `1` into the `i`-th tensor slot. -/
lemma tensorModuleFunctor_map_comp_delta (n : ℕ) (i : Fin (n + 2)) :
    (tensorModuleFunctor R M).map (tensorPowerCechHom R A n) ≫
        (amitsurCosimplicial R A M).δ i =
      (tensorModuleFunctor R M).map (tensorInsertOne R A n i) ≫
        (tensorModuleFunctor R M).map (tensorPowerCechHom R A (n + 1)) := by
  have hδ : (amitsurCosimplicial R A M).δ i =
      (tensorModuleFunctor R M).map ((algebraArrow R A).cechConerve.map (SimplexCategory.δ i)) :=
    rfl
  rw [hδ, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (tensorModuleFunctor R M).map (tensorPowerCechIso_hom_comp_map_delta R A n i)

/-- The identification of the terms with tensor powers carries the alternating sum of the coface
maps of `(A/R)• ⊗[R] M` to the alternating sum of the slot insertions. -/
lemma tensorModuleFunctor_map_comp_objD (n : ℕ) :
    (tensorModuleFunctor R M).map (tensorPowerCechHom R A n) ≫
        AlternatingCofaceMapComplex.objD (amitsurCosimplicial R A M) n =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (tensorModuleFunctor R M).map (tensorInsertOne R A n i)) ≫
        (tensorModuleFunctor R M).map (tensorPowerCechHom R A (n + 1)) := by
  rw [AlternatingCofaceMapComplex.objD, Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, tensorModuleFunctor_map_comp_delta]

/-- **The differential of the augmented descent complex is the alternating sum of the slot
insertions.** In degree `n + 1` it is, under the identification of the terms with
`A^{⊗(n + 1)} ⊗[R] M`, the sum `∑ (-1) ^ i (insert 1 in slot i) ⊗ 1`. -/
theorem augmentedDescentComplexXIso_d (n : ℕ) :
    (augmentedDescentComplexXIso R A M n).hom ≫ (augmentedDescentComplex R A M).d (n + 1) (n + 2) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (tensorModuleFunctor R M).map (tensorInsertOne R A n i)) ≫
        (augmentedDescentComplexXIso R A M (n + 1)).hom :=
  (congrArg ((augmentedDescentComplexXIso R A M n).hom ≫ ·)
    (augmentedDescentComplex_d_succ_succ R A M n)).trans
      (tensorModuleFunctor_map_comp_objD R A M n)

/-- **In the lowest degree the differential is the Amitsur differential.** Under the
identification of the terms with tensor powers, the map `A ⊗[R] M → A ⊗[R] A ⊗[R] M` is the
difference of the two slot insertions, `x ⊗ₜ m ↦ 1 ⊗ₜ x ⊗ₜ m - x ⊗ₜ 1 ⊗ₜ m`. -/
lemma augmentedDescentComplexXIso_zero_d :
    (augmentedDescentComplexXIso R A M 0).hom ≫ (augmentedDescentComplex R A M).d 1 2 =
      ((tensorModuleFunctor R M).map (tensorInsertOne R A 0 0) -
          (tensorModuleFunctor R M).map (tensorInsertOne R A 0 1)) ≫
        (augmentedDescentComplexXIso R A M 1).hom := by
  refine (augmentedDescentComplexXIso_d R A M 0).trans ?_
  congr 1
  rw [Fin.sum_univ_two]
  simp [sub_eq_add_neg]

end Stacks.Descent

end
