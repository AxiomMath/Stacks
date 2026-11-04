module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization

/-!
# The cohomology product of a derived tensor product, in a monoidal abelian category

Let `A` be an abelian category with an additive monoidal structure for which the total tensor
complex of two cochain complexes exists, so that `Comp(A)` is monoidal.  For two cochain
complexes `P` and `Q` of objects of `A`, tensoring cocycle representatives gives a map

`Hⁱ(P) ⊗ Hʲ(Q) ⟶ Hⁱ⁺ʲ(P ⊗ Q)`,

and if moreover every cochain complex receives a quasi-isomorphism from a K-flat one, so that
`D(A)` is monoidal under the derived tensor product
(`CochainComplex.KFlatMonoidal.derivedMonoidal`), the same construction gives the Künneth map

`Hⁱ(K) ⊗ Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗ᴸ L)`

for two arbitrary objects `K` and `L` of `D(A)`.

## Main definitions

* `CochainComplex.KFlatMonoidal.tensorCycles`: the tensor product of two cocycles is a cocycle
  in the total tensor complex.
* `CochainComplex.KFlatMonoidal.tensorHomology`: **the cohomology product of two cochain
  complexes**, `Hⁱ(P) ⊗ Hʲ(Q) ⟶ Hⁱ⁺ʲ(P ⊗ Q)`.
* `CochainComplex.KFlatMonoidal.CohomologyTensorProduct`: the Künneth map on `D(A)` together
  with K-flat representatives on which it is induced by `tensorCycles`.
* `CochainComplex.KFlatMonoidal.cohomologyTensorProduct`: **the Künneth map on `D(A)`**.

## Main results

* `CochainComplex.KFlatMonoidal.homologyπ_tensorHomology`: `tensorHomology` is the map induced
  by `tensorCycles` on cohomology classes.  This is the defining property: `tensorHomology` is
  the unique map through which `[p] ⊗ [q] ↦ [p ⊗ q]` factors, since the tensor product of the
  two projections to cohomology is an epimorphism
  (`CochainComplex.KFlatMonoidal.epi_homologyπ_tensor`).
* `CochainComplex.KFlatMonoidal.tensorCycles_naturality` and
  `CochainComplex.KFlatMonoidal.tensorHomology_naturality`: the cocycle tensor and the
  cohomology product are natural in both complexes.
* `CochainComplex.KFlatMonoidal.cohomologyTensorProduct_map_cocycles`: the cocycle formula for
  the Künneth map on `D(A)`, on the K-flat representatives it was built from.

## Implementation notes

`tensorHomology` is obtained from Mathlib's `CategoryTheory.Limits.CokernelCofork.isColimitTensor`:
`Hⁱ(P)` is the cokernel of `Pⁱ⁻¹ ⟶ Zⁱ(P)`, and the tensor product of two cokernels is a
cokernel as soon as tensoring preserves the relevant colimits.  That is where the
`PreservesFiniteColimits` hypothesis comes from; it is asked for on the left only, since on the
right it follows from the braiding by
`CochainComplex.KFlatMonoidal.preservesFiniteColimitsTensorRight`.  No element-level computation
is performed, so nothing here is specific to modules.

The sign in `tensorCycles_right_boundary` is the Koszul sign `ComplexShape.ε₂` of the total
complex; it is a unit, so it does not affect the vanishing, but it has to be carried through
`tensor_right_boundary_d` explicitly because the differential of the total complex is a sum of
two terms, only the second of which is signed.

For the derived statement, the choice of K-flat representatives is made once, by
`Classical.choose`, and recorded in the `maps_cocycles` field.  This is a sufficient instance of
the source's construction, which requires only one factor to be K-flat; the statement makes one
such choice and does not assert coherence across all choices.  Both halves — the map and the
cocycle formula — are packaged into `CohomologyTensorProduct` so that the map is never available
without the formula that pins it down.

## References

* [The Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Category
open CochainComplex.KFlatBifunctor

universe w v u

namespace CochainComplex.KFlatMonoidal

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [MonoidalPreadditive A]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-! ### The tensor product of two cocycles -/

section Cycles

omit [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- The tensor product of a cocycle in degree `i` and a cocycle in degree `j` is annihilated by
the differential of the total tensor complex in degree `i + j`. -/
lemma tensor_cycles_comp_d (P Q : CochainComplex A ℤ) (i j : ℤ) :
    ((P.iCycles i ⊗ₘ Q.iCycles j) ≫
        HomologicalComplex.ιTensorObj P Q i j (i + j) rfl) ≫
      (P ⊗ Q).d (i + j) (i + j + 1) = 0 := by
  show ((P.iCycles i ⊗ₘ Q.iCycles j) ≫
    HomologicalComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _) (ComplexShape.up ℤ)
      i j (i + j) rfl) ≫
    (HomologicalComplex.mapBifunctor P Q (MonoidalCategory.curriedTensor _)
      (ComplexShape.up ℤ)).d (i + j) (i + j + 1) = 0
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add]
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq P Q (MonoidalCategory.curriedTensor _) _
    (show (ComplexShape.up ℤ).Rel i (i + 1) by simp) j (i + j + 1)
    (by show i + 1 + j = i + j + 1; omega),
    HomologicalComplex.mapBifunctor.d₂_eq P Q (MonoidalCategory.curriedTensor _) _
    i (show (ComplexShape.up ℤ).Rel j (j + 1) by simp) (i + j + 1)
    (by show i + (j + 1) = i + j + 1; omega)]
  simp [tensorHom_def, whisker_exchange_assoc, ← comp_whiskerRight_assoc,
    ← whiskerLeft_comp_assoc]

/-- **The tensor product of two cocycles is a cocycle**: the map
`Zⁱ(P) ⊗ Zʲ(Q) ⟶ Zⁱ⁺ʲ(P ⊗ Q)` induced by the inclusion of the tensor factor of degree
`(i, j)` into the total tensor complex. -/
def tensorCycles (P Q : CochainComplex A ℤ) (i j : ℤ) :
    P.cycles i ⊗ Q.cycles j ⟶ (P ⊗ Q).cycles (i + j) :=
  (P ⊗ Q).liftCycles
    ((P.iCycles i ⊗ₘ Q.iCycles j) ≫
      HomologicalComplex.ιTensorObj P Q i j (i + j) rfl)
    (i + j + 1) (by simp) (tensor_cycles_comp_d P Q i j)

omit [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- `CochainComplex.KFlatMonoidal.tensorCycles`, composed with the inclusion of the cocycles,
is the tensor product of the two inclusions followed by the inclusion of the tensor factor. -/
@[simp]
lemma tensorCycles_i (P Q : CochainComplex A ℤ) (i j : ℤ) :
    tensorCycles P Q i j ≫ (P ⊗ Q).iCycles (i + j) =
      (P.iCycles i ⊗ₘ Q.iCycles j) ≫
        HomologicalComplex.ιTensorObj P Q i j (i + j) rfl :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

omit [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- The differential of the total tensor complex, applied to the tensor factor of degree
`(i - 1, j)`, is the differential of the first factor: in this corner the Koszul sign is
trivial. -/
lemma tensor_left_boundary_d (P Q : CochainComplex A ℤ) (i j : ℤ) :
    ((𝟙 (P.X (i - 1)) ⊗ₘ Q.iCycles j) ≫
        HomologicalComplex.ιTensorObj P Q (i - 1) j (i + j - 1) (by omega)) ≫
      (P ⊗ Q).d (i + j - 1) (i + j) =
    (P.d (i - 1) i ⊗ₘ Q.iCycles j) ≫
      HomologicalComplex.ιTensorObj P Q i j (i + j) rfl := by
  show ((𝟙 (P.X (i - 1)) ⊗ₘ Q.iCycles j) ≫
      HomologicalComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _)
        (ComplexShape.up ℤ) (i - 1) j (i + j - 1) (by dsimp; omega)) ≫
    (HomologicalComplex.mapBifunctor P Q (MonoidalCategory.curriedTensor _)
      (ComplexShape.up ℤ)).d (i + j - 1) (i + j) = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add]
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq P Q (MonoidalCategory.curriedTensor _) _
    (show (ComplexShape.up ℤ).Rel (i - 1) i by simp) j (i + j)
    (by show i + j = i + j; rfl),
    HomologicalComplex.mapBifunctor.d₂_eq P Q (MonoidalCategory.curriedTensor _) _
    (i - 1) (show (ComplexShape.up ℤ).Rel j (j + 1) by simp) (i + j)
    (by show i - 1 + (j + 1) = i + j; omega)]
  simp [tensorHom_def, whisker_exchange_assoc, ← whiskerLeft_comp_assoc]

omit [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- **A coboundary in the first factor tensored with a cocycle is a coboundary.** -/
lemma tensorCycles_left_boundary (P Q : CochainComplex A ℤ) (i j : ℤ) :
    (P.toCycles (i - 1) i ⊗ₘ 𝟙 (Q.cycles j)) ≫
      tensorCycles P Q i j ≫ (P ⊗ Q).homologyπ (i + j) = 0 := by
  let x : P.X (i - 1) ⊗ Q.cycles j ⟶ (P ⊗ Q).X (i + j - 1) :=
    (𝟙 (P.X (i - 1)) ⊗ₘ Q.iCycles j) ≫
      HomologicalComplex.ιTensorObj P Q (i - 1) j (i + j - 1) (by omega)
  have h : (P.toCycles (i - 1) i ⊗ₘ 𝟙 (Q.cycles j)) ≫
      tensorCycles P Q i j =
      x ≫ (P ⊗ Q).toCycles (i + j - 1) (i + j) := by
    rw [← cancel_mono ((P ⊗ Q).iCycles (i + j))]
    simp only [Category.assoc, tensorCycles_i, HomologicalComplex.toCycles_i]
    show (P.toCycles (i - 1) i ⊗ₘ 𝟙 (Q.cycles j)) ≫
      (P.iCycles i ⊗ₘ Q.iCycles j) ≫
        HomologicalComplex.ιTensorObj P Q i j (i + j) rfl =
      x ≫ (P ⊗ Q).d (i + j - 1) (i + j)
    rw [tensor_left_boundary_d]
    simp [tensorHom_def, ← comp_whiskerRight_assoc]
  rw [← Category.assoc, h, Category.assoc,
    HomologicalComplex.toCycles_comp_homologyπ, Limits.comp_zero]

omit [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- The differential of the total tensor complex, applied to the tensor factor of degree
`(i, j - 1)`, is the differential of the second factor up to the Koszul sign. -/
lemma tensor_right_boundary_d (P Q : CochainComplex A ℤ) (i j : ℤ) :
    ((P.iCycles i ⊗ₘ 𝟙 (Q.X (j - 1))) ≫
        HomologicalComplex.ιTensorObj P Q i (j - 1) (i + j - 1) (by omega)) ≫
      (P ⊗ Q).d (i + j - 1) (i + j) =
    ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      ⟨i, j - 1⟩ •
      ((P.iCycles i ⊗ₘ Q.d (j - 1) j) ≫
        HomologicalComplex.ιTensorObj P Q i j (i + j) rfl) := by
  show ((P.iCycles i ⊗ₘ 𝟙 (Q.X (j - 1))) ≫
      HomologicalComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _)
        (ComplexShape.up ℤ) i (j - 1) (i + j - 1) (by dsimp; omega)) ≫
    (HomologicalComplex.mapBifunctor P Q (MonoidalCategory.curriedTensor _)
      (ComplexShape.up ℤ)).d (i + j - 1) (i + j) = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add]
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq P Q (MonoidalCategory.curriedTensor _) _
    (show (ComplexShape.up ℤ).Rel i (i + 1) by simp) (j - 1) (i + j)
    (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq P Q (MonoidalCategory.curriedTensor _) _
    i (show (ComplexShape.up ℤ).Rel (j - 1) j by simp) (i + j)
    (by dsimp)]
  simp [tensorHom_def, ← comp_whiskerRight_assoc,
    Linear.comp_units_smul]

omit [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- **A cocycle tensored with a coboundary in the second factor is a coboundary.** -/
lemma tensorCycles_right_boundary (P Q : CochainComplex A ℤ) (i j : ℤ) :
    (𝟙 (P.cycles i) ⊗ₘ Q.toCycles (j - 1) j) ≫
      tensorCycles P Q i j ≫ (P ⊗ Q).homologyπ (i + j) = 0 := by
  let ε : ℤˣ := ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) ⟨i, j - 1⟩
  let x : P.cycles i ⊗ Q.X (j - 1) ⟶ (P ⊗ Q).X (i + j - 1) :=
    ε • ((P.iCycles i ⊗ₘ 𝟙 (Q.X (j - 1))) ≫
      HomologicalComplex.ιTensorObj P Q i (j - 1) (i + j - 1) (by omega))
  have h : (𝟙 (P.cycles i) ⊗ₘ Q.toCycles (j - 1) j) ≫
      tensorCycles P Q i j =
      x ≫ (P ⊗ Q).toCycles (i + j - 1) (i + j) := by
    rw [← cancel_mono ((P ⊗ Q).iCycles (i + j))]
    simp only [Category.assoc, tensorCycles_i, HomologicalComplex.toCycles_i]
    show (𝟙 (P.cycles i) ⊗ₘ Q.toCycles (j - 1) j) ≫
      (P.iCycles i ⊗ₘ Q.iCycles j) ≫
        HomologicalComplex.ιTensorObj P Q i j (i + j) rfl =
      (ε • ((P.iCycles i ⊗ₘ 𝟙 (Q.X (j - 1))) ≫
        HomologicalComplex.ιTensorObj P Q i (j - 1) (i + j - 1) (by omega))) ≫
          (P ⊗ Q).d (i + j - 1) (i + j)
    rw [Linear.units_smul_comp, tensor_right_boundary_d, smul_smul,
      Int.units_mul_self, one_smul]
    simp only [← Category.assoc, tensorHom_comp_tensorHom,
      Category.id_comp, HomologicalComplex.toCycles_i]
  rw [← Category.assoc, h, Category.assoc,
    HomologicalComplex.toCycles_comp_homologyπ, Limits.comp_zero]

omit [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- **The tensor product of two cocycles is natural in both complexes.** -/
lemma tensorCycles_naturality {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q')
    (i j : ℤ) :
    (HomologicalComplex.cyclesMap f i ⊗ₘ HomologicalComplex.cyclesMap g j) ≫
        tensorCycles P' Q' i j =
      tensorCycles P Q i j ≫ HomologicalComplex.cyclesMap (f ⊗ₘ g) (i + j) := by
  rw [← cancel_mono ((P' ⊗ Q').iCycles (i + j))]
  simp only [Category.assoc, tensorCycles_i]
  rw [← Category.assoc, tensorHom_comp_tensorHom,
    HomologicalComplex.cyclesMap_i, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.cyclesMap_i, ← Category.assoc (tensorCycles P Q i j),
    tensorCycles_i]
  show ((P.iCycles i ≫ f.f i) ⊗ₘ (Q.iCycles j ≫ g.f j)) ≫
      HomologicalComplex.ιMapBifunctor P' Q' (MonoidalCategory.curriedTensor _)
        (ComplexShape.up ℤ) i j (i + j) rfl =
    ((P.iCycles i ⊗ₘ Q.iCycles j) ≫
      HomologicalComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _)
        (ComplexShape.up ℤ) i j (i + j) rfl) ≫
      (HomologicalComplex.mapBifunctorMap f g (MonoidalCategory.curriedTensor _)
        (ComplexShape.up ℤ)).f (i + j)
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp [tensorHom_def, whisker_exchange_assoc]

end Cycles

/-! ### The cohomology product of two cochain complexes -/

section Homology

variable [BraidedCategory A] [∀ X : A, PreservesFiniteColimits (tensorLeft X)]

omit [Abelian A] [MonoidalPreadditive A]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] in
/-- **In a braided category, tensoring on the right preserves whatever colimits tensoring on the
left preserves**: the braiding is a natural isomorphism `X ⊗ - ≅ - ⊗ X`.  Seated as a local
instance, so that a consumer of this file has only to supply the left-hand hypothesis. -/
theorem preservesFiniteColimitsTensorRight (X : A) :
    PreservesFiniteColimits (tensorRight X) :=
  preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

attribute [local instance] preservesFiniteColimitsTensorRight

/-- **The cohomology product of two cochain complexes**, `Hⁱ(P) ⊗ Hʲ(Q) ⟶ Hⁱ⁺ʲ(P ⊗ Q)`.

`Hⁱ(P)` is the cokernel of `Pⁱ⁻¹ ⟶ Zⁱ(P)` and `Hʲ(Q)` the cokernel of `Qʲ⁻¹ ⟶ Zʲ(Q)`, so their
tensor product is again a cokernel; the product is the map out of it induced by
`CochainComplex.KFlatMonoidal.tensorCycles`, which kills both coboundaries by
`tensorCycles_left_boundary` and `tensorCycles_right_boundary`. -/
def tensorHomology (P Q : CochainComplex A ℤ) (i j : ℤ) :
    P.homology i ⊗ Q.homology j ⟶ (P ⊗ Q).homology (i + j) := by
  let k := tensorCycles P Q i j ≫ (P ⊗ Q).homologyπ (i + j)
  have hk : Limits.coprod.desc (P.toCycles (i - 1) i ▷ Q.cycles j)
        (P.cycles i ◁ Q.toCycles (j - 1) j) ≫ k = 0 := by
    apply Limits.coprod.hom_ext
    · simp [k, ← tensorHom_id, tensorCycles_left_boundary,
        Limits.coprod.inl_desc]
    · simp [k, ← id_tensorHom, tensorCycles_right_boundary,
        Limits.coprod.inr_desc]
  exact (Limits.CokernelCofork.isColimitTensor
    (P.homologyIsCokernel (i - 1) i (by simp))
    (Q.homologyIsCokernel (j - 1) j (by simp))).desc
      (Limits.CokernelCofork.ofπ k hk)

omit [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- **The cohomology product is the map induced by tensoring cocycles**: the tensor product of
the two projections to cohomology, followed by the product, is `tensorCycles` followed by the
projection to cohomology.

This is the defining property of `CochainComplex.KFlatMonoidal.tensorHomology`; since the
tensor product of the two projections is an epimorphism, it determines the product. -/
lemma homologyπ_tensorHomology (P Q : CochainComplex A ℤ) (i j : ℤ) :
    (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫ tensorHomology P Q i j =
      tensorCycles P Q i j ≫ (P ⊗ Q).homologyπ (i + j) := by
  unfold tensorHomology
  exact Limits.Cofork.IsColimit.π_desc
    (hs := Limits.CokernelCofork.isColimitTensor
      (P.homologyIsCokernel (i - 1) i (by simp))
      (Q.homologyIsCokernel (j - 1) j (by simp)))

omit [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] in
/-- **The tensor product of the two projections to cohomology is an epimorphism**: it is the
cokernel projection of the tensor of the two cokernel coforks, which is a colimit cofork by
`CategoryTheory.Limits.CokernelCofork.isColimitTensor`.

This is what makes `CochainComplex.KFlatMonoidal.homologyπ_tensorHomology` a characterisation of
the cohomology product and not merely a property of it. -/
lemma epi_homologyπ_tensor (P Q : CochainComplex A ℤ) (i j : ℤ) :
    Epi (P.homologyπ i ⊗ₘ Q.homologyπ j) :=
  Limits.epi_of_isColimit_cofork (Limits.CokernelCofork.isColimitTensor
    (P.homologyIsCokernel (i - 1) i (by simp))
    (Q.homologyIsCokernel (j - 1) j (by simp)))

omit [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- **The cohomology product is natural in both complexes.** -/
lemma tensorHomology_naturality {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q')
    (i j : ℤ) :
    (HomologicalComplex.homologyMap f i ⊗ₘ HomologicalComplex.homologyMap g j) ≫
        tensorHomology P' Q' i j =
      tensorHomology P Q i j ≫ HomologicalComplex.homologyMap (f ⊗ₘ g) (i + j) := by
  have := epi_homologyπ_tensor P Q i j
  rw [← cancel_epi (P.homologyπ i ⊗ₘ Q.homologyπ j)]
  calc (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫
        (HomologicalComplex.homologyMap f i ⊗ₘ HomologicalComplex.homologyMap g j) ≫
          tensorHomology P' Q' i j
      = (HomologicalComplex.cyclesMap f i ⊗ₘ HomologicalComplex.cyclesMap g j) ≫
          (P'.homologyπ i ⊗ₘ Q'.homologyπ j) ≫ tensorHomology P' Q' i j := by
        rw [← Category.assoc, tensorHom_comp_tensorHom,
          HomologicalComplex.homologyπ_naturality, HomologicalComplex.homologyπ_naturality,
          ← tensorHom_comp_tensorHom, Category.assoc]
    _ = tensorCycles P Q i j ≫ HomologicalComplex.cyclesMap (f ⊗ₘ g) (i + j) ≫
          (P' ⊗ Q').homologyπ (i + j) := by
        rw [homologyπ_tensorHomology, ← Category.assoc, tensorCycles_naturality,
          Category.assoc]
    _ = tensorCycles P Q i j ≫ (P ⊗ Q).homologyπ (i + j) ≫
          HomologicalComplex.homologyMap (f ⊗ₘ g) (i + j) := by
        rw [HomologicalComplex.homologyπ_naturality]
    _ = (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫ tensorHomology P Q i j ≫
          HomologicalComplex.homologyMap (f ⊗ₘ g) (i + j) := by
        rw [← Category.assoc (P.homologyπ i ⊗ₘ Q.homologyπ j), homologyπ_tensorHomology,
          Category.assoc]

end Homology

/-! ### The Künneth map on the derived category -/

section Derived

variable (A)
variable [HasDerivedCategory.{w} A] [MonoidalCategory (DerivedCategory A)]

/-- Comparison data for a monoidal structure on `D(A)`: on K-flat complexes its tensor product
is the image of the total tensor complex.  This is what makes the structure the *derived* tensor
product, and `CochainComplex.KFlatMonoidal.derivedTensorIso` supplies it for
`CochainComplex.KFlatMonoidal.derivedMonoidal`. -/
abbrev KFlatComparison :=
  ∀ (P Q : CochainComplex A ℤ), KFlat (curriedTensor A) P → KFlat (curriedTensor A) Q →
    (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q ≅ DerivedCategory.Q.obj (P ⊗ Q))

omit [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [MonoidalCategory (DerivedCategory A)] in
/-- Every object of `D(A)` is isomorphic to the image of a K-flat cochain complex: any complex
representing it receives a quasi-isomorphism from a K-flat one, which becomes invertible in the
derived category. -/
theorem exists_kFlat_representative
    (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlat (curriedTensor A) P ∧ QuasiIso f)
    (X : DerivedCategory A) :
    ∃ P : CochainComplex A ℤ,
      KFlat (curriedTensor A) P ∧ Nonempty (DerivedCategory.Q.obj P ≅ X) := by
  obtain ⟨P, f, hP, _⟩ := hres (DerivedCategory.Q.objPreimage X)
  exact ⟨P, hP,
    ⟨asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso X⟩⟩

variable (cmp : KFlatComparison A)

/-- A Künneth map `Hⁱ(K) ⊗ Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗ᴸ L)` on `D(A)`, together with K-flat
representatives on which it is induced by tensoring cocycles: it sends the tensor of the classes
of two cocycles to the class of their tensor.

The second field is the formula `[p] ⊗ [q] ↦ [p ⊗ q]`, transcribed through the two
identifications it needs — `DerivedCategory.homologyFunctorFactors`, which computes the
cohomology of the image of a complex, and the comparison `cmp`, which identifies the derived
tensor product of two K-flat complexes with their total tensor complex. -/
structure CohomologyTensorProduct (K L : DerivedCategory A) (i j : ℤ) where
  /-- The Künneth map on cohomology. -/
  map :
    (DerivedCategory.homologyFunctor A i).obj K ⊗ (DerivedCategory.homologyFunctor A j).obj L ⟶
      (DerivedCategory.homologyFunctor A (i + j)).obj (K ⊗ L)
  /-- There are K-flat representatives for which `map` is induced by tensoring cocycles. -/
  maps_cocycles :
    ∃ (P Q : CochainComplex A ℤ)
      (hP : KFlat (curriedTensor A) P) (hQ : KFlat (curriedTensor A) Q)
      (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L)
      (z : P.cycles i ⊗ Q.cycles j ⟶ (P ⊗ Q).cycles (i + j)),
      z ≫ (P ⊗ Q).iCycles (i + j) =
          (P.iCycles i ⊗ₘ Q.iCycles j) ≫
            HomologicalComplex.ιTensorObj P Q i j (i + j) rfl ∧
        (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫
              ((DerivedCategory.homologyFunctorFactors A i).inv.app P ⊗ₘ
                (DerivedCategory.homologyFunctorFactors A j).inv.app Q) ≫
              ((DerivedCategory.homologyFunctor A i).map eP.hom ⊗ₘ
                (DerivedCategory.homologyFunctor A j).map eQ.hom) ≫
              map ≫
              (DerivedCategory.homologyFunctor A (i + j)).map
                ((eP.inv ⊗ₘ eQ.inv) ≫ (cmp P Q hP hQ).hom) ≫
              (DerivedCategory.homologyFunctorFactors A (i + j)).hom.app (P ⊗ Q) =
            z ≫ (P ⊗ Q).homologyπ (i + j)

variable [BraidedCategory A] [∀ X : A, PreservesFiniteColimits (tensorLeft X)]

attribute [local instance] preservesFiniteColimitsTensorRight

/-- **The Künneth map on `D(A)`.** For any two objects `K` and `L` of the derived category,
tensoring cocycles gives the canonical map `Hⁱ(K) ⊗ Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗ᴸ L)`.

K-flat representatives `P` of `K` and `Q` of `L` are chosen, the map is
`CochainComplex.KFlatMonoidal.tensorHomology` for `P` and `Q`, and the two ends are transported
along the chosen isomorphisms.  The representative witness in the result specifies the source's
formula `[p] ⊗ [q] ↦ [p ⊗ q]`. -/
def cohomologyTensorProduct
    (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlat (curriedTensor A) P ∧ QuasiIso f)
    (K L : DerivedCategory A) (i j : ℤ) : CohomologyTensorProduct A cmp K L i j := by
  let P := Classical.choose (exists_kFlat_representative A hres K)
  have hP := (Classical.choose_spec (exists_kFlat_representative A hres K)).1
  let eP := Classical.choice (Classical.choose_spec (exists_kFlat_representative A hres K)).2
  let Q := Classical.choose (exists_kFlat_representative A hres L)
  have hQ := (Classical.choose_spec (exists_kFlat_representative A hres L)).1
  let eQ := Classical.choice (Classical.choose_spec (exists_kFlat_representative A hres L)).2
  let c : K ⊗ L ≅ DerivedCategory.Q.obj (P ⊗ Q) := (eP ⊗ᵢ eQ).symm ≪≫ cmp P Q hP hQ
  let α : P.homology i ⊗ Q.homology j ≅
      (DerivedCategory.homologyFunctor A i).obj K ⊗
        (DerivedCategory.homologyFunctor A j).obj L :=
    (((DerivedCategory.homologyFunctorFactors A i).symm.app P) ≪≫
      (DerivedCategory.homologyFunctor A i).mapIso eP) ⊗ᵢ
    (((DerivedCategory.homologyFunctorFactors A j).symm.app Q) ≪≫
      (DerivedCategory.homologyFunctor A j).mapIso eQ)
  let β : (DerivedCategory.homologyFunctor A (i + j)).obj (K ⊗ L) ≅
      (P ⊗ Q).homology (i + j) :=
    (DerivedCategory.homologyFunctor A (i + j)).mapIso c ≪≫
      (DerivedCategory.homologyFunctorFactors A (i + j)).app (P ⊗ Q)
  refine ⟨α.inv ≫ tensorHomology P Q i j ≫ β.inv,
    P, Q, hP, hQ, eP, eQ, tensorCycles P Q i j,
    tensorCycles_i P Q i j, ?_⟩
  have hα :
      ((DerivedCategory.homologyFunctorFactors A i).inv.app P ⊗ₘ
          (DerivedCategory.homologyFunctorFactors A j).inv.app Q) ≫
        ((DerivedCategory.homologyFunctor A i).map eP.hom ⊗ₘ
          (DerivedCategory.homologyFunctor A j).map eQ.hom) = α.hom := by
    simp only [α, tensorIso_hom, tensorHom_comp_tensorHom]
    rfl
  have hβ :
      (DerivedCategory.homologyFunctor A (i + j)).map
          ((eP.inv ⊗ₘ eQ.inv) ≫ (cmp P Q hP hQ).hom) ≫
        (DerivedCategory.homologyFunctorFactors A (i + j)).hom.app (P ⊗ Q) = β.hom := by
    dsimp [β, c]
    rfl
  let f : P.homology i ⊗ Q.homology j ⟶
      (DerivedCategory.homologyFunctor A i).obj K ⊗
        (DerivedCategory.homologyFunctor A j).obj L :=
    ((DerivedCategory.homologyFunctorFactors A i).inv.app P ⊗ₘ
      (DerivedCategory.homologyFunctorFactors A j).inv.app Q) ≫
    ((DerivedCategory.homologyFunctor A i).map eP.hom ⊗ₘ
      (DerivedCategory.homologyFunctor A j).map eQ.hom)
  let g : (DerivedCategory.homologyFunctor A (i + j)).obj (K ⊗ L) ⟶
      (P ⊗ Q).homology (i + j) :=
    (DerivedCategory.homologyFunctor A (i + j)).map
        ((eP.inv ⊗ₘ eQ.inv) ≫ (cmp P Q hP hQ).hom) ≫
      (DerivedCategory.homologyFunctorFactors A (i + j)).hom.app (P ⊗ Q)
  have hf : f ≫ α.inv = 𝟙 (P.homology i ⊗ Q.homology j) := by
    rw [show f = α.hom from hα]
    exact α.hom_inv_id
  have hg : β.inv ≫ g = 𝟙 ((P ⊗ Q).homology (i + j)) := by
    rw [show g = β.hom from hβ]
    exact β.inv_hom_id
  calc
    _ = (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫
        (f ≫ α.inv) ≫ tensorHomology P Q i j ≫ (β.inv ≫ g) := by
          dsimp only [f, g]
          simp only [Category.assoc]
          rfl
    _ = tensorCycles P Q i j ≫ (P ⊗ Q).homologyπ (i + j) := by
          simpa only [hf, hg, Category.comp_id, Category.id_comp] using
            homologyπ_tensorHomology P Q i j

omit [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- **On the chosen K-flat representatives the Künneth map of `D(A)` sends the tensor of two
cohomology classes to the class of the tensor of their cocycle representatives.** -/
lemma cohomologyTensorProduct_map_cocycles
    (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlat (curriedTensor A) P ∧ QuasiIso f)
    (K L : DerivedCategory A) (i j : ℤ) :
    ∃ (P Q : CochainComplex A ℤ)
      (hP : KFlat (curriedTensor A) P) (hQ : KFlat (curriedTensor A) Q)
      (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L)
      (z : P.cycles i ⊗ Q.cycles j ⟶ (P ⊗ Q).cycles (i + j)),
      z ≫ (P ⊗ Q).iCycles (i + j) =
          (P.iCycles i ⊗ₘ Q.iCycles j) ≫
            HomologicalComplex.ιTensorObj P Q i j (i + j) rfl ∧
        (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫
              ((DerivedCategory.homologyFunctorFactors A i).inv.app P ⊗ₘ
                (DerivedCategory.homologyFunctorFactors A j).inv.app Q) ≫
              ((DerivedCategory.homologyFunctor A i).map eP.hom ⊗ₘ
                (DerivedCategory.homologyFunctor A j).map eQ.hom) ≫
              (cohomologyTensorProduct A cmp hres K L i j).map ≫
              (DerivedCategory.homologyFunctor A (i + j)).map
                ((eP.inv ⊗ₘ eQ.inv) ≫ (cmp P Q hP hQ).hom) ≫
              (DerivedCategory.homologyFunctorFactors A (i + j)).hom.app (P ⊗ Q) =
            z ≫ (P ⊗ Q).homologyπ (i + j) :=
  (cohomologyTensorProduct A cmp hres K L i j).maps_cocycles

end Derived

end CochainComplex.KFlatMonoidal

end
