module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels

/-!
# The product on the homology of a tensor product of cochain complexes

Let `C` be a monoidal preadditive category with homology and let `P`, `Q` be cochain complexes
in `C` whose tensor product exists. Tensoring a cocycle of degree `i` with a cocycle of degree
`j` gives a cocycle of degree `i + j` of `P ⊗ Q`, and the class of the result depends only on
the two classes. This produces a canonical map

`Hⁱ(P) ⊗ Hʲ(Q) ⟶ Hⁱ⁺ʲ(P ⊗ Q)`.

Everything here is at the level of complexes; nothing is derived. The construction is the
input for the cohomology product of a derived tensor product, both over a ring and over a sheaf
of rings, which is why it is stated for an arbitrary ambient category rather than for modules.

## Main definitions

* `CochainComplex.tensorHomology`: the map `Hⁱ(P) ⊗ Hʲ(Q) ⟶ Hⁱ⁺ʲ(P ⊗ Q)`.
* `CochainComplex.tensorCycles`: the underlying map on cycles, from which it descends.

## Main results

* `CochainComplex.tensorCycles_i`: the map on cycles is the tensor of the two cycle inclusions,
  followed by the inclusion of the summand of degree `(i, j)`.
* `CochainComplex.homologyπ_tensorHomology`: the defining property, that `tensorHomology`
  sends the tensor of two homology classes to the class of the tensor of representatives.

## Implementation notes

The tensor product of the two complexes is taken as `HomologicalComplex.tensorObj` under a
`HomologicalComplex.HasTensor` hypothesis, rather than as `P ⊗ Q` for the monoidal structure on
`CochainComplex C ℤ`. Only the degreewise decomposition of the tensor product and its
differential are used — never the associator or the unitors — so assuming the full monoidal
structure on complexes, which needs a long list of coproduct hypotheses on graded objects,
would be assuming more than the construction consumes.

That the product descends from cycles to homology is `CategoryTheory.Limits.CokernelCofork.
isColimitTensor`: homology is the cokernel of the map from the complex into the cycles, and the
tensor product of two such cokernels is again one provided the tensor functors preserve them.
The hypothesis is phrased as preservation of finite colimits by the two tensor functors, which
is what a closed monoidal structure supplies.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Category Limits

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [CategoryWithHomology C]
  [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]
  (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]

/-- The tensor of a degree-`i` cycle of `P` with a degree-`j` cycle of `Q`, read in the summand
of bidegree `(i, j)`, is killed by the differential of `P ⊗ Q`. -/
theorem tensor_cycles_comp_d (i j : ℤ) :
    ((P.iCycles i ⊗ₘ Q.iCycles j) ≫
        HomologicalComplex.ιTensorObj P Q i j (i + j) rfl) ≫
      (HomologicalComplex.tensorObj P Q).d (i + j) (i + j + 1) = 0 := by
  change ((P.iCycles i ⊗ₘ Q.iCycles j) ≫
    HomologicalComplex.ιMapBifunctor P Q (curriedTensor C) (ComplexShape.up ℤ)
      i j (i + j) rfl) ≫
    (HomologicalComplex.mapBifunctor P Q (curriedTensor C)
      (ComplexShape.up ℤ)).d (i + j) (i + j + 1) = 0
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add]
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq P Q (curriedTensor C) _
    (show (ComplexShape.up ℤ).Rel i (i + 1) by simp) j (i + j + 1)
    (by change i + 1 + j = i + j + 1; omega),
    HomologicalComplex.mapBifunctor.d₂_eq P Q (curriedTensor C) _
    i (show (ComplexShape.up ℤ).Rel j (j + 1) by simp) (i + j + 1)
    (by change i + (j + 1) = i + j + 1; omega)]
  simp [tensorHom_def, whisker_exchange_assoc, ← comp_whiskerRight_assoc,
    ← whiskerLeft_comp_assoc]

/-- Tensoring a degree-`i` cycle of `P` with a degree-`j` cycle of `Q` gives a degree-`i + j`
cycle of `P ⊗ Q`. -/
def tensorCycles (i j : ℤ) :
    P.cycles i ⊗ Q.cycles j ⟶ (HomologicalComplex.tensorObj P Q).cycles (i + j) :=
  (HomologicalComplex.tensorObj P Q).liftCycles
    ((P.iCycles i ⊗ₘ Q.iCycles j) ≫
      HomologicalComplex.ιTensorObj P Q i j (i + j) rfl)
    (i + j + 1) (by simp) (tensor_cycles_comp_d P Q i j)

/-- The cycle `tensorCycles P Q i j`, included into the degree-`i + j` term of `P ⊗ Q`, is the
tensor of the inclusions of cycles followed by the inclusion of the summand of bidegree `(i, j)`.
-/
@[simp]
theorem tensorCycles_i (i j : ℤ) :
    tensorCycles P Q i j ≫ (HomologicalComplex.tensorObj P Q).iCycles (i + j) =
      (P.iCycles i ⊗ₘ Q.iCycles j) ≫
        HomologicalComplex.ιTensorObj P Q i j (i + j) rfl :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The differential of `P ⊗ Q` applied to a term in which the second factor is a cycle
recovers the differential of `P` on the first factor. -/
theorem tensor_left_boundary_d (i j : ℤ) :
    ((𝟙 (P.X (i - 1)) ⊗ₘ Q.iCycles j) ≫
        HomologicalComplex.ιTensorObj P Q (i - 1) j (i + j - 1) (by omega)) ≫
      (HomologicalComplex.tensorObj P Q).d (i + j - 1) (i + j) =
    (P.d (i - 1) i ⊗ₘ Q.iCycles j) ≫
      HomologicalComplex.ιTensorObj P Q i j (i + j) rfl := by
  change ((𝟙 (P.X (i - 1)) ⊗ₘ Q.iCycles j) ≫
      HomologicalComplex.ιMapBifunctor P Q (curriedTensor C)
        (ComplexShape.up ℤ) (i - 1) j (i + j - 1) (by dsimp; omega)) ≫
    (HomologicalComplex.mapBifunctor P Q (curriedTensor C)
      (ComplexShape.up ℤ)).d (i + j - 1) (i + j) = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add]
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq P Q (curriedTensor C) _
    (show (ComplexShape.up ℤ).Rel (i - 1) i by simp) j (i + j)
    (by change i + j = i + j; rfl),
    HomologicalComplex.mapBifunctor.d₂_eq P Q (curriedTensor C) _
    (i - 1) (show (ComplexShape.up ℤ).Rel j (j + 1) by simp) (i + j)
    (by change i - 1 + (j + 1) = i + j; omega)]
  simp [tensorHom_def, whisker_exchange_assoc, ← whiskerLeft_comp_assoc]

/-- A boundary in the first variable tensored with a cycle in the second is a boundary. -/
theorem tensorCycles_left_boundary (i j : ℤ) :
    (P.toCycles (i - 1) i ⊗ₘ 𝟙 (Q.cycles j)) ≫
      tensorCycles P Q i j ≫
        (HomologicalComplex.tensorObj P Q).homologyπ (i + j) = 0 := by
  let x : P.X (i - 1) ⊗ Q.cycles j ⟶ (HomologicalComplex.tensorObj P Q).X (i + j - 1) :=
    (𝟙 (P.X (i - 1)) ⊗ₘ Q.iCycles j) ≫
      HomologicalComplex.ιTensorObj P Q (i - 1) j (i + j - 1) (by omega)
  have h : (P.toCycles (i - 1) i ⊗ₘ 𝟙 (Q.cycles j)) ≫ tensorCycles P Q i j =
      x ≫ (HomologicalComplex.tensorObj P Q).toCycles (i + j - 1) (i + j) := by
    rw [← cancel_mono ((HomologicalComplex.tensorObj P Q).iCycles (i + j))]
    simp only [Category.assoc, tensorCycles_i, HomologicalComplex.toCycles_i]
    rw [tensor_left_boundary_d]
    simp [tensorHom_def, ← comp_whiskerRight_assoc]
  rw [← Category.assoc, h, Category.assoc,
    HomologicalComplex.toCycles_comp_homologyπ, Limits.comp_zero]

/-- The differential of `P ⊗ Q` applied to a term in which the first factor is a cycle
recovers, up to the Koszul sign, the differential of `Q` on the second factor. -/
theorem tensor_right_boundary_d (i j : ℤ) :
    ((P.iCycles i ⊗ₘ 𝟙 (Q.X (j - 1))) ≫
        HomologicalComplex.ιTensorObj P Q i (j - 1) (i + j - 1) (by omega)) ≫
      (HomologicalComplex.tensorObj P Q).d (i + j - 1) (i + j) =
    ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      ⟨i, j - 1⟩ •
      ((P.iCycles i ⊗ₘ Q.d (j - 1) j) ≫
        HomologicalComplex.ιTensorObj P Q i j (i + j) rfl) := by
  change ((P.iCycles i ⊗ₘ 𝟙 (Q.X (j - 1))) ≫
      HomologicalComplex.ιMapBifunctor P Q (curriedTensor C)
        (ComplexShape.up ℤ) i (j - 1) (i + j - 1) (by dsimp; omega)) ≫
    (HomologicalComplex.mapBifunctor P Q (curriedTensor C)
      (ComplexShape.up ℤ)).d (i + j - 1) (i + j) = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add]
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq P Q (curriedTensor C) _
    (show (ComplexShape.up ℤ).Rel i (i + 1) by simp) (j - 1) (i + j)
    (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq P Q (curriedTensor C) _
    i (show (ComplexShape.up ℤ).Rel (j - 1) j by simp) (i + j)
    (by dsimp)]
  simp [tensorHom_def, ← comp_whiskerRight_assoc, Linear.comp_units_smul]

/-- A cycle in the first variable tensored with a boundary in the second is a boundary. -/
theorem tensorCycles_right_boundary (i j : ℤ) :
    (𝟙 (P.cycles i) ⊗ₘ Q.toCycles (j - 1) j) ≫
      tensorCycles P Q i j ≫
        (HomologicalComplex.tensorObj P Q).homologyπ (i + j) = 0 := by
  let ε : ℤˣ := ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) ⟨i, j - 1⟩
  let x : P.cycles i ⊗ Q.X (j - 1) ⟶ (HomologicalComplex.tensorObj P Q).X (i + j - 1) :=
    ε • ((P.iCycles i ⊗ₘ 𝟙 (Q.X (j - 1))) ≫
      HomologicalComplex.ιTensorObj P Q i (j - 1) (i + j - 1) (by omega))
  have h : (𝟙 (P.cycles i) ⊗ₘ Q.toCycles (j - 1) j) ≫ tensorCycles P Q i j =
      x ≫ (HomologicalComplex.tensorObj P Q).toCycles (i + j - 1) (i + j) := by
    rw [← cancel_mono ((HomologicalComplex.tensorObj P Q).iCycles (i + j))]
    simp only [Category.assoc, tensorCycles_i, HomologicalComplex.toCycles_i]
    change (𝟙 (P.cycles i) ⊗ₘ Q.toCycles (j - 1) j) ≫
      (P.iCycles i ⊗ₘ Q.iCycles j) ≫
        HomologicalComplex.ιTensorObj P Q i j (i + j) rfl =
      (ε • ((P.iCycles i ⊗ₘ 𝟙 (Q.X (j - 1))) ≫
        HomologicalComplex.ιTensorObj P Q i (j - 1) (i + j - 1) (by omega))) ≫
          (HomologicalComplex.tensorObj P Q).d (i + j - 1) (i + j)
    rw [Linear.units_smul_comp, tensor_right_boundary_d, smul_smul,
      Int.units_mul_self, one_smul]
    simp only [← Category.assoc, tensorHom_comp_tensorHom,
      Category.id_comp, HomologicalComplex.toCycles_i]
  rw [← Category.assoc, h, Category.assoc,
    HomologicalComplex.toCycles_comp_homologyπ, Limits.comp_zero]

variable [∀ X : C, PreservesFiniteColimits ((curriedTensor C).obj X)]
  [∀ X : C, PreservesFiniteColimits ((curriedTensor C).flip.obj X)]
  [HasBinaryCoproducts C]

/-- The tensor of the cokernel presentations of `Hⁱ(P)` and `Hʲ(Q)` is a cokernel presentation
of `Hⁱ(P) ⊗ Hʲ(Q)`. -/
private def isColimitTensorHomology (i j : ℤ) :=
  Limits.CokernelCofork.isColimitTensor
    (P.homologyIsCokernel (i - 1) i (by simp))
    (Q.homologyIsCokernel (j - 1) j (by simp))

/-- The product on homology induced by tensoring cocycles,
`Hⁱ(P) ⊗ Hʲ(Q) ⟶ Hⁱ⁺ʲ(P ⊗ Q)`. -/
def tensorHomology (i j : ℤ) :
    P.homology i ⊗ Q.homology j ⟶ (HomologicalComplex.tensorObj P Q).homology (i + j) :=
  (Limits.CokernelCofork.isColimitTensor
    (P.homologyIsCokernel (i - 1) i (by simp))
    (Q.homologyIsCokernel (j - 1) j (by simp))).desc
      (Limits.CokernelCofork.ofπ
        (tensorCycles P Q i j ≫ (HomologicalComplex.tensorObj P Q).homologyπ (i + j))
        (by
          apply Limits.coprod.hom_ext
          · simp [← tensorHom_id, tensorCycles_left_boundary]
          · simp [← id_tensorHom, tensorCycles_right_boundary]))

/-- The defining property of the homology product: it sends the tensor of the classes of two
cocycles to the class of the tensor of those cocycles. -/
theorem homologyπ_tensorHomology (i j : ℤ) :
    (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫ tensorHomology P Q i j =
      tensorCycles P Q i j ≫ (HomologicalComplex.tensorObj P Q).homologyπ (i + j) :=
  Limits.Cofork.IsColimit.π_desc
    (hs := isColimitTensorHomology P Q i j)

/-! ### Naturality in both variables -/

section Naturality

variable {P' Q' : CochainComplex C ℤ} [HomologicalComplex.HasTensor P' Q']

omit [∀ X : C, PreservesFiniteColimits ((curriedTensor C).obj X)]
  [∀ X : C, PreservesFiniteColimits ((curriedTensor C).flip.obj X)]
  [HasBinaryCoproducts C] in
/-- **The cycle-level product is natural in both variables.** For morphisms of complexes
`f : P ⟶ P'` and `g : Q ⟶ Q'`, tensoring cycles commutes with the map `P ⊗ Q ⟶ P' ⊗ Q'`
induced by `f` and `g`.

Both sides are maps into the cycles of `P' ⊗ Q'`, which is a monomorphism away from the
complex, so it is enough to compare them after `iCycles`; there each becomes the tensor of
`f` and `g` on the terms, followed by the inclusion of the `(i, j)` summand, by
`HomologicalComplex.ι_mapBifunctorMap`. -/
theorem tensorCycles_naturality (f : P ⟶ P') (g : Q ⟶ Q') (i j : ℤ) :
    tensorCycles P Q i j ≫
        HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom f g) (i + j) =
      (HomologicalComplex.cyclesMap f i ⊗ₘ HomologicalComplex.cyclesMap g j) ≫
        tensorCycles P' Q' i j := by
  have hι : HomologicalComplex.ιTensorObj P Q i j (i + j) rfl ≫
      (HomologicalComplex.tensorHom f g).f (i + j) =
        (f.f i ⊗ₘ g.f j) ≫ HomologicalComplex.ιTensorObj P' Q' i j (i + j) rfl := by
    rw [HomologicalComplex.ι_mapBifunctorMap, tensorHom_def, Category.assoc]
    rfl
  rw [← cancel_mono ((HomologicalComplex.tensorObj P' Q').iCycles (i + j)), Category.assoc,
    Category.assoc, HomologicalComplex.cyclesMap_i, tensorCycles_i, ← Category.assoc,
    tensorCycles_i, Category.assoc, hι, ← Category.assoc, ← Category.assoc,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.cyclesMap_i]

/-- **The product on homology is natural in both variables.** For morphisms of complexes
`f : P ⟶ P'` and `g : Q ⟶ Q'`, the square

`Hⁱ(P) ⊗ Hʲ(Q) ⟶ Hⁱ⁺ʲ(P ⊗ Q)`, `Hⁱ(P') ⊗ Hʲ(Q') ⟶ Hⁱ⁺ʲ(P' ⊗ Q')`

commutes, the vertical maps being those `f` and `g` induce on cohomology.

The target of the product is a cokernel of which `Hⁱ(P) ⊗ Hʲ(Q)` is the cone point, so two
maps out of it agree as soon as they agree after the projection
`P.homologyπ i ⊗ₘ Q.homologyπ j`; there both sides are the cycle-level product of
`tensorCycles_naturality` followed by a projection to homology. -/
theorem tensorHomology_naturality (f : P ⟶ P') (g : Q ⟶ Q') (i j : ℤ) :
    tensorHomology P Q i j ≫
        HomologicalComplex.homologyMap (HomologicalComplex.tensorHom f g) (i + j) =
      (HomologicalComplex.homologyMap f i ⊗ₘ HomologicalComplex.homologyMap g j) ≫
        tensorHomology P' Q' i j := by
  refine Limits.Cofork.IsColimit.hom_ext (isColimitTensorHomology P Q i j) ?_
  change (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫ _ = (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫ _
  rw [← Category.assoc, homologyπ_tensorHomology, Category.assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc, tensorCycles_naturality,
    Category.assoc, ← homologyπ_tensorHomology, ← Category.assoc, tensorHom_comp_tensorHom,
    ← Category.assoc, tensorHom_comp_tensorHom, HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.homologyπ_naturality]

end Naturality

end CochainComplex

end
