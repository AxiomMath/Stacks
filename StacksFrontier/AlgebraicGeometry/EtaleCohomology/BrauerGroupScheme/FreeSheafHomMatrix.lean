module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.MatrixFreeSheaf

/-!
# Morphisms between free sheaves of modules of finite rank are rectangular matrices

`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.MatrixFreeSheaf` identifies the
*endomorphisms* of a free sheaf of `𝒪_S`-modules of finite rank with square matrices over
`Stacks.EtaleCohomology.BrauerScheme.R₀ S`, the endomorphisms of the monoidal unit. This file is
the rectangular case: morphisms `free I ⟶ free K` are `I × K` matrices, and composition is the
matrix product in the same order.

The rectangular case is what a *factorisation* through a free sheaf of a different rank needs. In
[Stacks, Tag 0A2L] the projector `p` is read on a trivialisation as `Matrix.altProj` on the index
type `K = n → n`, right multiplication by it factors as
`M ↦ M a` followed by `v ↦ v aᵗ` (`Matrix.mul_altProj_eq_vecMulVec`), and the middle term is the
free module on `K` while the two ends are the free module on `K × K`. Those three ranks are
different, so the square dictionary cannot express the factorisation and this one can.

## Main definitions

* `CategoryTheory.MonoidalCategory.unitHomMatrixEquiv`: morphisms between two finite direct sums
  of copies of the monoidal unit are rectangular matrices over `End (𝟙_ C)`.
* `Stacks.EtaleCohomology.BrauerScheme.freeHomMatrixEquiv`: morphisms between two free sheaves of
  `𝒪_S`-modules of finite rank are rectangular matrices over `R₀ S`.

## Main results

* `CategoryTheory.MonoidalCategory.unitHomMatrixEquiv_comp` and
  `Stacks.EtaleCohomology.BrauerScheme.freeHomMatrixEquiv_comp`: **composition goes to the matrix
  product, in the same order.**
* `Stacks.EtaleCohomology.BrauerScheme.freeHomMatrixEquiv_add`: the dictionary is additive.
* `Stacks.EtaleCohomology.BrauerScheme.freeEndMatrixEquiv_eq_freeHomMatrixEquiv`: on
  endomorphisms it is the square dictionary of the sibling file.

## Implementation notes

The order of the matrix product does not reverse, for the reason recorded in the sibling file:
`CategoryTheory.Limits.biproduct.components` of a composite is `∑ k, components F j k ≫
components G k l`, and the multiplication of `End (𝟙_ C)` reverses composition, so the two
reversals cancel — which is only legitimate because `End (𝟙_ C)` is commutative
(`CategoryTheory.MonoidalCategory.comp_comm_unitEnd`).

The index types live in `Type 0` because `CategoryTheory.Limits.biproduct.matrix` does, and the
free sheaves are therefore taken on their `ULift`s, exactly as
`Stacks.EtaleCohomology.BrauerScheme.matrixAlgebra` is.

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
  [HasFiniteBiproducts C]

/-- **Morphisms between two finite direct sums of copies of the unit are rectangular matrices
over `End (𝟙_ C)`.** This is `CategoryTheory.Limits.biproduct.matrixEquiv`, read at the type
`Matrix`; the ascription matters, because instance search keys on `Matrix` and on `End` and
cannot see either through the bare function type `biproduct.matrixEquiv` is stated at. -/
def unitHomMatrixEquiv (I K : Type) [Finite I] [Finite K] :
    ((⨁ fun _ : I => 𝟙_ C) ⟶ ⨁ fun _ : K => 𝟙_ C) ≃ Matrix I K (End (𝟙_ C)) :=
  biproduct.matrixEquiv

omit [MonoidalPreadditive C] in
/-- The `(i, k)` entry of the matrix of `F` is the `(i, k)` component of `F` as a morphism of
biproducts. -/
lemma unitHomMatrixEquiv_apply (I K : Type) [Finite I] [Finite K]
    (F : (⨁ fun _ : I => 𝟙_ C) ⟶ ⨁ fun _ : K => 𝟙_ C) (i : I) (k : K) :
    unitHomMatrixEquiv I K F i k = biproduct.components F i k := rfl

omit [MonoidalPreadditive C] in
/-- **Composition goes to the matrix product, in the same order.** -/
theorem unitHomMatrixEquiv_comp (I K L : Type) [Finite I] [Fintype K] [Finite L]
    (F : (⨁ fun _ : I => 𝟙_ C) ⟶ ⨁ fun _ : K => 𝟙_ C)
    (G : (⨁ fun _ : K => 𝟙_ C) ⟶ ⨁ fun _ : L => 𝟙_ C) :
    unitHomMatrixEquiv I L (F ≫ G) =
      unitHomMatrixEquiv I K F * unitHomMatrixEquiv K L G := by
  have h : F ≫ G = biproduct.matrix (fun i l =>
      ∑ k, biproduct.components F i k ≫ biproduct.components G k l) := by
    rw [← CategoryTheory.SimplicialObject.EilenbergMacLane.biproduct_matrix_comp,
      biproduct.components_matrix, biproduct.components_matrix]
  funext i l
  rw [unitHomMatrixEquiv_apply, h, biproduct.matrix_components, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => comp_comm_unitEnd _ _

omit [MonoidalPreadditive C] in
/-- The dictionary is additive. -/
theorem unitHomMatrixEquiv_add (I K : Type) [Finite I] [Finite K]
    (F G : (⨁ fun _ : I => 𝟙_ C) ⟶ ⨁ fun _ : K => 𝟙_ C) :
    unitHomMatrixEquiv I K (F + G) =
      unitHomMatrixEquiv I K F + unitHomMatrixEquiv I K G := by
  funext i k
  simp only [unitHomMatrixEquiv_apply, Matrix.add_apply, biproduct.components,
    Preadditive.comp_add, Preadditive.add_comp]

end CategoryTheory.MonoidalCategory

namespace Stacks.EtaleCohomology.BrauerScheme

variable (S : Scheme.{u})

attribute [local instance] hasFiniteBiproductsModuleSheaf monoidalPreadditiveModuleSheaf

/-- **Morphisms between two free sheaves of `𝒪_S`-modules of finite rank are rectangular
matrices over `R₀ S`.** -/
def freeHomMatrixEquiv (I K : Type) [Finite I] [Finite K] :
    (_root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} K)) ≃
      Matrix I K (R₀ S) :=
  (Iso.homCongr (freeBiproductIso S I) (freeBiproductIso S K)).trans (unitHomMatrixEquiv I K)

/-- The matrix of a morphism `f` of free sheaves is the matrix of `f` transported along the
isomorphisms `freeBiproductIso` with the direct sums of copies of the unit. -/
lemma freeHomMatrixEquiv_apply (I K : Type) [Finite I] [Finite K]
    (f : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} K)) :
    freeHomMatrixEquiv S I K f =
      unitHomMatrixEquiv I K ((freeBiproductIso S I).inv ≫ f ≫ (freeBiproductIso S K).hom) :=
  rfl

/-- On endomorphisms the rectangular dictionary is the square one. -/
theorem freeEndMatrixEquiv_eq_freeHomMatrixEquiv (I : Type) [Finite I]
    (f : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I)) :
    freeEndMatrixEquiv S I f = freeHomMatrixEquiv S I I f :=
  rfl

/-- **Composition of morphisms of free sheaves of `𝒪_S`-modules goes to the matrix product, in
the same order.** -/
theorem freeHomMatrixEquiv_comp (I K L : Type) [Finite I] [Fintype K] [Finite L]
    (f : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} K))
    (g : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} K) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} L)) :
    freeHomMatrixEquiv S I L (f ≫ g) =
      freeHomMatrixEquiv S I K f * freeHomMatrixEquiv S K L g := by
  have hfg : (freeBiproductIso S I).inv ≫ (f ≫ g) ≫ (freeBiproductIso S L).hom =
      ((freeBiproductIso S I).inv ≫ f ≫ (freeBiproductIso S K).hom) ≫
        ((freeBiproductIso S K).inv ≫ g ≫ (freeBiproductIso S L).hom) :=
    Iso.homCongr_comp (freeBiproductIso S I) (freeBiproductIso S K) (freeBiproductIso S L) f g
  rw [freeHomMatrixEquiv_apply, freeHomMatrixEquiv_apply, freeHomMatrixEquiv_apply, hfg,
    unitHomMatrixEquiv_comp]

/-- The dictionary is additive. -/
theorem freeHomMatrixEquiv_add (I K : Type) [Finite I] [Finite K]
    (f g : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} K)) :
    freeHomMatrixEquiv S I K (f + g) =
      freeHomMatrixEquiv S I K f + freeHomMatrixEquiv S I K g := by
  simp only [freeHomMatrixEquiv_apply, Preadditive.comp_add, Preadditive.add_comp,
    unitHomMatrixEquiv_add]

end Stacks.EtaleCohomology.BrauerScheme

end

end
