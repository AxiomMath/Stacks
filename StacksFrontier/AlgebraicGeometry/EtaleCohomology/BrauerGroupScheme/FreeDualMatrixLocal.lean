module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.MatrixUnitCombination

/-!
# The matrix of an induced endomorphism, and locality of the coefficient ring

Let `S` be a scheme and let `I` be a finite index type. `Stacks.EtaleCohomology.BrauerScheme.
freeDualMatrix` reads an endomorphism of the free sheaf of `𝒪_S`-modules on `I` as a square
matrix over `R₀ S = End (𝒪_S)`, and `Stacks.EtaleCohomology.BrauerScheme.pointMatrix` reads the
image of a matrix unit under a morphism of the matrix algebra sheaf. This file connects the two:
a morphism `ϑ` of sheaves of algebras acts on matrices through
`Stacks.Matrix.unitCombination (pointMatrix ϑ)`, the `R₀ S`-linear map sending the `(c, e)`
matrix unit to `pointMatrix ϑ (c, e)`. This is the `R₀ S`-level counterpart of
`Stacks.EtaleCohomology.BrauerScheme.sectionMap_eq_unitCombination`, which says the same about
the sections over an open set.

The second half of the file is a separatedness statement for `R₀ S`: an element of `R₀ S` is
determined by the sections of `𝒪_S` it produces, and those form a section of a sheaf, so two
elements of `R₀ S` which agree on a neighbourhood of every point of `S` are equal. This is what
lets a global matrix identity over `R₀ S` be checked on the Zariski neighbourhoods that
Skolem--Noether supplies, which is how the overlap step of [Stacks, Tag 0A2L] is proved.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.eq_sum_uncurry'_comp_matIncl`: **an endomorphism of a
  finite free sheaf of modules is the combination of the matrix units with its own matrix as
  coefficients.**
* `Stacks.EtaleCohomology.BrauerScheme.freeDualMatrix_pointMap`: **a morphism of the matrix
  algebra sheaf acts on matrices over `R₀ S` as the combination of the images of the matrix
  units.**
* `Stacks.EtaleCohomology.BrauerScheme.unitEnd_eq_of_forall_opens` and
  `Stacks.EtaleCohomology.BrauerScheme.unitEnd_eq_of_cover`: **an element of `R₀ S` is determined
  by its values on all open sets, and those values are local.**

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules Opposite

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

attribute [local instance] hasFiniteBiproductsModuleSheaf monoidalPreadditiveModuleSheaf

variable {S : Scheme.{u}} {I : Type u} [Fintype I] [DecidableEq I]

/-! ### The matrix of an induced endomorphism -/

/-- The matrix of the image of a scaled matrix unit under a morphism of sheaves of algebras: it
is the scaled image of that matrix unit. -/
theorem freeDualMatrix_pointMap_uncurry'_comp_matIncl
    (ϑ : endAlgebra (freeModule S I) ⟶ endAlgebra (freeModule S I)) (r : R₀ S) (k : I × I) :
    freeDualMatrix (MonoidalClosed.pointMap ϑ
        (MonoidalClosed.uncurry' (r ≫ matIncl (S := S) k)))
      = r • pointMatrix ϑ k := by
  funext a b
  rw [Matrix.smul_apply, smul_eq_mul, ← curry'_comp_matCoord,
    MonoidalClosed.curry'_pointMap, MonoidalClosed.curry'_uncurry', Category.assoc,
    Category.assoc, matIncl_comp_comp_matCoord,
    CategoryTheory.MonoidalCategory.unitEnd_mul_eq_comp]

/-- The identity morphism of the matrix algebra sheaf sends each matrix unit to itself. -/
private theorem pointMatrix_id (k : I × I) :
    pointMatrix (𝟙 (endAlgebra (freeModule S I))) k = Matrix.single k.1 k.2 (1 : R₀ S) := by
  rw [pointMatrix, MonoidalClosed.pointMap_self, freeDualMatrix_uncurry'_matIncl]

/-- The matrix of a scaled matrix unit is the scaled matrix unit. -/
theorem freeDualMatrix_uncurry'_comp_matIncl (r : R₀ S) (k : I × I) :
    freeDualMatrix (MonoidalClosed.uncurry' (r ≫ matIncl (S := S) k))
      = r • Matrix.single k.1 k.2 (1 : R₀ S) := by
  have h := freeDualMatrix_pointMap_uncurry'_comp_matIncl
    (𝟙 (endAlgebra (freeModule S I))) r k
  rw [MonoidalClosed.pointMap_self] at h
  rw [h, pointMatrix_id]

/-- The combination of the matrix units at their own images is the identity map on matrices. -/
theorem unitCombination_single_eq (M : Matrix I I (R₀ S)) :
    Stacks.Matrix.unitCombination (fun k : I × I => Matrix.single k.1 k.2 (1 : R₀ S)) M = M := by
  rw [Stacks.Matrix.unitCombination]
  conv_rhs => rw [Matrix.matrix_eq_sum_single M]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

/-- The matrix of the combination of the matrix units with coefficients a given matrix. -/
theorem freeDualMatrix_sum_uncurry'_comp_matIncl
    (ϑ : endAlgebra (freeModule S I) ⟶ endAlgebra (freeModule S I)) (M : Matrix I I (R₀ S)) :
    freeDualMatrix (MonoidalClosed.pointMap ϑ
        (∑ a : I, ∑ b : I, MonoidalClosed.uncurry' (M a b ≫ matIncl (S := S) (a, b))))
      = Stacks.Matrix.unitCombination (pointMatrix ϑ) M := by
  rw [MonoidalClosed.pointMap_sum, freeDualMatrix_sum]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => congrArg freeDualMatrix
    (MonoidalClosed.pointMap_sum ϑ Finset.univ
      fun b : I => MonoidalClosed.uncurry' (M a b ≫ matIncl (S := S) (a, b)))]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => freeDualMatrix_sum Finset.univ
    fun b : I => MonoidalClosed.pointMap ϑ
      (MonoidalClosed.uncurry' (M a b ≫ matIncl (S := S) (a, b)))]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    freeDualMatrix_pointMap_uncurry'_comp_matIncl ϑ (M a b) (a, b)

/-- **An endomorphism of a finite free sheaf of `𝒪_S`-modules is the combination of the matrix
units with its own matrix as coefficients.** -/
theorem eq_sum_uncurry'_comp_matIncl (g : freeModule S I ⟶ freeModule S I) :
    g = ∑ a : I, ∑ b : I,
      MonoidalClosed.uncurry' (freeDualMatrix g a b ≫ matIncl (S := S) (a, b)) := by
  refine freeDualMatrix_injective ?_
  have h := freeDualMatrix_sum_uncurry'_comp_matIncl
    (𝟙 (endAlgebra (freeModule S I))) (freeDualMatrix g)
  rw [MonoidalClosed.pointMap_self] at h
  rw [h]
  rw [show pointMatrix (𝟙 (endAlgebra (freeModule S I))) = fun k : I × I =>
    Matrix.single k.1 k.2 (1 : R₀ S) from funext pointMatrix_id, unitCombination_single_eq]

/-- **A morphism of the matrix algebra sheaf acts on matrices over `R₀ S` as the combination of
the images of the matrix units.** This is the `R₀ S`-level form of
`Stacks.EtaleCohomology.BrauerScheme.sectionMap_eq_unitCombination`. -/
theorem freeDualMatrix_pointMap (ϑ : endAlgebra (freeModule S I) ⟶ endAlgebra (freeModule S I))
    (g : freeModule S I ⟶ freeModule S I) :
    freeDualMatrix (MonoidalClosed.pointMap ϑ g)
      = Stacks.Matrix.unitCombination (pointMatrix ϑ) (freeDualMatrix g) := by
  conv_lhs => rw [eq_sum_uncurry'_comp_matIncl g]
  exact freeDualMatrix_sum_uncurry'_comp_matIncl ϑ (freeDualMatrix g)

/-! ### Locality of the coefficient ring -/

/-- **An element of `R₀ S` is determined by the sections of `𝒪_S` it produces.** The section of
`𝒪_S` attached to an endomorphism of `𝒪_S` as a module over itself is its value on the unit
section, and a morphism out of `𝒪_S` is determined by that value. -/
theorem unitEnd_eq_of_forall_opens {r r' : R₀ S}
    (h : ∀ U : S.Opens, unitEndValueHom S U r = unitEndValueHom S U r') : r = r' := by
  refine (_root_.SheafOfModules.unitHomEquiv
    (_root_.SheafOfModules.unit (Tensor.ringSheaf S.sheaf))).injective ?_
  ext V
  exact h V.unop

/-- **The sections of `𝒪_S` attached to an element of `R₀ S` are local**: two elements of `R₀ S`
which agree on a neighbourhood of every point of `S` are equal. This is the structure sheaf's
separatedness, transported along `Stacks.EtaleCohomology.BrauerScheme.unitEndValueHom`. -/
theorem unitEnd_eq_of_cover {r r' : R₀ S}
    (h : ∀ x : S, ∃ V : S.Opens, x ∈ V ∧ unitEndValueHom S V r = unitEndValueHom S V r') :
    r = r' := by
  refine unitEnd_eq_of_forall_opens fun U => ?_
  choose V hV hVeq using h
  refine TopCat.Sheaf.eq_of_locally_eq' S.sheaf (fun x : U => V x.1 ⊓ U) U
    (fun x => homOfLE inf_le_right) (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, ⟨hV y, hy⟩⟩)
    _ _ fun x => ?_
  have res {W W' : S.Opens} (hle : W ≤ W')
      (h : unitEndValueHom S W' r = unitEndValueHom S W' r') :
      unitEndValueHom S W r = unitEndValueHom S W r' := by
    rw [← unitEndValueHom_res hle, ← unitEndValueHom_res hle, h]
  exact ((unitEndValueHom_res (inf_le_right : V x.1 ⊓ U ≤ U) r).trans
    (res inf_le_left (hVeq x.1))).trans (unitEndValueHom_res inf_le_right r').symm

end Stacks.EtaleCohomology.BrauerScheme

end

end
