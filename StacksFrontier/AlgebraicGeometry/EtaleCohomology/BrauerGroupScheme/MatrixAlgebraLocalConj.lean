module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.FreeDualMatrixLocal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.MatrixAlgebraSections

/-!
# An automorphism of the matrix algebra sheaf is locally inner, on the matrix units

`Stacks.EtaleCohomology.BrauerScheme.exists_units_conj_eq_of_iso_matrixAlgebra` -- Skolem--Noether
spread out from a stalk -- says that an automorphism `Ψ` of the sheaf of `d × d` matrices over
`𝒪_T` is, on a neighbourhood of any point of `T`, conjugation by a single invertible matrix of
sections. That statement is about the action of `Ψ` on *all* matrices of sections; the overlap
step of [Stacks, Tag 0A2L] needs it on the *matrix units* alone, because what the tensor power of
`Ψ` does to the Saltman projector is determined by what `Ψ` does to the matrix units.

This file performs that specialisation. The bookkeeping is the reindexing: the matrix dictionary
`Stacks.EtaleCohomology.BrauerScheme.sectionPointMatrix` is indexed by `ULift (Fin d)`, because
the free sheaf of modules of rank `d` is the one on `ULift (Fin d)`, whereas Skolem--Noether is
stated over `Fin d`. `Stacks.EtaleCohomology.BrauerScheme.matrixAlgebraSectionAlgEquiv` is the
composite of the two reindexings with
`Stacks.EtaleCohomology.BrauerScheme.sectionAlgEquiv`, and
`Stacks.Matrix.unitCombination_single` evaluates the latter at a matrix unit.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.exists_sectionPointMatrix_eq_conj`: **every point of `T`
  has a neighbourhood on which the images of the matrix units under an automorphism of
  `Mat_d(𝒪_T)` are the conjugates of the matrix units by one invertible matrix of sections.**

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

/-- Restriction along the identity inclusion of an open set leaves a matrix of sections
unchanged. -/
theorem matrix_map_res_self {T : Scheme.{u}} {ι : Type*} (V : T.Opens)
    (M : Matrix ι ι Γ(T, V)) :
    M.map (T.presheaf.map (homOfLE (le_refl V)).op).hom = M := by
  have h : (homOfLE (le_refl V)).op = 𝟙 (op V) := Subsingleton.elim _ _
  rw [h, T.presheaf.map_id]
  exact Matrix.map_id M

/-- The reindexing of a matrix unit over `Fin d` is the matrix unit over `ULift (Fin d)`. -/
theorem reindex_ulift_single {T : Scheme.{u}} {d : ℕ} (V : T.Opens) (a b : Fin d) :
    Matrix.reindex (Equiv.ulift.{u, 0} (α := Fin d)).symm
        (Equiv.ulift.{u, 0} (α := Fin d)).symm (Matrix.single a b (1 : Γ(T, V)))
      = Matrix.single (ULift.up a) (ULift.up b) (1 : Γ(T, V)) := by
  funext p q
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.single_apply, Matrix.single_apply]
  exact if_congr ⟨fun h ↦ ⟨congrArg ULift.up h.1, congrArg ULift.up h.2⟩,
    fun h ↦ ⟨congrArg ULift.down h.1, congrArg ULift.down h.2⟩⟩ rfl rfl

/-- The value of an automorphism of the matrix algebra sheaf, read on sections, at a matrix unit
is the image of that matrix unit in the matrix dictionary. -/
theorem matrixAlgebraSectionAlgEquiv_single {T : Scheme.{u}} {d : ℕ}
    (Ψ : matrixAlgebra T d ≅ matrixAlgebra T d) (V : T.Opens) (a b p q : Fin d) :
    matrixAlgebraSectionAlgEquiv Ψ V (Matrix.single a b (1 : Γ(T, V))) p q
      = sectionPointMatrix Ψ.hom V (ULift.up a, ULift.up b) (ULift.up p) (ULift.up q) := by
  have hstep : sectionAlgEquiv Ψ V
        (Matrix.reindex (Equiv.ulift.{u, 0} (α := Fin d)).symm
          (Equiv.ulift.{u, 0} (α := Fin d)).symm (Matrix.single a b (1 : Γ(T, V))))
      = sectionPointMatrix Ψ.hom V (ULift.up a, ULift.up b) := by
    rw [reindex_ulift_single]
    change sectionMap Ψ.hom.hom V (Matrix.single (ULift.up a) (ULift.up b) (1 : Γ(T, V))) = _
    rw [sectionMap_eq_unitCombination, Stacks.Matrix.unitCombination_single]
  change Matrix.reindex (Equiv.ulift.{u, 0} (α := Fin d))
      (Equiv.ulift.{u, 0} (α := Fin d))
      (sectionAlgEquiv Ψ V
        (Matrix.reindex (Equiv.ulift.{u, 0} (α := Fin d)).symm
          (Equiv.ulift.{u, 0} (α := Fin d)).symm (Matrix.single a b (1 : Γ(T, V))))) p q = _
  rw [hstep, Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl

/-- **Every point of `T` has a neighbourhood on which the images of the matrix units under an
automorphism of `Mat_d(𝒪_T)` are the conjugates of the matrix units by one invertible matrix of
sections.** This is
`Stacks.EtaleCohomology.BrauerScheme.exists_units_conj_eq_of_iso_matrixAlgebra` evaluated at the
matrix units, where `Stacks.Matrix.unitCombination_single` identifies the value of the
section-level automorphism with the matrix dictionary's `sectionPointMatrix`. -/
theorem exists_sectionPointMatrix_eq_conj {T : Scheme.{u}} {d : ℕ} [NeZero d]
    (Ψ : matrixAlgebra T d ≅ matrixAlgebra T d) (x : T) :
    ∃ (V : T.Opens) (_ : x ∈ V) (u : (Matrix (Fin d) (Fin d) Γ(T, V))ˣ),
      ∀ a b p q : Fin d,
        sectionPointMatrix Ψ.hom V (ULift.up a, ULift.up b) (ULift.up p) (ULift.up q)
          = ((u : Matrix (Fin d) (Fin d) Γ(T, V)) * Matrix.single a b (1 : Γ(T, V)) *
              ((u⁻¹ : (Matrix (Fin d) (Fin d) Γ(T, V))ˣ) :
                Matrix (Fin d) (Fin d) Γ(T, V))) p q := by
  obtain ⟨V, hxV, u, hu⟩ := exists_units_conj_eq_of_iso_matrixAlgebra Ψ x
  refine ⟨V, hxV, u, fun a b p q ↦ ?_⟩
  have h := hu V le_rfl (Matrix.single a b (1 : Γ(T, V)))
  simp only [matrix_map_res_self] at h
  exact (matrixAlgebraSectionAlgEquiv_single Ψ V a b p q).symm.trans (congrFun₂ h p q)

end Stacks.EtaleCohomology.BrauerScheme

end

end
