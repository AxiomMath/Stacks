module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedFiniteType
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic

/-!
# A graded module of finite type has finite graded pieces

`Stacks.Coherent.IsFiniteTypeOnAffine M` says that over every affine open `U` of `X` the sections
of `M` are generated, as a module over the sections of the graded algebra `A`, by a *finite* set
`G` of homogeneous sections. That is a statement about the whole of `M`, across all degrees at
once, and nothing in the library drew from it a statement about one graded piece `M.piece n`.

This file does. Fix a target degree `n` and an affine open `U`. Each generator `s ∈ G` acts by
multiplication, carrying the degree-`n - deg s` sections of `A` to the degree-`n` sections of `M`,
and those finitely many maps between them have images covering `Γ(M.piece n, U)`. So if each
graded piece of the *algebra* is module-finite over `Γ(X, U)`, then so is each graded piece of the
*module*.

The degrees of a `SheafOfModules.GradedModule` range over all of `ℤ`, which makes the statement
look as though it needs an infinite sum of actions. It does not: the target degree is fixed first,
and then the generating set is finite, so only finitely many source degrees `n - deg s` occur.

## Main results

* `Stacks.Coherent.moduleFinite_gradedPiece_of_isFiniteTypeOnAffine` — each graded piece of a
  graded module of finite type is module-finite over the sections of the structure sheaf, given
  that each graded piece of the graded algebra is.

## Implementation notes

`smulSectionₗ` bundles multiplication by a fixed homogeneous section as a linear map, which is
what lets the covering argument be a statement about `LinearMap.range` and hence about
`Submodule.fg_iSup`. `cast_eq_castHom` replaces the `▸` that the generating-set predicate produces
with `SheafOfModules.castHom`, so that the degree bookkeeping never leaves a cast inside a
statement.
-/

@[expose] public section

open CategoryTheory Limits Opposite SheafOfModules
open AlgebraicGeometry

universe u

namespace Stacks.Coherent

variable {X : Scheme.{u}} {A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-- A graded piece of a sheaf of modules on `X`, read as an `𝒪_X`-module. -/
public abbrev gradedPieceModule (P : ℤ → SheafOfModules.{u} X.ringCatSheaf) (n : ℤ) : X.Modules :=
  P n

/-- **Multiplication by a fixed homogeneous section, as a linear map.** For `x` a section of
`M.piece d` over an affine open `U`, multiplication by `x` carries the degree-`n - d` sections of
the graded algebra to the degree-`n` sections of `M`, linearly over `Γ(X, U)`. -/
public noncomputable def smulSectionₗ (M : SheafOfModules.GradedModule.{u, u, u} A) (n : ℤ)
    {d : ℤ} (U : X.affineOpens) (x : (M.piece d).val.obj (op U.1)) :
    Γ(gradedPieceModule A.piece (n - d), U.1) →ₗ[Γ(X, U.1)]
      Γ(gradedPieceModule M.piece n, U.1) where
  toFun a := M.smulSection n x a
  map_add' a b := (M.smulSection n x).map_add a b
  map_smul' r a := M.smulSection_smul_right n r x a

/-- Transporting a section along an equality of degrees is `SheafOfModules.castHom`. Stated so
that the degree bookkeeping below never leaves a `▸` inside a statement. -/
public theorem cast_eq_castHom (M : SheafOfModules.GradedModule.{u, u, u} A) {i j : ℤ} (h : i = j)
    (V : (X.Opens)ᵒᵖ) (y : (M.piece i).val.obj V) :
    (h ▸ y : (M.piece j).val.obj V) = SheafOfModules.castHom M.piece h V y := by
  subst h; rfl

/-- **A graded piece of a graded module of finite type is module-finite.** If every graded piece
of the graded algebra `A` is module-finite over the sections of the structure sheaf on affine
opens, and `M` is of finite type on affine opens, then every graded piece of `M` is module-finite
over the sections of the structure sheaf on affine opens.

The target degree `n` is fixed before the generating set is used, so although the degrees of `M`
range over all of `ℤ`, only the finitely many source degrees `n - deg s` for `s` in the generating
set contribute. -/
public theorem moduleFinite_gradedPiece_of_isFiniteTypeOnAffine
    (M : SheafOfModules.GradedModule.{u, u, u} A)
    (hA : ∀ (m : ℤ) (U : X.affineOpens),
      Module.Finite Γ(X, U.1) Γ(gradedPieceModule A.piece m, U.1))
    (hM : Stacks.Coherent.IsFiniteTypeOnAffine M) (n : ℤ) (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(gradedPieceModule M.piece n, U.1) := by
  classical
  obtain ⟨G, hG⟩ := hM U
  refine Module.finite_def.mpr ?_
  have hsub : (⊤ : Submodule Γ(X, U.1) Γ(gradedPieceModule M.piece n, U.1)) =
      ⨆ s : ↥G, LinearMap.range (smulSectionₗ M n U s.1.2) := by
    refine le_antisymm (fun t _ => ?_) le_top
    refine (AddSubgroup.closure_le
      (⨆ s : ↥G, LinearMap.range (smulSectionₗ M n U s.1.2)).toAddSubgroup).mpr ?_
      ((hG n).ge (AddSubgroup.mem_top t))
    rintro y ⟨s, hs, m, a, hdeg, rfl⟩
    obtain rfl : m = n - s.1 := by omega
    exact Submodule.mem_iSup_of_mem (⟨s, hs⟩ : ↥G)
      ⟨a, (cast_eq_castHom M hdeg (op U.1) _).symm⟩
  rw [hsub]
  refine Submodule.fg_iSup _ fun s => ?_
  rw [LinearMap.range_eq_map]
  exact (Module.finite_def.mp (hA (n - s.1.1) U)).map _

end Stacks.Coherent

end
