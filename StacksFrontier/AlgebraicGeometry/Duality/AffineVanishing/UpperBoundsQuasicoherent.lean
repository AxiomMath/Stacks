module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationTower
public import StacksFrontier.AlgebraicGeometry.Duality.SpaltensteinCriterion.QuasicoherentTruncationConvergence
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Further results

Results complementing `StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace CategoryTheory.Pretriangulated

end CategoryTheory.Pretriangulated

namespace Stacks.DerivedLimit

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]

variable (E : DerivedCategory A) [HasProduct fun n : ℕ ↦ (truncGETower A E).obj ⟨n⟩]

end Stacks.DerivedLimit

namespace Stacks.SmallDerivedCategory

/-! ### The canonical truncations and an object property -/

section Truncation

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]

variable (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]

end Truncation

/-! ### The upper bound on a single module and on a bounded object -/

section Single

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]
  (R : DerivedCategory A ⥤ DerivedCategory B) [R.CommShift ℤ]
  (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ R)
  (hcomp : ∀ I : CochainComplex A ℤ, I.IsKInjective →
    IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))

end Single

section Bounded

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  (R : DerivedCategory A ⥤ DerivedCategory B) [R.CommShift ℤ] [R.IsTriangulated]
  (d : ℤ)
  (hSingle : ∀ M, P M → ∀ n : ℤ,
    (R.obj ((DerivedCategory.singleFunctor A n).obj M)).IsLE (n + d))

end Bounded

/-! ### The upper bound at a derived limit -/

section Products

variable {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
  [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]
  [HasProductsOfShape ℕ (DerivedCategory B)]

end Products

end Stacks.SmallDerivedCategory

/-! ### Stacks 08D4 for a scheme -/

namespace AlgebraicGeometry

open Stacks.DerivedLimit Stacks.SmallDerivedCategory

attribute [local instance] HasDerivedCategory.standard

/-- Quasi-coherence holds of a zero module over a sheaf of rings on a topological space: the free
module on the empty index set is zero and is quasi-coherent. -/
theorem containsZero_isQuasicoherent_of_sheaf {T : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}) :
    (SheafOfModules.isQuasicoherent R).ContainsZero := by
  refine ⟨SheafOfModules.free (R := R) (PEmpty : Type u), ?_, inferInstance⟩
  rw [IsZero.iff_id_eq_zero]
  exact Sigma.hom_ext _ _ (fun n ↦ n.elim)

section Bounds

variable (X : Scheme.{u}) {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
  [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]
  (F : SheafOfModules.{u} X.ringCatSheaf ⥤ B) [F.Additive]
  [PreservesLimitsOfShape (Discrete ℕ) F]
  (RF : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤ DerivedCategory B)
  (alpha : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor alpha
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))]

end Bounds

end AlgebraicGeometry

end
