module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDirectSums
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionModule
public import StacksFrontier.Algebra.DifferentialGraded.Module.Bijective
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryCoproducts

/-!
# Taking sections over an object of a chaotic site commutes with direct sums

Let `C` be a category with the chaotic topology, `O` a sheaf of rings on it and `(A, d)` a sheaf
of differential graded `O`-algebras. Direct sums of differential graded `A`-modules are formed
degreewise on the underlying sheaves of modules, and on a chaotic site evaluation at an object
`U` commutes with colimits. So the sections over `U` of a direct sum `⨁ⱼ Mⱼ` are, degree by
degree, the direct sum of the sections of the `Mⱼ`, and the differential graded `A(U)`-module
`(⨁ⱼ Mⱼ)(U)`, with the sections of the coprojections, is a direct sum of the `Mⱼ(U)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.isColimit_sectionsPieceCofan`: in each degree, the
  sections over `U` of a direct sum are a direct sum of abelian groups.
* `SheafOfModules.DifferentialGradedModule.isColimit_sectionModuleCofan`: **the sections over
  `U` of a direct sum of differential graded modules are a direct sum of differential graded
  `A(U)`-modules.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t a v u

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra
  Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{v} C] {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R} {J : Type a} [DecidableEq J]
  (M : J → DifferentialGradedModule.{t, a, a} A) (U : Cᵒᵖ)

/-- **In each degree the sections over `U` of a direct sum are the direct sum of the sections**,
as abelian groups: the degree-`n` piece of `⨁ⱼ Mⱼ` is the direct sum of the degree-`n` pieces,
and evaluation at `U` commutes with direct sums on a chaotic site. -/
def isColimit_sectionsPieceCofan (n : ℤ) :
    IsColimit (Cofan.mk (AddCommGrpCat.of ((∐ M).sectionsPiece U n)) fun j ↦
      AddCommGrpCat.ofHom (sectionMapApp (Sigma.ι M j) U n)) := by
  have := Stacks.SheafOfModules.preservesColimitsOfShape_evaluation R U (Discrete J)
  exact isColimitCofanMkObjOfIsColimit
    (_root_.SheafOfModules.evaluation.{a} R U ⋙
      forget₂ (ModuleCat.{a} (R.obj.obj U)) AddCommGrpCat.{a}) _ _
    (coproductIsColimit_degree A M n)

/-- The sections of the coprojections of the degree-`n` piece of a direct sum, read in the direct
sum of the total sections of the summands. -/
def sectionsPieceToDirectSum (n : ℤ) :
    AddCommGrpCat.of ((∐ M).sectionsPiece U n) ⟶
      AddCommGrpCat.of (DirectSum J fun j ↦ (M j).totalSections U) :=
  Cofan.IsColimit.desc (isColimit_sectionsPieceCofan M U n) fun j ↦
    AddCommGrpCat.ofHom ((DirectSum.of (fun j ↦ (M j).totalSections U) j).comp
      (DirectSum.of ((M j).sectionsPiece U) n))

/-- `sectionsPieceToDirectSum` sends the image of a degree-`n` section `y` of `M j` under the
`j`-th coprojection to `y`, placed in degree `n` of the `j`-th summand. -/
theorem sectionsPieceToDirectSum_sectionMapApp (n : ℤ) (j : J) (y : (M j).sectionsPiece U n) :
    (sectionsPieceToDirectSum M U n).hom (sectionMapApp (Sigma.ι M j) U n y) =
      DirectSum.of (fun j ↦ (M j).totalSections U) j
        (DirectSum.of ((M j).sectionsPiece U) n y) := by
  have h := Cofan.IsColimit.fac (isColimit_sectionsPieceCofan M U n) (fun j ↦
    AddCommGrpCat.ofHom ((DirectSum.of (fun j ↦ (M j).totalSections U) j).comp
      (DirectSum.of ((M j).sectionsPiece U) n))) j
  exact congrArg (fun φ ↦ AddCommGrpCat.Hom.hom φ y) h

/-- The inverse of the comparison of the sections of a direct sum with the direct sum of the
sections, as an additive map. -/
def sectionsToDirectSum :
    (∐ M).totalSections U →+ DirectSum J fun j ↦ (M j).totalSections U :=
  DirectSum.toAddMonoid fun n ↦ (sectionsPieceToDirectSum M U n).hom

/-- The comparison of the direct sum of the sections with the sections of a direct sum, as an
additive map: the sections of the coprojections. -/
def directSumSectionsAdd :
    (DirectSum J fun j ↦ (M j).totalSections U) →+ (∐ M).totalSections U :=
  DirectSum.toAddMonoid fun j ↦ sectionMapAdd (Sigma.ι M j) U

/-- `sectionsToDirectSum` is a left inverse of `directSumSectionsAdd`. -/
theorem sectionsToDirectSum_directSumSectionsAdd
    (x : DirectSum J fun j ↦ (M j).totalSections U) :
    sectionsToDirectSum M U (directSumSectionsAdd M U x) = x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | of j y =>
      rw [directSumSectionsAdd, DirectSum.toAddMonoid_of]
      induction y using DirectSum.induction_on with
      | zero => rw [map_zero, map_zero, map_zero]
      | add y z hy hz => rw [map_add, map_add, hy, hz, map_add]
      | of n p =>
          rw [sectionMapAdd_of, sectionsToDirectSum, DirectSum.toAddMonoid_of,
            sectionsPieceToDirectSum_sectionMapApp]

/-- `sectionsToDirectSum` is a right inverse of `directSumSectionsAdd`. -/
theorem directSumSectionsAdd_sectionsToDirectSum (z : (∐ M).totalSections U) :
    directSumSectionsAdd M U (sectionsToDirectSum M U z) = z := by
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | of n w =>
      rw [sectionsToDirectSum, DirectSum.toAddMonoid_of]
      have h : (sectionsPieceToDirectSum M U n) ≫
          AddCommGrpCat.ofHom (directSumSectionsAdd M U) =
          AddCommGrpCat.ofHom (DirectSum.of ((∐ M).sectionsPiece U) n) := by
        refine Cofan.IsColimit.hom_ext (isColimit_sectionsPieceCofan M U n) _ _ fun j ↦ ?_
        refine AddCommGrpCat.ext fun y ↦ ?_
        change directSumSectionsAdd M U ((sectionsPieceToDirectSum M U n).hom
          (sectionMapApp (Sigma.ι M j) U n y)) = DirectSum.of _ n (sectionMapApp _ U n y)
        rw [sectionsPieceToDirectSum_sectionMapApp, directSumSectionsAdd,
          DirectSum.toAddMonoid_of, sectionMapAdd_of]
      exact ConcreteCategory.congr_hom h w

/-- **The comparison of the direct sum of the sections with the sections of a direct sum**, the
descent of the sections of the coprojections. -/
def directSumSectionsDesc :
    _root_.DifferentialGradedModule.directSumObj (fun j ↦ (M j).sectionModule U) ⟶
      (∐ M).sectionModule U :=
  _root_.DifferentialGradedModule.directSumDesc _ fun j ↦ sectionMap (Sigma.ι M j) U

/-- The underlying function of `directSumSectionsDesc` is `directSumSectionsAdd`. -/
theorem directSumSectionsDesc_toFun (x : DirectSum J fun j ↦ (M j).totalSections U) :
    (directSumSectionsDesc M U).toFun x = directSumSectionsAdd M U x := by
  induction x using DirectSum.induction_on with
  | zero => exact (map_zero (directSumSectionsDesc M U).toFun).trans (map_zero _).symm
  | add x y hx hy =>
      exact (map_add (directSumSectionsDesc M U).toFun x y).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
  | of j y =>
      exact (_root_.DifferentialGradedModule.directSumDescLinear_of
        (fun j ↦ (M j).sectionModule U) (fun j ↦ sectionMap (Sigma.ι M j) U) j y).trans
        (DirectSum.toAddMonoid_of (fun j ↦ sectionMapAdd (Sigma.ι M j) U) j y).symm

/-- **The sections over `U` of a direct sum of differential graded modules are the direct sum of
the sections**, with the sections of the coprojections as coprojections. -/
def isColimit_sectionModuleCofan :
    IsColimit (Cofan.mk ((∐ M).sectionModule U) fun j ↦ sectionMap (Sigma.ι M j) U) := by
  have hb' : Function.Bijective (directSumSectionsAdd M U) :=
    ⟨Function.LeftInverse.injective (g := sectionsToDirectSum M U)
      (sectionsToDirectSum_directSumSectionsAdd M U),
      Function.RightInverse.surjective (g := sectionsToDirectSum M U)
      (directSumSectionsAdd_sectionsToDirectSum M U)⟩
  have hb : Function.Bijective (directSumSectionsDesc M U).toFun := by
    have he : ((directSumSectionsDesc M U).toFun : _ → _) = directSumSectionsAdd M U :=
      funext (directSumSectionsDesc_toFun M U)
    rw [he]
    exact hb'
  have := _root_.DifferentialGradedModule.isIso_of_bijective _ hb
  refine IsColimit.ofIsoColimit
    (_root_.DifferentialGradedModule.isColimit_directSumObj fun j ↦ (M j).sectionModule U)
    (Cofan.ext (asIso (directSumSectionsDesc M U)) fun j ↦ ?_)
  exact _root_.DifferentialGradedModule.directSumInj_comp_directSumDesc _ _ j

end DifferentialGradedModule

end SheafOfModules

end
