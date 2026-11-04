module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic

/-!
# Constant sheaves on the small étale site

A constant abelian sheaf on a finite group is finite locally constant on any site (it is constant
on the slice at every object), hence constructible on Mathlib's small étale site: on the site of
Tag 021B it is again the constant sheaf, by
`Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso` along the dense subsite
inclusion. Restriction along an étale morphism takes the constant sheaf to the constant sheaf, by
the same lemma along the continuous and cocontinuous functor of composition with it.

## Main results

* `Stacks.EtaleCohomology.isFiniteLocallyConstant_constantSheaf_anyUniverse`.
* `Stacks.EtaleCohomology.isConstructibleEtaleSheaf_constantSheaf`.
* `Stacks.EtaleCohomology.etaleRestrictionConstantSheafIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w v u

namespace Stacks.EtaleCohomology

/-- **A constant sheaf on a finite group is finite locally constant.** -/
theorem isFiniteLocallyConstant_constantSheaf_anyUniverse {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{w}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [∀ (U : C) (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{w}),
      (Over.forget U).op.HasPointwiseRightKanExtension F]
    (M : AddCommGrpCat.{w}) [Finite M] :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant J
      ((constantSheaf J AddCommGrpCat.{w}).obj M) where
  exists_finite_cover U := by
    refine ⟨PUnit, fun _ => U, fun _ => 𝟙 U, ?_, fun _ => ⟨M, inferInstance,
      ⟨(Stacks.ConstantSheaf.overPullbackConstantSheafIso J AddCommGrpCat.{w} U).app M⟩⟩⟩
    exact J.superset_covering (fun _ f _ ↦ ⟨U, f, 𝟙 U, ⟨PUnit.unit⟩, Category.comp_id f⟩)
      (J.top_mem U)

/-- **A constant abelian sheaf on a finite group is constructible** on Mathlib's small étale
site. -/
theorem isConstructibleEtaleSheaf_constantSheaf (X : Scheme.{u}) (M : AddCommGrpCat.{u + 1})
    [Finite M] :
    IsConstructibleSmallEtaleSheaf
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  refine ⟨B, hX, ?_⟩
  have : ∀ X' : (X.Etale)ᵒᵖ, HasLimitsOfShape (StructuredArrow X'
      (SmallEtale.toEtaleSite B X hX).op) AddCommGrpCat.{u + 1} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  let e := (Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
    (SmallEtale.topology B X hX) X.smallEtaleTopology (SmallEtale.toEtaleSite B X hX)
    AddCommGrpCat.{u + 1}).app M
  have := isFiniteLocallyConstant_constantSheaf_anyUniverse (SmallEtale.topology B X hX) M
  exact isConstructibleAbelianSheaf_congr B (B.obj X hX) e.symm
    (isConstructibleAbelianSheaf_of_isFiniteLocallyConstant.{u + 1, u} B (B.obj X hX) _)

/-- **Restriction along an étale morphism takes the constant sheaf to the constant sheaf.** -/
def etaleRestrictionConstantSheafIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (M : AddCommGrpCat.{u + 1}) :
    (etaleRestriction.{u, u + 1} j).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) ≅
      (constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M :=
  have : ∀ X' : (X.Etale)ᵒᵖ, HasLimitsOfShape (StructuredArrow X'
      (Scheme.Etale.smallEtaleCompose j).op) AddCommGrpCat.{u + 1} :=
    fun _ ↦ inferInstance
  (Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
    U.smallEtaleTopology X.smallEtaleTopology (Scheme.Etale.smallEtaleCompose j)
    AddCommGrpCat.{u + 1}).app M

end Stacks.EtaleCohomology

end
