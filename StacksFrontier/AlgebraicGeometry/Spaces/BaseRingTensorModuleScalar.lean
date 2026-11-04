module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModule
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraExtensionPushoutEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.GlobalSmulFunctoriality
public import StacksFrontier.CategoryTheory.Preadditive.ModuleCatFunctorEvalLinear
public import StacksFrontier.CategoryTheory.Sites.Modules.BaseRingTensorScalar

/-!
# `𝒪_X ⊗_R -` on an algebraic space respects scalars

For an algebraic space `X` with a base-ring datum `φ : R →+* Γ(model, 𝒪)`, the module
`𝒪_X ⊗_R M` of Stacks 0D3F (`AlgebraicGeometry.Space.baseRingTensorModule`), restricted back to
the model, carries multiplication by `c ∈ R` on `M` to multiplication by `c` in the `R`-linear
structure of modules on the model induced by `φ`. In the proof of
[Stacks Project, Tag 0D1K] this matches the action of `k` on `Ext¹(NL_{X/k}, 𝒪_X ⊗_k k)` through
`k ⊗ -` with the action through the structure morphism.

## Main results

* `AlgebraicGeometry.Space.baseRingTensorModule_comp_scalarMap`

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules Deformation.AlgebraExtension
open scoped IsMulCommutative

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)

/-- The rings of sections of the structure sheaf of the model are commutative. -/
local instance isMulCommutative_modelStructureRing_obj (V : (SmallEtaleModel B S hS X.1)ᵒᵖ) :
    IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf
      ((ringRes (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X).inverse).obj
        (structureSheaf B S hS X.1 X.2))).obj.obj V) :=
  ⟨⟨fun a b => mul_comm (G := (structureSheaf B S hS X.1 X.2).obj.obj
    (op ((smallEtaleModelEquiv B S hS X).inverse.obj V.unop))) a b⟩⟩

/-- The rings of sections of the structure sheaf of the model, read as a sheaf of rings, are
commutative. -/
local instance isMulCommutative_ringSheafOfSite_smallEtaleModelStructureSheaf_obj
    (V : (SmallEtaleModel B S hS X.1)ᵒᵖ) :
    IsMulCommutative ((ringSheafOfSite (smallEtaleModelStructureSheaf B S hS X)).obj.obj V) :=
  ⟨⟨fun a b => mul_comm (G := (structureSheaf B S hS X.1 X.2).obj.obj
    (op ((smallEtaleModelEquiv B S hS X).inverse.obj V.unop))) a b⟩⟩

/-- The rings of sections of the structure sheaf of the model, read through the dense subsite, are
commutative. -/
local instance isMulCommutative_modelRingRestriction_obj' (V : (SmallEtaleModel B S hS X.1)ᵒᵖ) :
    IsMulCommutative ((Stacks.DenseSubsiteModules.ringRestriction
      (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)
      (smallEtaleModelEquiv B S hS X).inverse (structureRingSheaf B S hS X)).obj.obj V) :=
  ⟨⟨fun a b => mul_comm (G := (structureSheaf B S hS X.1 X.2).obj.obj
    (op ((smallEtaleModelEquiv B S hS X).inverse.obj V.unop))) a b⟩⟩

/-- **`𝒪_X ⊗_R -`, restricted to the model, carries `c · 1` to `c · 1`**, for the `R`-linear
structure on modules on the model induced by the base-ring datum `φ`. -/
theorem baseRingTensorModule_comp_scalarMap (c : R) :
    letI := Stacks.SheafOfModules.linearOver (Stacks.SheafOfModules.Tensor.ringSheaf
      ((ringRes (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X).inverse).obj
        (structureSheaf B S hS X.1 X.2))) φ
    (baseRingTensorModule B S hS X φ ⋙ (modelModulesEquiv B S hS X).functor).scalarMap c =
      c • 𝟙 _ := by
  let : Linear R (_root_.SheafOfModules.{u} _) := Stacks.SheafOfModules.linearOver
    (Stacks.SheafOfModules.Tensor.ringSheaf
      ((ringRes (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X).inverse).obj
        (structureSheaf B S hS X.1 X.2))) φ
  let e := smallEtaleModelModulesEquiv B S hS X
  change e.functor.map (e.inverse.map ((baseRingTensorFunctor.{u, u, u, u} φ).map
    (c • 𝟙 (ModuleCat.of R R)))) = _
  rw [baseRingTensorFunctor_map_smul_id.{u, u, u, u} φ c (ModuleCat.of R R)]
  refine (e.fun_inv_map _ _ _).trans ?_
  let b : GlobalSectionRing (Stacks.DenseSubsiteModules.ringRestriction
      (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)
      (smallEtaleModelEquiv B S hS X).inverse (structureRingSheaf B S hS X)) :=
    ⟨(φ c).1, (φ c).2⟩
  change e.counit.app _ ≫ globalSmul _ b _ ≫ e.counitInv.app _ = _
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ e.counitInv.app _)
    (comp_globalSmul _ b (e.counit.app _)))).trans (((Category.assoc _ _ _).trans
      (congrArg (globalSmul _ b _ ≫ ·) (e.counitIso.hom_inv_id_app _))).trans
      ((Category.comp_id _).trans (Stacks.SheafOfModules.linearOver_smul_id _ φ _ c).symm))

end AlgebraicGeometry.Space

end
