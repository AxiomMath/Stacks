module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangePresheaf

/-!
# The sheaf of modules attached to a module over the ring of a terminal object of a dense subsite

Let `v : C ⥤ C'` exhibit `(C, J)` as a dense subsite of `(C', K)`, let `R` be a sheaf of rings
on `(C', K)` whose section rings over `C` are commutative, and let `X` be a terminal object of
`C`. For an `R(v X)`-module `M` the presheaf `U ↦ R(v U) ⊗_{R(v X)} M` on `C` is
`Stacks.TerminalBaseChange.baseChangePresheaf`. When it is a sheaf for `J` — on a site of affine
schemes this is faithfully flat descent of modules — it extends uniquely, by the Comparison
Lemma for sheaves of modules, to a sheaf of `R`-modules `M^a` on `C'`.

This file constructs `M^a` and proves that the rule `M ↦ M^a` is left adjoint to taking sections
over `v X`, and that the sections of `M^a` over `v U` are `R(v U) ⊗_{R(v X)} M`. In particular
`M ↦ M^a` preserves colimits and carries `R(v X)` to the structure sheaf, so a module given by a
presentation `R^{(J)} ⟶ R^{(I)} ⟶ M ⟶ 0` goes to the cokernel of the corresponding morphism of
free sheaves of modules.

## Main definitions

* `Stacks.DenseSubsiteBaseChange.baseChangeSheaf`: the presheaf `U ↦ R(v U) ⊗ M` on `C`, as a
  sheaf of modules over the restriction of `R`.
* `Stacks.DenseSubsiteBaseChange.associatedSheaf`: the sheaf of `R`-modules `M^a` on `C'`.
* `Stacks.DenseSubsiteBaseChange.associatedSheafAdj`: `M ↦ M^a` is left adjoint to sections over
  `v X`.
* `Stacks.DenseSubsiteBaseChange.associatedSheafEvaluationIso`: the sections of `M^a` over `v U`
  are `R(v U) ⊗_{R(v X)} M`.
-/

@[expose] public section

universe w u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.DenseSubsiteModules Stacks.TerminalBaseChange

namespace Stacks.DenseSubsiteBaseChange

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsDenseSubsite J K]
  (R : Sheaf K RingCat.{w}) [CommSections (ringRestriction J K v R).obj]
  {X : C} (hX : IsTerminal X)

/-- The condition that the base change presheaf `U ↦ R(v U) ⊗_{R(v X)} M` on the subsite is a
sheaf for every module `M`. -/
def BaseChangeIsSheaf : Prop :=
  ∀ M : ModuleCat.{w} ((ringRestriction J K v R).obj.obj (op X)),
    Presheaf.IsSheaf J ((baseChangePresheaf.{w} (ringRestriction J K v R).obj hX).obj M).presheaf

variable {J K v R hX} (h : BaseChangeIsSheaf J K v R hX)

/-- The base change presheaf `U ↦ R(v U) ⊗_{R(v X)} M` on the subsite, as a sheaf of modules. -/
noncomputable def baseChangeSheaf :
    ModuleCat.{w} ((ringRestriction J K v R).obj.obj (op X)) ⥤
      SheafOfModules.{w} (ringRestriction J K v R) where
  obj M := ⟨(baseChangePresheaf.{w} (ringRestriction J K v R).obj hX).obj M, h M⟩
  map φ := ⟨(baseChangePresheaf.{w} (ringRestriction J K v R).obj hX).map φ⟩
  map_id M := SheafOfModules.hom_ext
    ((baseChangePresheaf.{w} (ringRestriction J K v R).obj hX).map_id M)
  map_comp φ ψ := SheafOfModules.hom_ext
    ((baseChangePresheaf.{w} (ringRestriction J K v R).obj hX).map_comp φ ψ)

/-- The base change sheaf followed by the forgetful functor to presheaves of modules is the base
change presheaf. -/
noncomputable def baseChangeSheafForgetIso :
    baseChangeSheaf h ⋙ SheafOfModules.forget.{w} (ringRestriction J K v R) ≅
      baseChangePresheaf.{w} (ringRestriction J K v R).obj hX :=
  Iso.refl _

/-- On the subsite, the base change sheaf is left adjoint to sections over the terminal
object. -/
noncomputable def baseChangeSheafAdj :
    baseChangeSheaf h ⊣ SheafOfModules.evaluation.{w} (ringRestriction J K v R) (op X) :=
  (baseChangeAdj.{w} (ringRestriction J K v R).obj hX).restrictFullyFaithful
    (iC := 𝟭 _) (iD := SheafOfModules.forget.{w} (ringRestriction J K v R))
    (Functor.FullyFaithful.id _) (SheafOfModules.fullyFaithfulForget _)
    (Functor.leftUnitor _ ≪≫ (baseChangeSheafForgetIso h).symm)
    (Iso.refl _ ≪≫ (Functor.rightUnitor _).symm)

variable [(v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence]

/-- **The sheaf of modules `M^a` on `C'` attached to an `R(v X)`-module `M`**: the unique
extension to `C'`, by the Comparison Lemma for sheaves of modules, of the base change sheaf
`U ↦ R(v U) ⊗_{R(v X)} M` on the dense subsite. -/
noncomputable def associatedSheaf :
    ModuleCat.{w} ((ringRestriction J K v R).obj.obj (op X)) ⥤ SheafOfModules.{w} R :=
  baseChangeSheaf h ⋙ (moduleRestrictionEquivalence J K v R).inverse

/-- The restriction of `M^a` to the dense subsite is the base change sheaf. -/
noncomputable def associatedSheafRestrictionIso :
    associatedSheaf h ⋙ moduleRestriction J K v R ≅ baseChangeSheaf h :=
  Functor.isoWhiskerLeft (baseChangeSheaf h) (moduleRestrictionEquivalence J K v R).counitIso ≪≫
    Functor.rightUnitor _

/-- **`M ↦ M^a` is left adjoint to sections over `v X`.** -/
noncomputable def associatedSheafAdj :
    associatedSheaf h ⊣ SheafOfModules.evaluation.{w} R (op (v.obj X)) :=
  (baseChangeSheafAdj h).comp (moduleRestrictionEquivalence J K v R).symm.toAdjunction

/-- **The sections of `M^a` over `v U` are `R(v U) ⊗_{R(v X)} M`.** -/
noncomputable def associatedSheafEvaluationIso (U : C) :
    associatedSheaf h ⋙ SheafOfModules.evaluation.{w} R (op (v.obj U)) ≅
      ModuleCat.extendScalars.{w, w, w}
        (rho (ringRestriction J K v R).obj hX (op U)) :=
  Functor.isoWhiskerRight (associatedSheafRestrictionIso h)
      (SheafOfModules.evaluation.{w} (ringRestriction J K v R) (op U)) ≪≫
    baseChangeEvaluationIso.{w} (ringRestriction J K v R).obj hX (op U)

/-- The functor `M ↦ M^a` preserves all colimits of size `w`. -/
instance associatedSheaf_preservesColimits :
    PreservesColimitsOfSize.{w, w} (associatedSheaf h) :=
  (associatedSheafAdj h).leftAdjoint_preservesColimits

end Stacks.DenseSubsiteBaseChange

end
