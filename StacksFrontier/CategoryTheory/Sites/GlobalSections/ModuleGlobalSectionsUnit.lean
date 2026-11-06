module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef

/-!
# Global sections of sheaves of modules are corepresented by the tensor unit

Let `R` be a commutative ring and `J` a Grothendieck topology on a category `C` whose objects
form a `Type u`. Sheaves of `R`-modules are taken with values in `ModuleCat.{max u w} R`, the
smallest universe containing both the ring `R : Type w` and the objects of the site, so that
morphisms of sheaves form a `Type (max u w)` again. There the ring itself is too small to be a
module, and the constant sheaf `R_C` is the constant sheaf on `ULift R`.

Global sections are corepresented by `R_C`: a morphism `R_C ⟶ F` is a morphism
`ULift R ⟶ Γ(F)` of `R`-modules by the constant sheaf adjunction, hence its value at `1`. So the
right derived functors of global sections are the `Ext`-groups out of `R_C`, and for the tensor
product of `CategoryTheory.Sheaf.monoidalCategory` (with the large-universe structure
`ModuleCat.liftedModuleMonoidal` on the coefficients) the tensor unit *is* `R_C`. This is what
identifies the cohomology groups of a sheaf of modules with the groups `Ext^i(𝟙, F)` on which the
cup product `Stacks.ExtCup.cup` is defined.

## Main definitions

* `Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv`: `Hom_R(ULift R, N) ≃+ N`.
* `Stacks.Cohomology.GlobalSections.constantModuleSheaf`: the constant sheaf `R_C`.
* `Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation`: global sections of
  sheaves of `R`-modules, read in abelian groups, are corepresented by `R_C`.
* `Stacks.Cohomology.GlobalSections.extConstantModuleSheafIsoRightDerived`:
  `Ext^n(R_C, -) ≅ Hⁿ(C, -)` read in abelian groups.
* `Stacks.Cohomology.GlobalSections.tensorUnitIsoConstantModuleSheaf`: the tensor unit of sheaves
  of modules is `R_C`.
* `Stacks.Cohomology.GlobalSections.extTensorUnitIsoRightDerived`: `Ext^n(𝟙, -) ≅ Hⁿ(C, -)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite MonoidalCategory

universe w v u

namespace Stacks.Cohomology.GlobalSections

variable (R : Type w) [CommRing R]

/-- **Linear maps out of the ring are their value at `1`**, for the ring lifted into a larger
universe. -/
def moduleULiftHomAddEquiv (N : ModuleCat.{max u w} R) :
    (ModuleCat.of R (ULift.{u} R) ⟶ N) ≃+ N where
  toFun f := f (ULift.up 1)
  invFun n := ModuleCat.ofHom
    ((LinearMap.toSpanSingleton R N n).comp ULift.moduleEquiv.toLinearMap)
  left_inv f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    obtain ⟨x⟩ := x
    change x • f.hom (ULift.up 1) = f.hom (ULift.up x)
    rw [← map_smul]
    congr 1
    exact ULift.ext (mul_one x)
  right_inv n := by
    change (1 : R) • n = n
    exact one_smul R n
  map_add' _ _ := rfl

/-- `moduleULiftHomAddEquiv` sends a linear map `f` to its value `f (ULift.up 1)`. -/
@[simp]
theorem moduleULiftHomAddEquiv_apply (N : ModuleCat.{max u w} R)
    (f : ModuleCat.of R (ULift.{u} R) ⟶ N) :
    moduleULiftHomAddEquiv.{w, u} R N f = f (ULift.up 1) :=
  rfl

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **The constant sheaf `R_C`** of sheaves of `R`-modules, on `ULift R` since `R` is too small to
be an object of `ModuleCat.{max u w} R`. -/
abbrev constantModuleSheaf [HasWeakSheafify J (ModuleCat.{max u w} R)] :
    Sheaf J (ModuleCat.{max u w} R) :=
  (constantSheaf J (ModuleCat.{max u w} R)).obj (ModuleCat.of R (ULift.{u} R))

section Corepresentation

variable [HasSheafify J (ModuleCat.{max u w} R)]
  [HasGlobalSectionsFunctor J (ModuleCat.{max u w} R)]

/-- Global sections of sheaves of modules are additive, being a right adjoint and hence
preserving binary products. -/
theorem additive_moduleΓ : (Sheaf.Γ J (ModuleCat.{max u w} R)).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] additive_moduleΓ

/-- The constant sheaf functor on modules is additive, being left adjoint to an additive
functor. -/
theorem additive_constantModuleSheaf : (constantSheaf J (ModuleCat.{max u w} R)).Additive :=
  (constantSheafΓAdj J (ModuleCat.{max u w} R)).left_adjoint_additive

attribute [local instance] additive_constantModuleSheaf

/-- **Global sections of sheaves of `R`-modules are corepresented by the constant sheaf `R_C`**,
read in abelian groups: a morphism `R_C ⟶ F` is a morphism `ULift R ⟶ Γ(F)` by the constant sheaf
adjunction, hence its value at `1`. -/
def moduleGlobalSectionsCorepresentation :
    Sheaf.Γ J (ModuleCat.{max u w} R) ⋙ forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w} ≅
      preadditiveCoyoneda.obj (op (constantModuleSheaf R J)) := by
  refine (NatIso.ofComponents (fun F =>
    (((constantSheafΓAdj J (ModuleCat.{max u w} R)).homAddEquiv
        (ModuleCat.of R (ULift.{u} R)) F).trans
      (moduleULiftHomAddEquiv.{w, u} R _)).toAddCommGrpIso) ?_).symm
  intro F G map
  ext element
  change ((constantSheaf J (ModuleCat.{max u w} R)).obj
    (ModuleCat.of R (ULift.{u} R)) ⟶ F) at element
  change ((constantSheafΓAdj J (ModuleCat.{max u w} R)).homEquiv _ G (element ≫ map))
      (ULift.up (1 : R)) =
    ((Sheaf.Γ J (ModuleCat.{max u w} R)).map map)
      (((constantSheafΓAdj J (ModuleCat.{max u w} R)).homEquiv _ F element) (ULift.up (1 : R)))
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- The value of the corepresentation at a section `s : R_C ⟶ F` is the global section it picks
out, `s` read through the constant sheaf adjunction and evaluated at `1`. -/
theorem moduleGlobalSectionsCorepresentation_inv_app_apply (F : Sheaf J (ModuleCat.{max u w} R))
    (s : constantModuleSheaf R J ⟶ F) :
    (moduleGlobalSectionsCorepresentation R J).inv.app F s =
      ((constantSheafΓAdj J (ModuleCat.{max u w} R)).homEquiv _ F s) (ULift.up (1 : R)) :=
  rfl

variable [HasExt.{max u w} (Sheaf J (ModuleCat.{max u w} R))]
  [HasInjectiveResolutions (Sheaf J (ModuleCat.{max u w} R))]

/-- Global sections of sheaves of modules preserve limits, being a right adjoint. -/
instance preservesLimits_moduleΓ :
    PreservesLimitsOfSize.{v, u} (Sheaf.Γ J (ModuleCat.{max u w} R)) :=
  (constantSheafΓAdj J (ModuleCat.{max u w} R)).rightAdjoint_preservesLimits

/-- **`Ext` out of the constant sheaf `R_C` is sheaf cohomology**: for every `n` and every sheaf
of `R`-modules `F`, `Ext^n(R_C, F) ≅ Hⁿ(C, F)`, read in abelian groups, naturally in `F`. -/
def extConstantModuleSheafIsoRightDerived (n : ℕ) :
    extFunctorObj (constantModuleSheaf R J) n ≅
      (Sheaf.Γ J (ModuleCat.{max u w} R)).rightDerived n ⋙
        forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w} :=
  have : PreservesFiniteLimits (Sheaf.Γ J (ModuleCat.{max u w} R) ⋙
      forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w}) :=
    comp_preservesFiniteLimits _ _
  ModuleSheafCohomology.extFunctorObjIsoRightDerived _ _
      (moduleGlobalSectionsCorepresentation R J) n ≪≫
    Functor.rightDerivedCompIso _ _ n

end Corepresentation

section Unit

variable [HasSheafify J (ModuleCat.{max u w} R)]
  [(J.W (A := ModuleCat.{max u w} R)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

/-- **The tensor unit of sheaves of `R`-modules is the constant sheaf `R_C`**: it is the
sheafification of the constant presheaf on the unit `ULift R` of `ModuleCat.{max u w} R`. -/
def tensorUnitIsoConstantModuleSheaf :
    𝟙_ (Sheaf J (ModuleCat.{max u w} R)) ≅ constantModuleSheaf R J :=
  Iso.refl _

variable [HasGlobalSectionsFunctor J (ModuleCat.{max u w} R)]
  [HasExt.{max u w} (Sheaf J (ModuleCat.{max u w} R))]
  [HasInjectiveResolutions (Sheaf J (ModuleCat.{max u w} R))]

attribute [local instance] additive_moduleΓ

/-- **`Ext` out of the tensor unit is sheaf cohomology**: `Ext^n(𝟙, F) ≅ Hⁿ(C, F)` for sheaves of
`R`-modules, read in abelian groups, naturally in `F`. These are the groups on which the cup
product `Stacks.ExtCup.cup` is defined. -/
def extTensorUnitIsoRightDerived (n : ℕ) :
    extFunctorObj (𝟙_ (Sheaf J (ModuleCat.{max u w} R))) n ≅
      (Sheaf.Γ J (ModuleCat.{max u w} R)).rightDerived n ⋙
        forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w} :=
  extConstantModuleSheafIsoRightDerived R J n

end Unit

end Stacks.Cohomology.GlobalSections

end
