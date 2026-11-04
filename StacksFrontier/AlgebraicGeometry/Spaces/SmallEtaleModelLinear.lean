module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleEquiUniverseModel
public import StacksFrontier.CategoryTheory.Sites.Modules.GlobalSmulFunctoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Linear structures across the equi-universe model of the small étale site

Let `X` be an algebraic space and `Y` the equi-universe model of its small étale ringed site
(`AlgebraicGeometry.Space.smallEtaleModelRingedSite`), with the equivalence
`e : Mod(𝒪_X) ≌ Mod(𝒪_Y)` (`AlgebraicGeometry.Space.modulesEquivModelModules`).  A ring map
`θ : A →+* Γ(X, 𝒪_X)` induces one into `Γ(Y, 𝒪_Y)` (restriction of compatible families along the
model equivalence), hence `A`-linear structures on both module categories; this file shows that
`e` is `A`-linear and carries the structure sheaf to the structure sheaf, and records the
additivity and total-complex instances of the tensor product on `Y`.

## Main definitions

* `AlgebraicGeometry.Space.modelGlobalSectionRingHom`: `Γ(X, 𝒪_X) →+* Γ(Y, 𝒪_Y)`.
* `AlgebraicGeometry.Space.modulesEquivModelModulesUnitIso`: `e(𝒪_X) ≅ 𝒪_Y`.

## Main results

* `AlgebraicGeometry.Space.modulesEquivModelModules_map_globalSmul`: `e` carries multiplication by
  a global section to multiplication by its restriction.
* `AlgebraicGeometry.Space.modulesEquivModelModules_functor_linear`: `e` is `A`-linear.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace Stacks.SheafOfModules

universe w u₁ v₁ u₂ v₂

/-- A sheaf of rings with commutative sections stays so after reindexing along an equivalence of
sites. -/
instance isMulCommutative_reindexRing {C : Type u₁} [Category.{v₁} C] {C' : Type u₂}
    [Category.{v₂} C'] {J : GrothendieckTopology C} (J' : GrothendieckTopology C') (e : C' ≌ C)
    [e.functor.IsContinuous J' J] (R : Sheaf J RingCat.{w}) [∀ X, IsMulCommutative (R.obj.obj X)]
    (X : C'ᵒᵖ) : IsMulCommutative ((reindexRing J' e R).obj.obj X) :=
  inferInstanceAs (IsMulCommutative (R.obj.obj (op (e.functor.obj X.unop))))

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The sections of the structure sheaf of the small étale ringed site are commutative. -/
instance (X : (smallEtaleRingedSite B S hS F hF).Cᵒᵖ) :
    IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O).obj.obj X) :=
  ⟨⟨fun a b => mul_comm (G := (smallEtaleRingedSite B S hS F hF).O.obj.obj X) a b⟩⟩

/-- The sections of the structure sheaf of the equi-universe model are commutative. -/
instance (X : (smallEtaleModelRingedSite B S hS F hF).Cᵒᵖ) :
    IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleModelRingedSite B S hS F hF).O).obj.obj X) :=
  ⟨⟨fun a b => mul_comm (G := (smallEtaleModelRingedSite B S hS F hF).O.obj.obj X) a b⟩⟩

/-- **Global sections of `𝒪_X` restrict to global sections of the model ring.** -/
def modelGlobalSectionRingHom :
    GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) →+*
      GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) where
  toFun s := ⟨fun V => s.1 (op ((smallEtaleModelEquivalence B S hS F).functor.obj V.unop)),
    fun {_ _} f => s.2 ((smallEtaleModelEquivalence B S hS F).functor.map f.unop).op⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The model equivalence carries multiplication by a global section to multiplication by its
restriction.** -/
theorem modulesEquivModelModules_map_globalSmul
    (s : GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (M : Modules.{u, u} B S hS F hF) :
    (modulesEquivModelModules B S hS F hF).functor.map (globalSmul _ s M) =
      globalSmul _ (modelGlobalSectionRingHom B S hS F hF s)
        ((modulesEquivModelModules B S hS F hF).functor.obj M) := by
  ext U x
  rfl

variable {A : Type*} [CommRing A]
  (θ : A →+* GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))

/-- **The model equivalence is `A`-linear**, for the linear structures induced by `θ` and by its
restriction to the model. -/
theorem modulesEquivModelModules_functor_linear :
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) θ
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)
      ((modelGlobalSectionRingHom B S hS F hF).comp θ)
    (modulesEquivModelModules B S hS F hF).functor.Linear A :=
  Stacks.SheafOfModules.linear_of_map_globalSmul _ _ _ fun a M =>
    modulesEquivModelModules_map_globalSmul B S hS F hF (θ a) M

/-- The model equivalence is additive. -/
instance modulesEquivModelModules_functor_additive :
    (modulesEquivModelModules B S hS F hF).functor.Additive where
  map_add := by intros; ext; rfl

/-- **The model equivalence carries the structure sheaf to the structure sheaf.** -/
def modulesEquivModelModulesUnitIso :
    (modulesEquivModelModules B S hS F hF).functor.obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) :=
  haveI := Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit
    (Fun := (smallEtaleModelEquivalence B S hS F).functor)
    (𝟙 (Stacks.SheafOfModules.reindexRing (smallEtaleModelTopology B S hS F)
      (smallEtaleModelEquivalence B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
  (asIso (SheafOfModules.unitToPushforwardObjUnit.{u}
    (F := (smallEtaleModelEquivalence B S hS F).functor)
    (𝟙 (Stacks.SheafOfModules.reindexRing (smallEtaleModelTopology B S hS F)
      (smallEtaleModelEquivalence B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))))).symm

/-- The tensor product of modules on the model is additive in its first variable. -/
instance modelSheafTensorAdditive :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (smallEtaleModelRingedSite B S hS F hF).O).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u}
    (J := (smallEtaleModelRingedSite B S hS F hF).J) (smallEtaleModelRingedSite B S hS F hF).O

/-- The tensor product of modules on the model is additive in its second variable. -/
instance modelSheafTensorObjAdditive (M : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (smallEtaleModelRingedSite B S hS F hF).O).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
    (J := (smallEtaleModelRingedSite B S hS F hF).J) (smallEtaleModelRingedSite B S hS F hF).O M

/-- Modules on the model have colimits indexed by small types. -/
theorem modelModules_hasColimitsOfSize :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)) :=
  hasColimitsOfSizeShrink.{0, 0, u, u} _

/-- The total complexes of the tensor product of two complexes of modules on the model exist. -/
instance modelHasMapBifunctor (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O))
      (ComplexShape.up ℤ)) :
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleModelRingedSite B S hS F hF).O) (ComplexShape.up ℤ) :=
  fun _ => @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (modelModules_hasColimitsOfSize B S hS F hF) _ _) _

end AlgebraicGeometry.Space

end
