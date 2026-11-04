module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackModel
public import StacksFrontier.AlgebraicGeometry.AffineChartLocalization.Basic

/-!
# The base-change presheaf of a module along `R ⟶ Γ(X, ⊤)`

Let `X` be a scheme, `φ : R ⟶ Γ(X, ⊤)` a ring map and `N` an `R`-module. The presheaf

`U ↦ Γ(X, U) ⊗_R N`

of `𝒪_X`-modules, the ring map `R → Γ(X, U)` being `φ` followed by restriction, is in general
not a sheaf. **Over an affine open `V` its sheafification unit is nevertheless bijective**: its
sections over `V` are already the sections of the associated sheaf.

## Main definitions

* `sectionsRingHom`: the ring map `R ⟶ Γ(X, U)`, `φ` followed by restriction.
* `basePresheaf`: the presheaf `U ↦ Γ(X, U) ⊗_R N` of `𝒪_X`-modules, whose sections over `U`
  are `(ModuleCat.extendScalars (sectionsRingHom φ U).hom).obj N` by definition
  (`basePresheaf_obj`) and whose restriction maps are the base changes of those of `𝒪_X`
  (`basePresheaf_map_tmul`).

## Main results

* `isLocalizedModule_basePresheaf`: for `V` affine and `g : Γ(X, V)`, the restriction
  `Γ(X, V) ⊗_R N → Γ(X, D(g)) ⊗_R N` is a localization away from `g`. It is the base change
  along `R → Γ(X, V)` of the localization `Γ(X, V) → Γ(X, D(g))`
  (`AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`), and localization commutes with
  `- ⊗_R N` (`IsLocalizedModule.rTensor`).
* `bijective_toSheafify_basePresheaf_app`: **the sheafification unit of `basePresheaf φ N` is
  bijective on the sections over an affine open**, by
  `Stacks.AlgebraicGeometry.AffineChartLocalization.bijective_toSheafify_app_of_isAffineOpen`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.AffineChartLocalization
open scoped TensorProduct

attribute [local instance] Stacks.AlgebraicGeometry.AffineChartLocalization.sectionsModule

universe u

namespace Stacks.AlgebraicGeometry.BaseChangePresheaf

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (φ : R ⟶ Γ(X, ⊤)) (N : ModuleCat.{u} R)

/-- The ring map `R ⟶ Γ(X, U)`: `φ` followed by restriction. -/
abbrev sectionsRingHom (U : X.Opens) : R ⟶ Γ(X, U) := φ ≫ X.presheaf.map (homOfLE le_top).op

/-- The ring maps `R ⟶ Γ(X, U)` commute with the restriction maps of `𝒪_X`. -/
theorem restrict_sectionsRingHom {U U' : X.Opens} (i : U' ⟶ U) (r : R) :
    (X.presheaf.map i.op).hom ((sectionsRingHom φ U).hom r) = (sectionsRingHom φ U').hom r := by
  show ((φ ≫ X.presheaf.map (homOfLE le_top).op) ≫ X.presheaf.map i.op).hom r = _
  rw [Category.assoc, ← Functor.map_comp]
  rfl

/-- The presheaf `U ↦ Γ(X, U) ⊗_R N` of `𝒪_X`-modules. -/
def basePresheaf : PresheafOfModules.{u} X.ringCatSheaf.obj where
  obj U := (ModuleCat.extendScalars (sectionsRingHom φ U.unop).hom).obj N
  map {U U'} i := Stacks.PullbackModel.baseChangeMap (sectionsRingHom φ U.unop).hom
    (sectionsRingHom φ U'.unop).hom (ρ := RingHom.id R) (σ := (X.presheaf.map i).hom)
    (fun r => restrict_sectionsRingHom φ i.unop r) (M := N) (M' := N) LinearMap.id
  map_id U := by
    refine Stacks.PullbackModel.extendScalars_hom_ext _ fun m => ?_
    change Stacks.PullbackModel.tmul _ ((X.presheaf.map (𝟙 U)).hom 1) m = _
    rw [map_one]
    rfl
  map_comp {U U' U''} i j := by
    refine Stacks.PullbackModel.extendScalars_hom_ext _ fun m => ?_
    change Stacks.PullbackModel.tmul _ ((X.presheaf.map (i ≫ j)).hom 1) m =
      Stacks.PullbackModel.tmul _ ((X.presheaf.map j).hom ((X.presheaf.map i).hom 1)) m
    rw [map_one, map_one, map_one]

/-- The sections of `basePresheaf φ N` over `U` are `Γ(X, U) ⊗_R N`. -/
theorem basePresheaf_obj (U : X.Opens) :
    (basePresheaf φ N).obj (op U) =
      (ModuleCat.extendScalars (sectionsRingHom φ U).hom).obj N := rfl

/-- The restriction maps of `basePresheaf φ N` on pure tensors. -/
theorem basePresheaf_map_tmul {U U' : X.Opens} (i : U' ⟶ U) (r : Γ(X, U)) (n : N) :
    (basePresheaf φ N).map i.op (Stacks.PullbackModel.tmul (sectionsRingHom φ U).hom r n) =
      Stacks.PullbackModel.tmul (sectionsRingHom φ U').hom (X.presheaf.map i.op r) n := rfl

section Localization

variable {V : X.Opens}

/-- Over an affine open `V`, `basePresheaf φ N` localizes on the basic opens of `V`. -/
theorem isLocalizedModule_basePresheaf (hV : IsAffineOpen V) (g : Γ(X, V)) {U : X.Opens}
    (hU : U = X.basicOpen g) (hUV : U ≤ V) :
    letI := presheafModuleOfLE (basePresheaf φ N) hUV
    IsLocalizedModule.Away g (presheafRestrictₗ (basePresheaf φ N) hUV) := by
  let : Algebra R Γ(X, V) := (sectionsRingHom φ V).hom.toAlgebra
  let : Algebra R Γ(X, U) := (sectionsRingHom φ U).hom.toAlgebra
  let : Algebra Γ(X, V) Γ(X, U) := (X.presheaf.map (homOfLE hUV).op).hom.toAlgebra
  have : IsLocalization.Away g Γ(X, U) := hV.isLocalization_of_eq_basicOpen g (homOfLE hUV) hU
  have : IsScalarTower R Γ(X, V) Γ(X, U) := ⟨fun r a b => by
    show (X.presheaf.map (homOfLE hUV).op).hom ((sectionsRingHom φ V).hom r * a) * b =
      (sectionsRingHom φ U).hom r * ((X.presheaf.map (homOfLE hUV).op).hom a * b)
    rw [map_mul, restrict_sectionsRingHom, mul_assoc]⟩
  have key := IsLocalizedModule.rTensor (R := R) (A := Γ(X, V)) (M := Γ(X, V))
    (M' := Γ(X, U)) (Submonoid.powers g) (N := N) (Algebra.linearMap Γ(X, V) Γ(X, U))
  exact key

/-- Over an affine open `V` the sheafification unit of `basePresheaf φ N` is bijective. -/
theorem bijective_toSheafify_basePresheaf_app {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Bijective (ConcreteCategory.hom
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) (basePresheaf φ N).presheaf).app
        (op V))) :=
  bijective_toSheafify_app_of_isAffineOpen (basePresheaf φ N) hV
    fun g _ hU hUV => isLocalizedModule_basePresheaf φ N hV g hU hUV

end Localization

end Stacks.AlgebraicGeometry.BaseChangePresheaf

end
