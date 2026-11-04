module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs
public import StacksFrontier.AlgebraicGeometry.RestrictionExact.OverExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction of the ideal sheaf along an open immersion

Let `j : U ⟶ V` be an open immersion of schemes and let `k : Z ⟶ U` be any morphism of
schemes. Write `I(f)` for the ideal sheaf of a morphism `f`, the kernel of `𝒪 ⟶ f_* 𝒪` read as
a morphism of sheaves of modules (`Stacks.ClosedImmersion.idealSheaf`). Then
`j^* I(k ≫ j) ≅ I(k)`, compatibly with the inclusions of the ideal sheaves into the structure
sheaves.

## Main definitions

* `Stacks.IdealSheafRestrict.unitModule`: the structure sheaf of a scheme as a module over
  itself.
* `Stacks.IdealSheafRestrict.structureMap`: the structure-sheaf map `𝒪_B ⟶ f_* 𝒪_A` of a
  morphism of schemes `f : A ⟶ B`, as a morphism of `𝒪_B`-modules.
* `Stacks.IdealSheafRestrict.restrictKernelStructureMapIso` and
  `Stacks.IdealSheafRestrict.pullbackKernelStructureMapIso`: the isomorphism
  `j^* I(k ≫ j) ≅ I(k)`, with `j^*` the restriction and the pullback of
  `AlgebraicGeometry.Scheme.Modules` respectively.
* `Stacks.IdealSheafRestrict.pullbackIdealSheafIso`: the isomorphism `j^* I(k ≫ j) ≅ I(k)` for
  `RingedSpaceModuleAdjunction.modulePullback` and `Stacks.ClosedImmersion.idealSheaf`.

## Main results

* `Stacks.IdealSheafRestrict.restrictStructureMapSquare`: the restriction along `j` of the
  structure-sheaf map of `k ≫ j` is the structure-sheaf map of `k`, up to the canonical
  identifications of its source and target.
* `Stacks.IdealSheafRestrict.preservesFiniteLimits_restrictFunctor`: restriction of sheaves
  of modules along an open immersion of schemes is left exact.
* `Stacks.IdealSheafRestrict.restrictKernelStructureMapIso_hom_comp_ι`,
  `Stacks.IdealSheafRestrict.pullbackKernelStructureMapIso_hom_comp_ι` and
  `Stacks.IdealSheafRestrict.pullbackIdealSheafIso_hom_comp_ι`: each isomorphism commutes with
  the inclusions of the two ideal sheaves into the two structure sheaves.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.IdealSheafRestrict

variable {U V Z : Scheme.{u}}

/-! ### The structure sheaf as a module, and the structure-sheaf map -/

/-- The structure sheaf of a scheme, regarded as a module over itself: the
`CategoryTheory.SheafOfModules.unit` of `AlgebraicGeometry.Scheme.ringCatSheaf`, as an object of
`X.Modules`. -/
noncomputable def unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The structure-sheaf map `𝒪_B ⟶ f_* 𝒪_A` of a morphism of schemes `f : A ⟶ B`, read as a
morphism of `𝒪_B`-modules. Its kernel is the ideal sheaf of `f`. -/
noncomputable def structureMap {A B : Scheme.{u}} (f : A ⟶ B) :
    unitModule B ⟶ (Scheme.Modules.pushforward f).obj (unitModule A) :=
  SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toLRSHom.toShHom)

/-- On sections, the structure-sheaf map of `f` is the map on sections of `f` itself. -/
theorem structureMap_app {A B : Scheme.{u}} (f : A ⟶ B) (O : B.Opens) (x : Γ(B, O)) :
    (structureMap f).app O x = f.app O x :=
  rfl

/-- The ideal sheaf of `f` is the kernel of `structureMap f`. -/
theorem kernel_structureMap {A B : Scheme.{u}} (f : A ⟶ B) :
    kernel (structureMap f) = Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom :=
  rfl

/-- The structure-sheaf map of a composite `f ≫ g`, with its target read as the iterated
pushforward `g_* (f_* 𝒪)`. -/
noncomputable def structureMapComp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    unitModule C ⟶ (Scheme.Modules.pushforward g).obj
      ((Scheme.Modules.pushforward f).obj (unitModule A)) :=
  structureMap (f ≫ g)

/-- `structureMapComp` is the structure-sheaf map of the composite. -/
theorem structureMapComp_eq {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    structureMapComp f g = structureMap (f ≫ g) :=
  rfl

/-! ### The square -/

/-- Over an open `W` of `U`, the map on sections of `k ≫ j` on the image `j ''ᵁ W`, restricted
back to `k ⁻¹ᵁ W`, is the map on sections of `k` precomposed with the isomorphism
`AlgebraicGeometry.Scheme.Hom.appIso`. -/
theorem appIso_hom_comp_app (j : U ⟶ V) [IsOpenImmersion j] (k : Z ⟶ U) (W : U.Opens) :
    (k ≫ j).app (j ''ᵁ W) ≫ Z.presheaf.map ((Opens.map k.base).map
        (eqToHom (j.preimage_image_eq W).symm)).op =
      (j.appIso W).hom ≫ k.app W := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.app_eq_appLE k, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE]
  rfl

/-- Restriction along an open immersion carries the structure sheaf of the target to the
structure sheaf of the source. -/
noncomputable def restrictUnitModuleIso (j : U ⟶ V) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).obj (unitModule V) ≅ unitModule U :=
  Scheme.Modules.restrictUnitIso j

/-- Over an open `W`, `restrictUnitModuleIso` is `AlgebraicGeometry.Scheme.Hom.appIso`. -/
theorem restrictUnitModuleIso_hom_app (j : U ⟶ V) [IsOpenImmersion j] (W : U.Opens)
    (x : Γ(V, j ''ᵁ W)) :
    (restrictUnitModuleIso j).hom.app W x = (j.appIso W).hom x :=
  rfl

/-- The restriction along `j` of the pushforward along `j` of `k_* 𝒪_Z` is `k_* 𝒪_Z`, by the
counit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`. -/
noncomputable def restrictPushforwardIso (j : U ⟶ V) [IsOpenImmersion j] (k : Z ⟶ U) :
    (Scheme.Modules.restrictFunctor j).obj
        ((Scheme.Modules.pushforward j).obj
          ((Scheme.Modules.pushforward k).obj (unitModule Z))) ≅
      (Scheme.Modules.pushforward k).obj (unitModule Z) :=
  asIso ((Scheme.Modules.restrictAdjunction j).counit.app
    ((Scheme.Modules.pushforward k).obj (unitModule Z)))

/-- The restriction of the structure-sheaf map of `k ≫ j` is that of `k`: the square
```
j^* 𝒪_V ----- j^*(structureMap (k ≫ j)) -----> j^* ((k ≫ j)_* 𝒪_Z)
  |                                                  |
  v                                                  v
 𝒪_U -------- structureMap k ------------------> k_* 𝒪_Z
```
commutes, the two vertical maps being `restrictUnitModuleIso` and `restrictPushforwardIso`. -/
theorem restrictStructureMapSquare (j : U ⟶ V) [IsOpenImmersion j] (k : Z ⟶ U) :
    (Scheme.Modules.restrictFunctor j).map (structureMapComp k j) ≫
        (restrictPushforwardIso j k).hom =
      (restrictUnitModuleIso j).hom ≫ structureMap k := by
  ext W x
  exact congr($(appIso_hom_comp_app j k W) x)

/-! ### Left exactness of restriction, and the isomorphism of ideal sheaves -/

/-- Restriction of sheaves of modules along an open immersion of schemes is left exact. -/
@[sga "4 IV 11.2.2" "special case", sga "4 IV 13.7" "special case"]
instance preservesFiniteLimits_restrictFunctor (j : U ⟶ V) [IsOpenImmersion j] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor j) :=
  Stacks.AlgebraicGeometry.RestrictionExact.preservesFiniteLimits_pushforward _

/-- The restriction along `j` of the kernel of the structure-sheaf map of `k ≫ j` is the
kernel of the structure-sheaf map of `k`. -/
noncomputable def restrictKernelStructureMapIso (j : U ⟶ V) [IsOpenImmersion j] (k : Z ⟶ U) :
    (Scheme.Modules.restrictFunctor j).obj (kernel (structureMapComp k j)) ≅
      kernel (structureMap k) :=
  (PreservesKernel.iso (Scheme.Modules.restrictFunctor j) (structureMapComp k j)).trans
    (kernel.mapIso ((Scheme.Modules.restrictFunctor j).map (structureMapComp k j))
      (structureMap k) (restrictUnitModuleIso j) (restrictPushforwardIso j k)
      (restrictStructureMapSquare j k))

/-- `restrictKernelStructureMapIso` commutes with the inclusions of the two ideal sheaves into
the two structure sheaves. -/
theorem restrictKernelStructureMapIso_hom_comp_ι (j : U ⟶ V) [IsOpenImmersion j]
    (k : Z ⟶ U) :
    (restrictKernelStructureMapIso j k).hom ≫ kernel.ι (structureMap k) =
      (Scheme.Modules.restrictFunctor j).map (kernel.ι (structureMapComp k j)) ≫
        (restrictUnitModuleIso j).hom := by
  rw [restrictKernelStructureMapIso, Iso.trans_hom, Category.assoc, kernel.mapIso_hom,
    kernel.lift_ι, ← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι]

/-! ### The pullback form -/

/-- The pullback along `j` of the kernel of the structure-sheaf map of `k ≫ j` is the kernel
of the structure-sheaf map of `k`. -/
noncomputable def pullbackKernelStructureMapIso (j : U ⟶ V) [IsOpenImmersion j] (k : Z ⟶ U) :
    (Scheme.Modules.pullback j).obj (kernel (structureMapComp k j)) ≅
      kernel (structureMap k) :=
  ((Scheme.Modules.restrictFunctorIsoPullback j).app
      (kernel (structureMapComp k j))).symm.trans (restrictKernelStructureMapIso j k)

/-- The pullback along `j` of the structure sheaf of `V` is the structure sheaf of `U`. -/
noncomputable def pullbackUnitModuleIso (j : U ⟶ V) [IsOpenImmersion j] :
    (Scheme.Modules.pullback j).obj (unitModule V) ≅ unitModule U :=
  ((Scheme.Modules.restrictFunctorIsoPullback j).app (unitModule V)).symm.trans
    (restrictUnitModuleIso j)

/-- `pullbackKernelStructureMapIso` commutes with the inclusions of the two ideal sheaves into
the two structure sheaves. -/
theorem pullbackKernelStructureMapIso_hom_comp_ι (j : U ⟶ V) [IsOpenImmersion j]
    (k : Z ⟶ U) :
    (pullbackKernelStructureMapIso j k).hom ≫ kernel.ι (structureMap k) =
      (Scheme.Modules.pullback j).map (kernel.ι (structureMapComp k j)) ≫
        (pullbackUnitModuleIso j).hom := by
  rw [pullbackKernelStructureMapIso, pullbackUnitModuleIso, Iso.trans_hom, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_hom, Category.assoc, restrictKernelStructureMapIso_hom_comp_ι,
    ← Category.assoc, ← Category.assoc]
  congr 1
  exact ((Scheme.Modules.restrictFunctorIsoPullback j).inv.naturality
    (kernel.ι (structureMapComp k j))).symm

/-- For an open immersion `j : U ⟶ V` and an arbitrary morphism `k : Z ⟶ U`, the module
pullback along `j` of the ideal sheaf of `k ≫ j` is the ideal sheaf of `k`. -/
noncomputable def pullbackIdealSheafIso (j : U ⟶ V) [IsOpenImmersion j] (k : Z ⟶ U) :
    (modulePullback j.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf (k ≫ j).toLRSHom.toShHom) ≅
      Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom :=
  pullbackKernelStructureMapIso j k

/-- The module pullback along `j` of the structure sheaf of `V` is the structure sheaf of
`U`. -/
noncomputable def pullbackUnitIso (j : U ⟶ V) [IsOpenImmersion j] :
    (modulePullback j.toLRSHom.toShHom).obj
        (SheafOfModules.unit (structureSheafRing V.toSheafedSpace)) ≅
      SheafOfModules.unit (structureSheafRing U.toSheafedSpace) :=
  pullbackUnitModuleIso j

/-- `pullbackIdealSheafIso` commutes with the inclusions of the two ideal sheaves into the
two structure sheaves. -/
theorem pullbackIdealSheafIso_hom_comp_ι (j : U ⟶ V) [IsOpenImmersion j] (k : Z ⟶ U) :
    (pullbackIdealSheafIso j k).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom k.toLRSHom.toShHom)) =
      (modulePullback j.toLRSHom.toShHom).map
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom (k ≫ j).toLRSHom.toShHom))) ≫
        (pullbackUnitIso j).hom :=
  pullbackKernelStructureMapIso_hom_comp_ι j k

end Stacks.IdealSheafRestrict

end
