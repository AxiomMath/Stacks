module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleChartKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalModuleInverseImageKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceSquareZeroValues
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SharpCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceCommonTarget

/-!
# The map of conormal modules of a morphism of thickenings is read off its comorphism

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, with inclusion
`i : Z ⟶ X`, let `W₀ ⊆ W` be a closed subspace with inclusion `j : W₀ ⟶ W`, and let
`c : X ⟶ W` and `e₀ : Z ⟶ W₀` make the square `i ≫ c = e₀ ≫ j` commute.  The square has the map
`e₀^*𝒞_{W₀/W} ⟶ 𝒞_{Z/X}` of conormal modules of [Stacks Project, Tag 04CP]
(`AlgebraicGeometry.Space.conormalMap`).  This file shows that it is the map which the comorphism
of `c` induces on the defining ideals.

## Main results

* `AlgebraicGeometry.Space.homEquiv_conormalTranspose`: the transpose along `(i ≫ c)^* ⊣ (i ≫ c)_*`
  of `i^*` of the map of defining ideal sheaves, read through `(i ≫ c)^* ≅ i^* c^*`.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1) (c : X ⟶ W)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)

/-- Evaluating a composite of morphisms of sheaves of sets on a section is evaluating the two
factors in turn. -/
theorem setSheaf_comp_hom_app_apply {Cc : Type*} [Category Cc] {Jc : GrothendieckTopology Cc}
    {P Q R : Sheaf Jc (Type u)} (f : P ⟶ Q) (g : Q ⟶ R) (V : Ccᵒᵖ) (x : P.obj.obj V) :
    (f ≫ g).hom.app V x = g.hom.app V (f.hom.app V x) :=
  rfl

/-- Equal morphisms of modules on the small étale site of an algebraic space agree on every
local section. -/
theorem modules_val_app_congr {Y : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS Y.1 Y.2} {x y : M ⟶ N} (h : x = y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ) (t : M.val.obj U) :
    x.val.app U t = y.val.app U t :=
  congrArg (fun m : M ⟶ N ↦ m.val.app U t) h

/-- Evaluating a composite of morphisms of modules on a local section is evaluating the two
factors in turn. -/
theorem modules_comp_val_app {Y : AlgebraicSpaces B S hS}
    {M N P : Modules.{u, u} B S hS Y.1 Y.2} (a : M ⟶ N) (b : N ⟶ P)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ) (t : M.val.obj U) :
    (a ≫ b).val.app U t = b.val.app U (a.val.app U t) :=
  rfl

/-- **The transpose of `i^*` of the map of defining ideal sheaves.**  Along
`(i ≫ c)^* ⊣ (i ≫ c)_*`, read through the comparison `(i ≫ c)^* ≅ i^* c^*` of
[Stacks Project, Tag 03LU], it is the transpose `𝓘_W ⟶ c_*𝓘_Z` of the map of defining ideal sheaves,
followed by `c_*` of the unit `𝓘_Z ⟶ i_*i^*𝓘_Z` and by the comparison `c_*i_* ≅ (i ≫ c)_*`. -/
theorem homEquiv_conormalTranspose :
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z ≫ c)).homEquiv _ _
        ((modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).inv.app
            (definingIdealSheaf B S hS W W₀).toSheafOfModules ≫
          (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
            (idealSheafMap B S hS Z W₀ c e₀ hsq)) =
      ((modulePullbackAdjunction B S hS c).homEquiv _ _ (idealSheafMap B S hS Z W₀ c e₀ hsq) ≫
          (modulePushforward B S hS c).map
            ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
              (definingIdealSheaf B S hS X Z).toSheafOfModules)) ≫
        (modulePushforwardCompIso B S hS (subspaceInclusion B S hS X Z) c).hom.app
          ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
            (definingIdealSheaf B S hS X Z).toSheafOfModules) := by
  refine (homEquiv_modulePullbackCompIso_inv_app_comp B S hS (subspaceInclusion B S hS X Z) c
    (definingIdealSheaf B S hS W W₀).toSheafOfModules _
    ((modulePullback B S hS (subspaceInclusion B S hS X Z)).map
      (idealSheafMap B S hS Z W₀ c e₀ hsq))).trans ?_
  refine congrArg (· ≫ (modulePushforwardCompIso B S hS (subspaceInclusion B S hS X Z) c).hom.app
    ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
      (definingIdealSheaf B S hS X Z).toSheafOfModules)) ?_
  refine (congrArg ((modulePullbackAdjunction B S hS c).homEquiv _ _)
    ((Adjunction.homEquiv_unit _ _ _ _).trans
      ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit_naturality
        (idealSheafMap B S hS Z W₀ c e₀ hsq)))).trans ?_
  exact Adjunction.homEquiv_naturality_right _ _ _


section Core

variable (hZ : IsFirstOrderThickening B S hS X Z.1)

/-- **The conormal module of a first order thickening inside `i^{-1}𝒪_X`, as sheaves of sets.**
The inclusion `i_*𝒞_{Z/X} ⟶ 𝒪_X` of the pushed-forward conormal module
(`AlgebraicGeometry.Space.firstOrderConormalModuleι`) followed by the unit `𝒪_X ⟶ i_*i^{-1}𝒪_X`
is a morphism between two direct images along `i`, and the direct image of sheaves of sets along
a closed immersion is fully faithful ([Stacks Project, Tag 04E5]); this is its preimage. -/
noncomputable def conormalSetInclusion :
    (CategoryTheory.Sheaf.moduleSheafFunctor
        (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).obj
        (conormalModule B S hS X Z) ⟶
      (sheafCompose (SmallEtale.topology B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
        (CategoryTheory.forget RingCat.{u})).obj
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) :=
  (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS (subspaceInclusion B S hS X Z)
      Z.2.2).preimage
    (X := (CategoryTheory.Sheaf.moduleSheafFunctor
        (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).obj
        (conormalModule B S hS X Z))
    (Y := (sheafCompose (SmallEtale.topology B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
        (CategoryTheory.forget RingCat.{u})).obj
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    ((CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (firstOrderConormalModuleι B S hS Z hZ) ≫
      (sheafCompose (SmallEtale.topology B S hS X.1) (CategoryTheory.forget RingCat.{u})).map
        (thickeningRingUnit B S hS Z))

/-- The direct image along `i` of `AlgebraicGeometry.Space.conormalSetInclusion` is the
inclusion `i_*𝒞_{Z/X} ⟶ 𝒪_X` followed by the unit `𝒪_X ⟶ i_*i^{-1}𝒪_X`. -/
theorem map_conormalSetInclusion :
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        (conormalSetInclusion B S hS Z hZ) =
      (CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          (firstOrderConormalModuleι B S hS Z hZ) ≫
        (sheafCompose (SmallEtale.topology B S hS X.1) (CategoryTheory.forget RingCat.{u})).map
          (thickeningRingUnit B S hS Z) :=
  (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS (subspaceInclusion B S hS X Z)
      Z.2.2).map_preimage _

/-- **The unit `𝓘_Z ⟶ i_*i^*𝓘_Z`, followed by the direct image of the conormal inclusion, is the
unit `𝒪_X ⟶ i_*i^{-1}𝒪_X` on the defining ideal**, on sections. -/
theorem map_conormalSetInclusion_unit (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U) :
    ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        (conormalSetInclusion B S hS Z hZ)).hom.app U
        (((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules).val.app U t) =
      (thickeningRingUnit B S hS Z).hom.app U ((definingIdealSheaf B S hS X Z).ι.val.app U t) :=
  (setSheafHom_congr_app_apply (map_conormalSetInclusion B S hS Z hZ) U _).trans
    (congrArg ((thickeningRingUnit B S hS Z).hom.app U)
      (SheafOfModules.hom_congr_app_apply
        (unit_comp_submoduleιOfEssImage B S hS (subspaceInclusion B S hS X Z) Z.2.2
          (definingIdealSheaf B S hS X Z)
          (essImage_modulePushforward_definingIdealSheaf_of_isFirstOrderThickening B S hS Z hZ))
        U t))

/-- `AlgebraicGeometry.Space.map_conormalSetInclusion_unit` as an equation of morphisms of
sheaves of sets on the small étale site of `X`. -/
theorem unit_comp_map_conormalSetInclusion :
    (CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules) ≫
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        (conormalSetInclusion B S hS Z hZ) =
      (CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          (definingIdealSheaf B S hS X Z).ι ≫
        (sheafCompose (SmallEtale.topology B S hS X.1) (CategoryTheory.forget RingCat.{u})).map
          (thickeningRingUnit B S hS Z) :=
  CategoryTheory.Sheaf.hom_ext_sections fun U t ↦
    map_conormalSetInclusion_unit B S hS Z hZ U t

/-- **The transpose of the map of defining ideal sheaves, read inside the structure sheaf.**  The
transpose `𝓘_W ⟶ c_*𝓘_Z` of the map of defining ideal sheaves of [Stacks Project, Tag 04CP],
followed by the inclusion of `𝓘_Z` into `𝒪_X`, is the inclusion of `𝓘_W` into `𝒪_W` followed by
the transpose of the canonical comparison `c^*𝒪_W ⟶ 𝒪_X`. -/
theorem homEquiv_idealSheafMap_comp_ι :
    (modulePullbackAdjunction B S hS c).homEquiv _ _ (idealSheafMap B S hS Z W₀ c e₀ hsq) ≫
        (modulePushforward B S hS c).map (definingIdealSheaf B S hS X Z).ι =
      (definingIdealSheaf B S hS W W₀).ι ≫
        (modulePullbackAdjunction B S hS c).homEquiv _ _ (structureModulePullbackMap B S hS c) :=
  ((modulePullbackAdjunction B S hS c).homEquiv_naturality_right _ _).symm.trans
    ((congrArg ((modulePullbackAdjunction B S hS c).homEquiv _ _)
      (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z W₀ c e₀ hsq)).trans
      ((modulePullbackAdjunction B S hS c).homEquiv_naturality_left _ _))

end Core

/-! ### Injectivity of the conormal inclusion -/

section Injective

variable (hZ : IsFirstOrderThickening B S hS X Z.1)

/-- A morphism of sheaves of sets on the small étale site of an algebraic space which is
injective on sections is a monomorphism. -/
theorem mono_of_injective_app_setSheaf {Y : AlgebraicSpaces B S hS}
    {P Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)} (f : P ⟶ Q)
    (hf : ∀ V, Function.Injective (f.hom.app V)) : Mono f :=
  ⟨fun _ _ H ↦ Sheaf.hom_ext (NatTrans.ext (funext fun V ↦
    ConcreteCategory.hom_ext _ _ fun z ↦ hf V (congrArg (fun m ↦ m.hom.app V z) H)))⟩

/-- **The conormal inclusion of sheaves of sets is a monomorphism.**  Its direct image along `i`
is the inclusion `i_*𝒞_{Z/X} ⟶ 𝒪_X`, which is injective on sections, followed by the unit
`𝒪_X ⟶ i_*i^{-1}𝒪_X`, which is an isomorphism for a thickening; and the direct image along a
closed immersion is faithful. -/
theorem mono_conormalSetInclusion : Mono (conormalSetInclusion B S hS Z hZ) := by
  have := (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS
    (subspaceInclusion B S hS X Z) Z.2.2).faithful
  have hm : Mono ((CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
      (firstOrderConormalModuleι B S hS Z hZ)) :=
    mono_of_injective_app_setSheaf B S hS _ fun V ↦
      injective_firstOrderConormalModuleι_app B S hS Z hZ V
  have := isIso_thickeningRingUnit B S hS Z hZ.1
  have hi : IsIso ((sheafCompose (SmallEtale.topology B S hS X.1)
      (CategoryTheory.forget RingCat.{u})).map (thickeningRingUnit B S hS Z)) :=
    Functor.map_isIso _ _
  refine (smallToposMorphismTypeU B S hS
    (subspaceInclusion B S hS X Z)).pushforward.mono_of_mono_map ?_
  rw [map_conormalSetInclusion B S hS Z hZ]
  exact mono_comp' hm (@IsIso.mono_of_iso _ _ _ _ _ hi)

/-- **The direct image of the conormal inclusion along any morphism is a monomorphism**: the
direct image of sheaves of sets is a right adjoint, so it preserves monomorphisms. -/
theorem mono_pushforward_map_conormalSetInclusion {T : AlgebraicSpaces B S hS}
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ T) :
    Mono ((smallToposMorphismTypeU B S hS e).pushforward.map
      (conormalSetInclusion B S hS Z hZ)) := by
  have := mono_conormalSetInclusion B S hS Z hZ
  have := (smallToposMorphismTypeU B S hS e).adj.rightAdjoint_preservesLimits
  infer_instance

end Injective

section Comorphism

/-- **The comorphism of `c` read through the thickening, on underlying sheaves of sets**: the
structure map of `c`, the direct image of the unit `𝒪_X ⟶ i_*i^{-1}𝒪_X`, and the comparison
`c_*i_* ≅ (i ≫ c)_*` of [Stacks Project, Tag 03G2], part (3). -/
theorem sheafCompose_map_structureSharpThroughThickening_thickeningRingUnit :
    (sheafCompose (SmallEtale.topology B S hS W.1) (CategoryTheory.forget RingCat.{u})).map
        (structureSharpThroughThickening B S hS Z c) =
      structureSharpSet B S hS c ≫
        (smallToposMorphismTypeU B S hS c).pushforward.map
          ((sheafCompose (SmallEtale.topology B S hS X.1) (CategoryTheory.forget RingCat.{u})).map
            (thickeningRingUnit B S hS Z)) ≫
        (smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X Z) c).hom.app
          ((sheafCompose (SmallEtale.topology B S hS
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
            (CategoryTheory.forget RingCat.{u})).obj
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) := by
  simp only [structureSharpThroughThickening_eq, Functor.map_comp, pullbackRingSheafFunctor_map]
  rfl


variable (hZ : IsFirstOrderThickening B S hS X Z.1)

/-- **The transpose of `i^*` of the map of defining ideal sheaves is the comorphism of `c` on the
defining ideal.**  Along `(i ≫ c)^* ⊣ (i ≫ c)_*`, the morphism `(i ≫ c)^*𝓘_W ⟶ 𝒞_{Z/X}`
obtained from the map of defining ideal sheaves transposes to a morphism
`𝓘_W ⟶ (i ≫ c)_*𝒞_{Z/X}`; followed by the direct image of the inclusion `𝒞_{Z/X} ⟶ i^{-1}𝒪_X`
of sheaves of sets, it is the inclusion of `𝓘_W` into `𝒪_W` followed by the comorphism
`𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` of `c` read through the thickening. -/
theorem pushforward_conormalSetInclusion_homEquiv (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V) :
    ((smallToposMorphismTypeU B S hS ((subspaceInclusion B S hS X Z) ≫ c)).pushforward.map
        (conormalSetInclusion B S hS Z hZ)).hom.app V
        (((modulePullbackAdjunction B S hS ((subspaceInclusion B S hS X Z) ≫ c)).homEquiv _ _
          ((modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).inv.app
              (definingIdealSheaf B S hS W W₀).toSheafOfModules ≫
            (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
              (idealSheafMap B S hS Z W₀ c e₀ hsq))).val.app V s) =
      (structureSharpThroughThickening B S hS Z c).hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) := by
  have h1 := modules_val_app_congr B S hS
    (homEquiv_conormalTranspose B S hS Z W₀ c e₀ hsq) V s
  have h2 := modulePushforwardCompIso_hom_app_val_app B S hS (subspaceInclusion B S hS X Z) c
    ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
      (definingIdealSheaf B S hS X Z).toSheafOfModules) V
    ((((modulePullbackAdjunction B S hS c).homEquiv _ _ (idealSheafMap B S hS Z W₀ c e₀ hsq) ≫
      (modulePushforward B S hS c).map
        ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules))).val.app V s)
  have h3 := setSheafHom_congr_app_apply
    ((smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X Z) c).hom.naturality
      (conormalSetInclusion B S hS Z hZ)) V
    ((((modulePullbackAdjunction B S hS c).homEquiv _ _ (idealSheafMap B S hS Z W₀ c e₀ hsq) ≫
      (modulePushforward B S hS c).map
        ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules))).val.app V s)
  have h4 := setSheafHom_congr_app_apply
    (congrArg (smallToposMorphismTypeU B S hS c).pushforward.map
      (unit_comp_map_conormalSetInclusion B S hS Z hZ)) V
    (((modulePullbackAdjunction B S hS c).homEquiv _ _
      (idealSheafMap B S hS Z W₀ c e₀ hsq)).val.app V s)
  have h5 := modules_val_app_congr B S hS
    (homEquiv_idealSheafMap_comp_ι B S hS Z W₀ c e₀ hsq) V s
  have h6 := CategoryTheory.Sheaf.hom_congr_app_apply
    (moduleSheafFunctor_map_homEquiv_structureModulePullbackMap B S hS c) V
    ((definingIdealSheaf B S hS W W₀).ι.val.app V s)
  have h7 := setSheafHom_congr_app_apply
    ((smallToposMorphismTypeU B S hS c).pushforward.map_comp
      ((CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules))
      ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        (conormalSetInclusion B S hS Z hZ))) V
    (((modulePullbackAdjunction B S hS c).homEquiv _ _
      (idealSheafMap B S hS Z W₀ c e₀ hsq)).val.app V s)
  have h8 := setSheafHom_congr_app_apply
    ((smallToposMorphismTypeU B S hS c).pushforward.map_comp
      ((CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          (definingIdealSheaf B S hS X Z).ι)
      ((sheafCompose (SmallEtale.topology B S hS X.1) (CategoryTheory.forget RingCat.{u})).map
          (thickeningRingUnit B S hS Z))) V
    (((modulePullbackAdjunction B S hS c).homEquiv _ _
      (idealSheafMap B S hS Z W₀ c e₀ hsq)).val.app V s)
  refine (congrArg (((smallToposMorphismTypeU B S hS
      ((subspaceInclusion B S hS X Z) ≫ c)).pushforward.map
    (conormalSetInclusion B S hS Z hZ)).hom.app V)
      ((h1.trans (modules_comp_val_app B S hS _ _ V s)).trans h2)).trans ?_
  refine h3.symm.trans (Eq.trans ?_ (setSheafHom_congr_app_apply
    (sheafCompose_map_structureSharpThroughThickening_thickeningRingUnit B S hS Z c) V
    ((definingIdealSheaf B S hS W W₀).ι.val.app V s)).symm)
  refine (setSheaf_comp_hom_app_apply _ _ V _).trans (Eq.trans ?_
    (setSheaf_comp_hom_app_apply _ _ V _).symm)
  refine congrArg _ ?_
  refine (h7.symm.trans (h4.trans h8)).trans ?_
  refine (setSheaf_comp_hom_app_apply _ _ V _).trans (Eq.trans ?_
    (setSheaf_comp_hom_app_apply _ _ V _).symm)
  refine congrArg _ ?_
  exact h5.trans h6

/-- `AlgebraicGeometry.Space.pushforward_conormalSetInclusion_homEquiv`, with the composite
`i ≫ c` replaced by a morphism `F'` it is equal to, through the comparison `F'^* = (i ≫ c)^*`. -/
theorem pushforward_conormalSetInclusion_homEquiv_at
    (F' : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : (subspaceInclusion B S hS X Z) ≫ c = F')
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V) :
    ((smallToposMorphismTypeU B S hS F').pushforward.map
        (conormalSetInclusion B S hS Z hZ)).hom.app V
        (((modulePullbackAdjunction B S hS F').homEquiv _ _
          ((eqToIso (congrArg (fun g ↦ modulePullback B S hS g) h.symm)).hom.app
              (definingIdealSheaf B S hS W W₀).toSheafOfModules ≫
            (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).inv.app
              (definingIdealSheaf B S hS W W₀).toSheafOfModules ≫
            (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
              (idealSheafMap B S hS Z W₀ c e₀ hsq))).val.app V s) =
      (structureSharpThroughThickeningAt B S hS Z c F' h).hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) := by
  subst h
  simp only [eqToIso_refl, Iso.refl_hom, structureSharpThroughThickeningAt, eqToHom_refl,
    Category.comp_id]
  exact pushforward_conormalSetInclusion_homEquiv B S hS Z W₀ c e₀ hsq hZ V s

end Comorphism

end AlgebraicGeometry.Space

end
