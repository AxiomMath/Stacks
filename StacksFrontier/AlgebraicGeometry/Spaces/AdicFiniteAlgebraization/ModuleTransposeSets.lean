module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackChartSectionTranspose
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPushforwardAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent

/-!
# Transposes along the module pullback adjunction, on sections

On underlying sheaves of sets, the transpose along the module pullback adjunction of the
identification of `g^* (A_mod)` with the module underlying `g^* A`, followed by the underlying
module map of a morphism of algebras `χ`, is the algebra transpose of `χ`
(`AlgebraicGeometry.Space.modulePullbackAdjunction_homEquiv_underlyingModuleMap_val_app_heq`).
These are the section-level ingredients of the transposition identity of a cartesian affine
square (`AlgebraicGeometry.Space.isPushforwardTransposeCompatible_cartesianTransition`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

/-- Composites of heterogeneously equal morphisms between equal objects are heterogeneously
equal. -/
theorem CategoryTheory.comp_heq_comp {C : Type*} [Category C] {X X' Y Y' Z Z' : C}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z}
    {g' : Y' ⟶ Z'} (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst hX hY hZ
  cases hf
  cases hg
  rfl

/-- On underlying sheaves of sets, restriction of scalars does nothing to a morphism. -/
theorem CategoryTheory.Sheaf.moduleSheafFunctor_map_restrictScalars_map.{w, w', w''}
    {C : Type w''} [Category.{w'} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget RingCat.{w})]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})] {R R' : Sheaf J RingCat.{w}} (α : R ⟶ R')
    {N N' : SheafOfModules.{w} R'} (ψ : N ⟶ N') :
    (Sheaf.moduleSheafFunctor R).map ((SheafOfModules.restrictScalars α).map ψ) =
      (Sheaf.moduleSheafFunctor R').map ψ :=
  Sheaf.hom_ext_sections fun _ _ => rfl

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- On underlying sheaves of sets, the transpose along Stacks 03CZ of the identification of
`g^*(A_mod)` with the module underlying `g^*A`, followed by a morphism of algebras `χ`, is the
first inclusion `g⁻¹A ⟶ g^*A` of the pushout followed by `χ`. -/
theorem moduleSheafFunctor_map_extendScalarsAdjunction_homEquiv_comp_heq (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2)
    (χ : (algebraPullback B S hS g).obj A ⟶ C) :
    HEq ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((ringSheafPullback B S hS g).obj (structureSheaf B S hS X.1 X.2)))).map
      ((Stacks.FlatChangeOfRings.extendScalarsAdjunction (structurePullbackMap B S hS g)).homEquiv
        ((Stacks.Sheaves.RingedToposModules.inverseImageModules
          (smallEtaleRingedToposHom B S hS g).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2))).obj
            A.underlyingModule) C.underlyingModule
        ((underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom ≫
          AlgebraSheaf.underlyingModuleMap χ)))
      ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((algebraPullbackMap B S hS g).app A ≫ χ.right)) := by
  have h3 := (Stacks.FlatChangeOfRings.extendScalarsAdjunction
    (structurePullbackMap B S hS g)).homEquiv_naturality_right
      (X := (Stacks.Sheaves.RingedToposModules.inverseImageModules
          (smallEtaleRingedToposHom B S hS g).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2))).obj
            A.underlyingModule)
      (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom
      (AlgebraSheaf.underlyingModuleMap χ)
  have e := (congrArg (Sheaf.moduleSheafFunctor.{u, u, u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      ((ringSheafPullback B S hS g).obj (structureSheaf B S hS X.1 X.2)))).map h3).trans
      ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((ringSheafPullback B S hS g).obj (structureSheaf B S hS X.1 X.2)))).map_comp _ _)
  refine (heq_of_eq e).trans ?_
  refine HEq.trans ?_ (heq_of_eq ((sheafCompose (SmallEtale.topology B S hS Y.1)
    (forget CommRingCat.{u})).map_comp _ _).symm)
  refine comp_heq_comp rfl rfl rfl
    (moduleSheafFunctor_map_extendScalarsAdjunction_homEquiv_heq B S hS g A) ?_
  exact heq_of_eq (Sheaf.hom_ext_sections fun _ _ => rfl)

/-- **On underlying sheaves of sets, the transpose along Stacks 03D7 of a morphism of algebras
out of a pullback algebra is the ring-level transpose.** -/
theorem moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_comp_heq (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2)
    (χ : (algebraPullback B S hS g).obj A ⟶ C) :
    HEq ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS X)).map
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        (smallEtaleRingedToposModulesHom B S hS g)).homEquiv
        A.underlyingModule C.underlyingModule
        ((underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom ≫
          AlgebraSheaf.underlyingModuleMap χ)))
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
        ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
          A.right C.right ((algebraPullbackMap B S hS g).app A ≫ χ.right))) :=
  moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_heq_of B S hS g A
    ((algebraPullbackMap B S hS g).app A ≫ χ.right)
    ((underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom ≫
      AlgebraSheaf.underlyingModuleMap χ)
    (moduleSheafFunctor_map_extendScalarsAdjunction_homEquiv_comp_heq B S hS g A C χ)

/-- The sections of a composite of morphisms of sheaves of modules. -/
theorem _root_.SheafOfModules.comp_val_app_apply'.{w, w', w''} {C : Type w''} [Category.{w'} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} {M N P : SheafOfModules.{w} R}
    (f : M ⟶ N) (g : N ⟶ P) (V : Cᵒᵖ) (x : M.val.obj V) :
    (f ≫ g).val.app V x = g.val.app V (f.val.app V x) :=
  rfl

/-- The comparison of the two direct images of modules is the identity on sections, with the
section taken in the direct image of the ringed topoi. -/
theorem modulePushforwardIso_hom_app_val_app_heq' {X' Y' : AlgebraicSpaces B S hS} (f : X' ⟶ Y')
    (N : Modules.{u, u} B S hS X'.1 X'.2) (W : (SmallEtale B S hS Y'.1)ᵒᵖ)
    (y : ((smallEtaleRingedToposHom B S hS f).pushforwardModules.obj N).val.obj W) :
    HEq (((modulePushforwardIso B S hS f).hom.app N).val.app W y) y :=
  heq_of_eq (modulePushforwardIso_hom_app_val_app B S hS f N W y)

/-- The transpose along `AlgebraicGeometry.Space.modulePullbackAdjunction` agrees on sections with
the transpose along the adjunction of the ringed topoi. -/
theorem modulePullbackAdjunction_homEquiv_val_app_heq (g : Y ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (N : Modules.{u, u} B S hS Y.1 Y.2)
    (k : (modulePullback B S hS g).obj M ⟶ N) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : M.val.obj V) :
    HEq (((modulePullbackAdjunction B S hS g).homEquiv M N k).val.app V x)
      (((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        (smallEtaleRingedToposModulesHom B S hS g)).homEquiv M N k).val.app V x) := by
  have h1 : (modulePullbackAdjunction B S hS g).homEquiv M N k =
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        (smallEtaleRingedToposModulesHom B S hS g)).homEquiv M N k ≫
      (modulePushforwardIso B S hS g).hom.app N :=
    Adjunction.homEquiv_ofNatIsoRight_apply _ _ k
  rw [h1]
  refine HEq.trans (heq_of_eq (SheafOfModules.comp_val_app_apply' _ _ V x)) ?_
  exact modulePushforwardIso_hom_app_val_app_heq' B S hS g N V
    (((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        (smallEtaleRingedToposModulesHom B S hS g)).homEquiv M N k).val.app V x)

/-- **The transpose along `g^* ⊣ g_*` of a morphism of algebras out of a pullback algebra, read
on its underlying modules, is the transpose along the adjunction of algebra sheaves**, on
sections. -/
theorem modulePullbackAdjunction_homEquiv_underlyingModuleMap_val_app_heq (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2)
    (χ : (algebraPullback B S hS g).obj A ⟶ C) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : A.underlyingModule.val.obj V) :
    HEq (((modulePullbackAdjunction B S hS g).homEquiv A.underlyingModule C.underlyingModule
        ((underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom ≫
          AlgebraSheaf.underlyingModuleMap χ)).val.app V x)
      ((algebraPullbackHomEquiv g A C χ).right.hom.app V x) :=
  (modulePullbackAdjunction_homEquiv_val_app_heq B S hS g _ _ _ V x).trans
    (Sheaf.hom_app_heq rfl rfl
      (moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_comp_heq B S hS g A C χ) V x)

end AlgebraicGeometry.Space

end
