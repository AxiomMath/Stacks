module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPullback

/-!
# `(G ⊗ N)^∨ ≅ N^∨ ⊗ G^∨` under pullback

For finite locally free `G` the identification `(G ⊗ N)^∨ ≅ N^∨ ⊗ G^∨` pairs `ν ⊗ μ` with `x ⊗ y`
to `μ(x) ν(y)`. Under pullback along a morphism of schemes it corresponds, through the dual
base-change isomorphisms, to the same identification for `f^* G ≅ G'` and `f^* N ≅ N'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualMap)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section Pairing

variable {X : Scheme.{u}} (G N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]

/-- **The pairing of `N^∨ ⊗ G^∨ ≅ (G ⊗ N)^∨`** on pure tensors: `(ν ⊗ μ) ⊗ (x ⊗ y) ↦ μ(x) ν(y)`. -/
public theorem dualTensorIso_inv_pairing (U : X.Opensᵒᵖ) (ν : (dualSheaf N).val.obj U)
    (μ : (dualSheaf G).val.obj U) (x : G.val.obj U) (y : N.val.obj U) :
    (tensorMap (Z := X.toRingedSpace) (dualTensorIso G N).inv
        (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G).obj N)) ≫
        dualEvaluation (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G).obj N)).val.app U
      ((PresheafOfModules.tensorSheafUnit (Osharp := X.toRingedSpace.sheaf)
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (dualSheaf N)).obj
                (dualSheaf G))
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G).obj N)).app U
        (toTensorSheafSection X.toRingedSpace (dualSheaf N) (dualSheaf G) U (ν ⊗ₜ μ) ⊗ₜ
          toTensorSheafSection X.toRingedSpace G N U (x ⊗ₜ y))) =
      Stacks.SheafOfModules.evalNestedInternalHomSection X.toRingedSpace U.unop
        ((sheafHomIsoTensorDual G (dualSheaf N)).inv.val.app U
          (toTensorSheafSection X.toRingedSpace (dualSheaf N) (dualSheaf G) U (ν ⊗ₜ μ))) x y := by
  refine (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine (congrArg ((dualEvaluation
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G).obj N)).val.app U)
    (Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      (J := Opens.grothendieckTopology X) (Osharp := X.sheaf) (f := (dualTensorIso G N).inv)
      (g := 𝟙 _) (V := U) (x := toTensorSheafSection X.toRingedSpace (dualSheaf N) (dualSheaf G) U
        (ν ⊗ₜ μ)) (y := toTensorSheafSection X.toRingedSpace G N U (x ⊗ₜ y)))).trans ?_
  refine (dualEvaluation_tensorSheafUnit _ U _ _).trans ?_
  have hi := Stacks.SheafOfModules.internalHomTensorIso_hom_app_tmul X.toRingedSpace U.unop
    ((Stacks.SheafOfModules.internalHomTensorIso X.toRingedSpace G N
      (SheafOfModules.unit (_root_.structureSheaf X.sheaf))).inv.val.app U
      ((sheafHomIsoTensorDual G (dualSheaf N)).inv.val.app U
        (toTensorSheafSection X.toRingedSpace (dualSheaf N) (dualSheaf G) U (ν ⊗ₜ μ)))) x y
  have hc := Stacks.Chow.iso_inv_val_app_hom_val_app (Stacks.SheafOfModules.internalHomTensorIso
    X.toRingedSpace G N (SheafOfModules.unit (_root_.structureSheaf X.sheaf))).symm U.unop
    ((sheafHomIsoTensorDual G (dualSheaf N)).inv.val.app U
      (toTensorSheafSection X.toRingedSpace (dualSheaf N) (dualSheaf G) U (ν ⊗ₜ μ)))
  exact hi.symm.trans (congrArg (fun s => Stacks.SheafOfModules.evalNestedInternalHomSection
    X.toRingedSpace U.unop s x y) hc)

/-- The rank-one section of `SheafHom(G, N^∨)` attached to `ν ⊗ μ`, evaluated on `x` and `y`:
`μ(x) ν(y)`. -/
public theorem evalNested_rankOne (U : X.Opensᵒᵖ) (ν : (dualSheaf N).val.obj U)
    (μ : (dualSheaf G).val.obj U) (x : G.val.obj U) (y : N.val.obj U) (r₁ r₂ : Γ(X, U.unop))
    (h₁ : (μ.app (op (Over.mk (𝟙 U.unop)))).hom x = r₁)
    (h₂ : (ν.app (op (Over.mk (𝟙 U.unop)))).hom y = r₂) :
    Stacks.SheafOfModules.evalNestedInternalHomSection X.toRingedSpace U.unop
        ((sheafHomIsoTensorDual G (dualSheaf N)).inv.val.app U
          (toTensorSheafSection X.toRingedSpace (dualSheaf N) (dualSheaf G) U (ν ⊗ₜ μ))) x y =
      r₁ * r₂ := by
  have h3 := Stacks.SheafOfModules.tensorDualToSheafHom_toTensorSheafSection X.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) G (dualSheaf N) U ν μ
  have h4 := (congrArg (fun s => (((s.app (op (Over.mk (𝟙 U.unop)))).hom x).app
    (op (Over.mk (𝟙 U.unop)))).hom y) h3)
  refine h4.trans ?_
  refine (congrArg (fun t => (t.app (op (Over.mk (𝟙 U.unop)))).hom y)
    (Stacks.SheafOfModules.rankOneHomSection_app X.sheaf.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) ν μ
        (op (Over.mk (𝟙 U.unop))) x)).trans ?_
  subst h₁ h₂
  rw [Stacks.SheafOfModules.resSection_self (U := U.unop) ν]
  have hid : ∀ z : Γ(X, U.unop), X.presheaf.map (𝟙 (op U.unop)) z = z := fun z => by
    rw [X.presheaf.map_id]; rfl
  exact congrArg (fun a => a * _) (hid _)

/-- The pairing of `dualTensorIso_inv_pairing` is `r₁ * r₂`, given `μ(x) = r₁` and `ν(y) = r₂`. -/
private theorem dualTensorIso_inv_pairing_eq_mul (U : X.Opensᵒᵖ) (ν : (dualSheaf N).val.obj U)
    (μ : (dualSheaf G).val.obj U) (x : G.val.obj U) (y : N.val.obj U) (r₁ r₂ : Γ(X, U.unop))
    (h₁ : (μ.app (op (Over.mk (𝟙 U.unop)))).hom x = r₁)
    (h₂ : (ν.app (op (Over.mk (𝟙 U.unop)))).hom y = r₂) :
    (tensorMap (Z := X.toRingedSpace) (dualTensorIso G N).inv
        (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G).obj N)) ≫
        dualEvaluation (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G).obj N)).val.app U
      ((PresheafOfModules.tensorSheafUnit (Osharp := X.toRingedSpace.sheaf)
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (dualSheaf N)).obj
                (dualSheaf G))
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G).obj N)).app U
        (toTensorSheafSection X.toRingedSpace (dualSheaf N) (dualSheaf G) U (ν ⊗ₜ μ) ⊗ₜ
          toTensorSheafSection X.toRingedSpace G N U (x ⊗ₜ y))) =
      r₁ * r₂ :=
  (dualTensorIso_inv_pairing G N U ν μ x y).trans (evalNested_rankOne G N U ν μ x y r₁ r₂ h₁ h₂)

end Pairing


section Ext

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `pullback_tensorSheaf_hom_ext₂₂`, with the inner tensor products of
`Stacks.SheafOfModules.TensorStalkRingedSpace`. -/
public theorem pullback_tensorSheaf_hom_ext₂₂T {A B C D : Y.Modules} {N : X.Modules}
    {θ₁ θ₂ : (pullbackFunctor f.toLRSHom.toShHom).obj ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj A).obj B,
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj C).obj D)) ⟶ N}
    (h : ∀ (U : (Opens Y.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) (c : C.val.obj U)
        (d : D.val.obj U),
      θ₁.val.app ((opensMap f.toLRSHom.toShHom).op.obj U)
          (pullbackUnit f.toLRSHom.toShHom _ U
            ((PresheafOfModules.tensorSheafUnit (Osharp := Y.toRingedSpace.sheaf)
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj A).obj B)
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj C).obj D)).app U
          (toTensorSheafSection Y.toRingedSpace A B U (a ⊗ₜ b) ⊗ₜ
            toTensorSheafSection Y.toRingedSpace C D U (c ⊗ₜ d)))) =
        θ₂.val.app ((opensMap f.toLRSHom.toShHom).op.obj U)
          (pullbackUnit f.toLRSHom.toShHom _ U
            ((PresheafOfModules.tensorSheafUnit (Osharp := Y.toRingedSpace.sheaf)
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj A).obj B)
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj C).obj D)).app U
          (toTensorSheafSection Y.toRingedSpace A B U (a ⊗ₜ b) ⊗ₜ
            toTensorSheafSection Y.toRingedSpace C D U (c ⊗ₜ d))))) :
    θ₁ = θ₂ :=
  pullback_tensorSheaf_hom_ext₂₂ f.toLRSHom.toShHom (A := A) (B := B) (C := C) (D := D) h

end Ext


section BaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {G N : Y.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj G).obj N)]
  {G' N' : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G').obj N')]
  (σ : (Scheme.Modules.pullback f).obj G ≅ G') (δ : (Scheme.Modules.pullback f).obj N ≅ N')

/-- **`(G ⊗ N)^∨ ≅ N^∨ ⊗ G^∨` under pullback**: along `σ : f^* G ≅ G'` and `δ : f^* N ≅ N'`, the
dual base-change isomorphisms of `N`, `G` and `G ⊗ N` intertwine the two identifications. -/
public theorem dualTensorIso_inv_pullback :
    (Scheme.Modules.pullback f).map (dualTensorIso G N).inv ≫
        (pullbackDualIsoOf f _ (tensorPullbackIsoT f σ δ) inferInstance).hom =
      (tensorPullbackIsoT f (pullbackDualIsoOf f N δ inferInstance)
          (pullbackDualIsoOf f G σ inferInstance)).hom ≫ (dualTensorIso G' N').inv := by
  refine pullbackDualIsoOf_curry f (tensorPullbackIsoT f σ δ) _ _ _ ?_
  refine pullback_tensorSheaf_hom_ext₂₂T f (A := dualSheaf N) (B := dualSheaf G) (C := G) (D := N)
    (fun U ν μ x y => ?_)
  -- the left side
  have l1 := pullbackUnit_naturality f.toLRSHom.toShHom
    (tensorMap (Z := Y.toRingedSpace) (dualTensorIso G N).inv
        (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj G).obj N)) ≫
      dualEvaluation (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj G).obj N))
    U ((PresheafOfModules.tensorSheafUnit (Osharp := Y.toRingedSpace.sheaf)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (dualSheaf N)).obj (dualSheaf G))
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj G).obj N)).app U
        (toTensorSheafSection Y.toRingedSpace (dualSheaf N) (dualSheaf G) U (ν ⊗ₜ μ) ⊗ₜ
          toTensorSheafSection Y.toRingedSpace G N U (x ⊗ₜ y)))
  have l23 := dualTensorIso_inv_pairing_eq_mul G N U ν μ x y _ _ rfl rfl
  have l4 := Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit f.toLRSHom.toShHom U
    (@id Γ(Y, U.unop) ((μ.app (op (Over.mk (𝟙 U.unop)))).hom x) *
      @id Γ(Y, U.unop) ((ν.app (op (Over.mk (𝟙 U.unop)))).hom y))
  have r1 := Stacks.RingedSpace.comparison_pullbackUnit_tmul f.toLRSHom.toShHom
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (dualSheaf N)).obj (dualSheaf G))
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj G).obj N) U
    (toTensorSheafSection Y.toRingedSpace (dualSheaf N) (dualSheaf G) U (ν ⊗ₜ μ))
    (toTensorSheafSection Y.toRingedSpace G N U (x ⊗ₜ y))
  have r3 := tensorPullbackIso_unit f.toLRSHom.toShHom (pullbackDualIsoOf f N δ inferInstance)
    (pullbackDualIsoOf f G σ inferInstance) U ν μ
  have r4 := tensorPullbackIso_unit f.toLRSHom.toShHom σ δ U x y
  have r56 := dualTensorIso_inv_pairing_eq_mul G' N' ((opensMap f.toLRSHom.toShHom).op.obj U)
    ((pullbackDualIsoOf f N δ inferInstance).hom.val.app _
      (pullbackUnit f.toLRSHom.toShHom (dualSheaf N) U ν))
    ((pullbackDualIsoOf f G σ inferInstance).hom.val.app _
      (pullbackUnit f.toLRSHom.toShHom (dualSheaf G) U μ))
    (σ.hom.val.app _ (pullbackUnit f.toLRSHom.toShHom G U x))
    (δ.hom.val.app _ (pullbackUnit f.toLRSHom.toShHom N U y)) _ _
    (pullbackDualIsoOf_unit f G σ inferInstance U μ x)
    (pullbackDualIsoOf_unit f N δ inferInstance U ν y)
  refine (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine (congrArg ((Stacks.PullbackAlgebra.pullbackUnitIso f.toLRSHom.toShHom).hom.val.app _)
    l1).trans ?_
  refine (congrArg (fun t =>
      (Stacks.PullbackAlgebra.pullbackUnitIso f.toLRSHom.toShHom).hom.val.app _
    (pullbackUnit f.toLRSHom.toShHom _ U t)) l23).trans ?_
  refine l4.trans ?_
  refine Eq.trans ?_ (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).symm
  refine Eq.trans ?_ (congrArg ((tensorMap (Z := X.toRingedSpace)
      (tensorPullbackIsoT f (pullbackDualIsoOf f N δ inferInstance)
        (pullbackDualIsoOf f G σ inferInstance)).hom (tensorPullbackIsoT f σ δ).hom ≫
      tensorMap (Z := X.toRingedSpace) (dualTensorIso G' N').inv
        (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G').obj N')) ≫
      dualEvaluation (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G').obj N')).val.app _) r1).symm
  refine Eq.trans ?_ (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).symm
  refine Eq.trans ?_ (congrArg ((tensorMap (Z := X.toRingedSpace) (dualTensorIso G' N').inv
        (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G').obj N')) ≫
      dualEvaluation (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G').obj N')).val.app _)
    (Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      (J := Opens.grothendieckTopology X) (Osharp := X.sheaf)
      (f := (tensorPullbackIsoT f (pullbackDualIsoOf f N δ inferInstance)
        (pullbackDualIsoOf f G σ inferInstance)).hom) (g := (tensorPullbackIsoT f σ δ).hom)
      (V := (opensMap f.toLRSHom.toShHom).op.obj U) (x := pullbackUnit f.toLRSHom.toShHom _ U
        (toTensorSheafSection Y.toRingedSpace (dualSheaf N) (dualSheaf G) U (ν ⊗ₜ μ)))
      (y := pullbackUnit f.toLRSHom.toShHom _ U
        (toTensorSheafSection Y.toRingedSpace G N U (x ⊗ₜ y))))).symm
  have r34 : (PresheafOfModules.tensorSheafUnit (Osharp := X.toRingedSpace.sheaf)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (dualSheaf N')).obj
              (dualSheaf G'))
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G').obj N')).app
          ((opensMap f.toLRSHom.toShHom).op.obj U)
        ((tensorPullbackIsoT f (pullbackDualIsoOf f N δ inferInstance)
          (pullbackDualIsoOf f G σ inferInstance)).hom.val.app _
            (pullbackUnit f.toLRSHom.toShHom _ U
              (toTensorSheafSection Y.toRingedSpace (dualSheaf N) (dualSheaf G) U (ν ⊗ₜ μ))) ⊗ₜ
          (tensorPullbackIsoT f σ δ).hom.val.app _ (pullbackUnit f.toLRSHom.toShHom _ U
            (toTensorSheafSection Y.toRingedSpace G N U (x ⊗ₜ y)))) =
      (PresheafOfModules.tensorSheafUnit (Osharp := X.toRingedSpace.sheaf)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (dualSheaf N')).obj
              (dualSheaf G'))
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G').obj N')).app
          ((opensMap f.toLRSHom.toShHom).op.obj U)
        (toTensorSheafSection X.toRingedSpace (dualSheaf N') (dualSheaf G') _
          ((pullbackDualIsoOf f N δ inferInstance).hom.val.app _
            (pullbackUnit f.toLRSHom.toShHom (dualSheaf N) U ν) ⊗ₜ
          (pullbackDualIsoOf f G σ inferInstance).hom.val.app _
            (pullbackUnit f.toLRSHom.toShHom (dualSheaf G) U μ)) ⊗ₜ
        toTensorSheafSection X.toRingedSpace G' N' _
          (σ.hom.val.app _ (pullbackUnit f.toLRSHom.toShHom G U x) ⊗ₜ
            δ.hom.val.app _ (pullbackUnit f.toLRSHom.toShHom N U y))) := by
    rw [show (tensorPullbackIsoT f (pullbackDualIsoOf f N δ inferInstance)
          (pullbackDualIsoOf f G σ inferInstance)).hom.val.app _
            (pullbackUnit f.toLRSHom.toShHom _ U
              (toTensorSheafSection Y.toRingedSpace (dualSheaf N) (dualSheaf G) U (ν ⊗ₜ μ))) =
            _ from r3,
      show (tensorPullbackIsoT f σ δ).hom.val.app _ (pullbackUnit f.toLRSHom.toShHom _ U
            (toTensorSheafSection Y.toRingedSpace G N U (x ⊗ₜ y))) = _ from r4]
    rfl
  refine Eq.trans ?_ (congrArg ((tensorMap (Z := X.toRingedSpace) (dualTensorIso G' N').inv
        (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G').obj N')) ≫
      dualEvaluation (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G').obj N')).val.app _) r34).symm
  refine Eq.trans ?_ r56.symm
  exact map_mul (ConcreteCategory.hom ((structureSheafHom f.toLRSHom.toShHom).hom.app U)) _ _

end BaseChange

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
