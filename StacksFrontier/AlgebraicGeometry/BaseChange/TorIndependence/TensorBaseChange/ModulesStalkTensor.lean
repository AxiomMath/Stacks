module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.StalkComplexCriterion
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorOnModels

/-!
# The stalk of a tensor product of sheaves of modules on a scheme

For sheaves of modules `M`, `N` on a scheme `X` and a point `x`, the stalk of `M ⊗_{𝒪_X} N` at `x`
is `M_x ⊗_{𝒪_{X,x}} N_x` (Stacks 01CB), naturally in both variables; the stalk of a pullback
`f^*N` at `x` is `𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} N_{f(x)}`, computed on germs.

## Main definitions

* `Stacks.ModuleSkyscraper.modulesStalkTensorIso`: the isomorphism
  `(M ⊗ N)_x ≅ M_x ⊗_{𝒪_{X,x}} N_x`.

## Main results

* `Stacks.ModuleSkyscraper.modulesStalkTensorIso_naturality_left`,
  `Stacks.ModuleSkyscraper.modulesStalkTensorIso_naturality_right`: `modulesStalkTensorIso` is
  natural in each variable.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace Stacks.ModuleSkyscraper

open AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

/-- **The stalk of a pullback, on germs.** The identification `𝒪_{X,x} ⊗ N_{f x} ≅ (f^*N)_x`
carries `1 ⊗ germ a` to the germ of the pullback-unit image of `a`. -/
theorem pullbackStalkIso_hom_app_one_tmul (N : Y.Modules) (V : Y.Opens) (hV : f x ∈ V)
    (a : Γ(N, V)) :
    ((pullbackStalkIso f x).hom.app N).hom
        ((ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app
          ((modulesStalkFunctor Y (f x)).obj N) ((N.presheaf.germ V (f x) hV) a)) =
      (((Scheme.Modules.pullback f).obj N).presheaf.germ (f ⁻¹ᵁ V) x hV)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app (op V) a) := by
  have h := unit_conjugateEquiv_symm
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (modulesStalkSkyAdjunction X x))
    ((modulesStalkSkyAdjunction Y (f x)).comp
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom)) (pushSkyIso f x).hom N
  exact (congrFun (congrArg (fun ψ => PresheafOfModules.Hom.app ψ.val (op V) a) h) ⟨hV⟩).symm

/-- The inverse of the identification `𝒪_{X,x} ⊗ N_{f x} ≅ (f^*N)_x` carries the germ of the
pullback-unit image of `a` to `1 ⊗ germ a`. -/
theorem pullbackStalkIso_inv_app_germ (N : Y.Modules) (V : Y.Opens) (hV : f x ∈ V)
    (a : Γ(N, V)) :
    ((pullbackStalkIso f x).inv.app N).hom
        ((((Scheme.Modules.pullback f).obj N).presheaf.germ (f ⁻¹ᵁ V) x hV)
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app (op V) a)) =
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app
          ((modulesStalkFunctor Y (f x)).obj N) ((N.presheaf.germ V (f x) hV) a) := by
  rw [← pullbackStalkIso_hom_app_one_tmul]
  exact ((pullbackStalkIso f x).app N).hom_inv_id_apply _

end Stacks.ModuleSkyscraper

namespace Stacks.ModuleSkyscraper

open AlgebraicGeometry Stacks.SheafOfModules.TensorStalkRingedSpace

variable {X : Scheme.{u}} (x : X)

/-- The two module structures on the stalk of a sheaf of modules over the local ring agree. -/
theorem modulesStalk_smul_eq (M : X.Modules) (r : X.presheaf.stalk x)
    (m : (modulesStalkFunctor X x).obj M) :
    r • m = @HSMul.hSMul _ _ _ (@instHSMul _ _
      (stalkModule X.toSheafedSpace M.val x).toSMul) r m := by
  obtain ⟨U₁, hU₁, r₀, hr⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  obtain ⟨U₂, hU₂, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
    M.val.presheaf m
  have hmem : x ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
  have hr' : (X.presheaf.germ (U₁ ⊓ U₂) x hmem).hom
      ((X.presheaf.map (homOfLE inf_le_left).op).hom r₀) = r := by
    rwa [TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) x hmem
      r₀]
  have hm' : (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf (U₁ ⊓ U₂) x hmem).hom
      ((M.val.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op).hom m₀) = m := by
    rwa [TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) M.val.presheaf
      (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) x hmem m₀]
  rw [← hr', ← hm']
  exact (germ_smul' M.val x (U₁ ⊓ U₂) hmem _ _).symm.trans
    (stalkModule_germ_smul X.toSheafedSpace M.val x (U₁ ⊓ U₂) hmem _ _)

/-- The module structure of Stacks 01CB on the stalk of a sheaf of modules on a scheme. -/
noncomputable local instance stalkModuleScheme (M : X.Modules) :
    Module (X.presheaf.stalk x) (grpStalk X.toRingedSpace M.val x) :=
  stalkModule X.toRingedSpace M.val x

/-- The stalk of a sheaf of modules over the local ring, with the module structure of
Stacks 01CB. -/
def stalkModuleEquiv (M : X.Modules) :
    letI : Module (X.presheaf.stalk x) (grpStalk X.toRingedSpace M.val x) :=
      stalkModule X.toRingedSpace M.val x
    (modulesStalkFunctor X x).obj M ≃ₗ[X.presheaf.stalk x] grpStalk X.toRingedSpace M.val x :=
  letI : Module (X.presheaf.stalk x) (grpStalk X.toRingedSpace M.val x) :=
    stalkModule X.toRingedSpace M.val x
  { toFun := fun m => m
    invFun := fun m => m
    map_add' := fun _ _ => rfl
    map_smul' := fun r m => modulesStalk_smul_eq x M r m
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- **The stalk of a tensor product of sheaves of modules on a scheme**, over the local ring:
`(M ⊗ N)_x ≅ M_x ⊗_{𝒪_{X,x}} N_x`. -/
def modulesStalkTensorIso (M N : X.Modules) :
    (modulesStalkFunctor X x).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N) ≅
      ((curriedTensor (ModuleCat.{u} (X.presheaf.stalk x))).obj
        ((modulesStalkFunctor X x).obj M)).obj ((modulesStalkFunctor X x).obj N) :=
  LinearEquiv.toModuleIso ((stalkModuleEquiv x
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N)).trans
    ((tensorStalkIso X.toRingedSpace x M N).trans
      (TensorProduct.congr (stalkModuleEquiv x M).symm (stalkModuleEquiv x N).symm)))

/-- The isomorphism `modulesStalkTensorIso` carries the germ of a pure tensor `m ⊗ n` of
sections to the pure tensor of the germs of `m` and `n`. -/
theorem modulesStalkTensorIso_hom_germ (M N : X.Modules) (U : X.Opens) (hx : x ∈ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (modulesStalkTensorIso x M N).hom.hom
        (grpGerm X.toRingedSpace
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N).val x U hx
          (toTensorSheafSection X.toRingedSpace M N (op U) (m ⊗ₜ n))) =
      (show (modulesStalkFunctor X x).obj M from grpGerm X.toRingedSpace M.val x U hx m) ⊗ₜ
        (show (modulesStalkFunctor X x).obj N from grpGerm X.toRingedSpace N.val x U hx n) :=
  (congrArg (TensorProduct.congr (stalkModuleEquiv x M).symm (stalkModuleEquiv x N).symm)
    (tensorStalkIso_germ X.toRingedSpace x M N U hx m n)).trans rfl

/-- Transporting `TensorProduct.map a b` along `stalkModuleEquiv` gives the tensor product
`a' ⊗ₘ b'` of morphisms of stalks, whenever `a`, `b` agree pointwise with `a'`, `b'`. -/
theorem congr_stalkModuleEquiv_map {M M' N N' : X.Modules}
    (a : grpStalk X.toRingedSpace M.val x →ₗ[X.presheaf.stalk x]
      grpStalk X.toRingedSpace M'.val x)
    (b : grpStalk X.toRingedSpace N.val x →ₗ[X.presheaf.stalk x]
      grpStalk X.toRingedSpace N'.val x)
    (a' : (modulesStalkFunctor X x).obj M ⟶ (modulesStalkFunctor X x).obj M')
    (b' : (modulesStalkFunctor X x).obj N ⟶ (modulesStalkFunctor X x).obj N')
    (ha : ∀ m, a m = a'.hom m) (hb : ∀ n, b n = b'.hom n)
    (w : grpStalk X.toRingedSpace M.val x ⊗[X.presheaf.stalk x]
      grpStalk X.toRingedSpace N.val x) :
    TensorProduct.congr (stalkModuleEquiv x M').symm (stalkModuleEquiv x N').symm
        (TensorProduct.map a b w) =
      (a' ⊗ₘ b').hom (TensorProduct.congr (stalkModuleEquiv x M).symm
        (stalkModuleEquiv x N).symm w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m n =>
    rw [TensorProduct.map_tmul, TensorProduct.congr_tmul, TensorProduct.congr_tmul,
      ModuleCat.MonoidalCategory.tensorHom_tmul]
    exact congrArg₂ (fun s t => s ⊗ₜ t) (ha m) (hb n)
  | add p q hp hq => simp only [map_add, hp, hq]

/-- The isomorphism `modulesStalkTensorIso` is natural in the first variable: it intertwines the
stalk of `φ ⊗ 𝟙 N` with `φ_x ⊗ 𝟙 N_x`. -/
theorem modulesStalkTensorIso_naturality_left {M M' : X.Modules} (φ : M ⟶ M') (N : X.Modules) :
    (modulesStalkFunctor X x).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map φ).app N) ≫
      (modulesStalkTensorIso x M' N).hom =
      (modulesStalkTensorIso x M N).hom ≫
        ((curriedTensor (ModuleCat.{u} (X.presheaf.stalk x))).map
          ((modulesStalkFunctor X x).map φ)).app ((modulesStalkFunctor X x).obj N) := by
  rw [← Category.comp_id (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map φ).app N),
    ← CategoryTheory.Functor.map_id (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M')) N]
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  have hz := DFunLike.congr_fun (tensorStalkIso_natural X.toRingedSpace x M N M' N φ (𝟙 N)) z
  refine (congrArg (fun t => TensorProduct.congr (stalkModuleEquiv x M').symm
    (stalkModuleEquiv x N).symm t) hz.symm).trans ?_
  exact congr_stalkModuleEquiv_map x _ _ _ (𝟙 _) (fun _ => rfl)
    (fun n => Stacks.SheafOfModules.KFlatStalkCriterion.stalkMapL_id X.toRingedSpace x N n) _

/-- The isomorphism `modulesStalkTensorIso` is natural in the second variable: it intertwines the
stalk of `𝟙 M ⊗ ψ` with `𝟙 M_x ⊗ ψ_x`. -/
theorem modulesStalkTensorIso_naturality_right (M : X.Modules) {N N' : X.Modules} (ψ : N ⟶ N') :
    (modulesStalkFunctor X x).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).map ψ) ≫
      (modulesStalkTensorIso x M N').hom =
      (modulesStalkTensorIso x M N).hom ≫
        ((curriedTensor (ModuleCat.{u} (X.presheaf.stalk x))).obj
          ((modulesStalkFunctor X x).obj M)).map ((modulesStalkFunctor X x).map ψ) := by
  rw [← Category.id_comp (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).map ψ),
    ← NatTrans.id_app (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M)) N,
    ← CategoryTheory.Functor.map_id (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) M]
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  have hz := DFunLike.congr_fun (tensorStalkIso_natural X.toRingedSpace x M N M N' (𝟙 M) ψ) z
  refine (congrArg (fun t => TensorProduct.congr (stalkModuleEquiv x M).symm
    (stalkModuleEquiv x N').symm t) hz.symm).trans ?_
  exact congr_stalkModuleEquiv_map x _ _ (𝟙 _) _
    (fun m => Stacks.SheafOfModules.KFlatStalkCriterion.stalkMapL_id X.toRingedSpace x M m)
    (fun _ => rfl) _

/-- Maps out of the stalk of a tensor product are determined by their values on the germs of
pure tensors. -/
theorem modulesStalkTensor_hom_ext (M N : X.Modules) {T : ModuleCat.{u} (X.presheaf.stalk x)}
    (φ ψ : (modulesStalkFunctor X x).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N) ⟶ T)
    (h : ∀ (U : X.Opens) (hx : x ∈ U) (m : M.val.obj (op U)) (n : N.val.obj (op U)),
      φ.hom (grpGerm X.toRingedSpace
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N).val x U hx
          (toTensorSheafSection X.toRingedSpace M N (op U) (m ⊗ₜ n))) =
        ψ.hom (grpGerm X.toRingedSpace
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N).val x U hx
          (toTensorSheafSection X.toRingedSpace M N (op U) (m ⊗ₜ n)))) :
    φ = ψ := by
  rw [← cancel_epi (modulesStalkTensorIso x M N).inv]
  refine ModuleCat.hom_ext (TensorProduct.ext' fun a b => ?_)
  obtain ⟨U₁, hU₁, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
    M.val.presheaf a
  obtain ⟨U₂, hU₂, n₀, hn⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
    N.val.presheaf b
  have hmem : x ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
  have hm' : grpGerm X.toRingedSpace M.val x (U₁ ⊓ U₂) hmem
      ((M.val.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op).hom m₀) = a :=
    (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) M.val.presheaf
      (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) x hmem m₀).trans hm
  have hn' : grpGerm X.toRingedSpace N.val x (U₁ ⊓ U₂) hmem
      ((N.val.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op).hom n₀) = b :=
    (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) N.val.presheaf
      (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) x hmem n₀).trans hn
  have he := modulesStalkTensorIso_hom_germ x M N (U₁ ⊓ U₂) hmem
    ((M.val.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op).hom m₀)
    ((N.val.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op).hom n₀)
  rw [hm', hn'] at he
  have hi : (modulesStalkTensorIso x M N).inv.hom (a ⊗ₜ b) =
      grpGerm X.toRingedSpace
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N).val x (U₁ ⊓ U₂) hmem
        (toTensorSheafSection X.toRingedSpace M N (op (U₁ ⊓ U₂))
          ((M.val.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op).hom m₀ ⊗ₜ
            (N.val.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op).hom n₀)) := by
    rw [← he]
    exact (modulesStalkTensorIso x M N).hom_inv_id_apply _
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply, hi]
  exact h _ _ _ _

end Stacks.ModuleSkyscraper
