module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Topologies.BaseIdealMultiple
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
public import StacksFrontier.RingTheory.TensorProduct.PushoutAction

/-!
# Modules with an action of an algebra, and modules on the base change

Let `p : X ⟶ V` be a morphism from an algebraic space to an affine scheme of the site, let
`q : W ⟶ V` be a morphism of affine schemes, and let `X' = W ×_V X` with its projections
`pr : X' ⟶ X` and `pr' : X' ⟶ W`.  Writing `A = Γ(V, 𝒪)` and `R = Γ(W, 𝒪)`, an `𝒪_X`-module `F`
together with a ring map `ρ : R → End(F)` which on `A` is multiplication by the pulled back
functions is the same thing as a module over `p^* R̃ = pr_* 𝒪_{X'}`, and Stacks 67.20.10 says
that a quasi-coherent such module is `pr_* F'` for a unique quasi-coherent `𝒪_{X'}`-module `F'`.

This file constructs `F'` and proves `pr_* F' ≅ F` compatibly with the action of `R`, with no
appeal to a general relative spectrum: `F'` is the quotient of `pr^* F` by the relations
`pr^*(ρ r) = r`, for `r ∈ R`, and on the base change `U ×_X X' = U ×_V W` of an affine étale
chart `U` of `X` its sections are `Γ(U) ⊗_A R ⊗_{Γ(U)} F(U)` modulo those relations, which is
`F(U)` by `Algebra.IsPushout.sub_tmul_actionLift_mem`.

## Main definitions

* `AlgebraicGeometry.Space.pullbackFunction`: the pullback `pr'^♯ r` of a function on `W`, a
  global function on `X'`.
* `AlgebraicGeometry.Space.moduleOfActionRelations`: the morphism `∐_{r ∈ R} pr^* F ⟶ pr^* F` whose
  `r`-th component is `pr^*(ρ r) - pr'^♯ r`.
* `AlgebraicGeometry.Space.moduleOfAction`: the `𝒪_{X'}`-module `F'`, its cokernel.
* `AlgebraicGeometry.Space.toPushforwardModuleOfAction`: the comparison
  `F ⟶ pr_* F'`, `s ↦ [1 ⊗ s]`, with `pr_*` computed on the base-changed charts.

## Main results

* `AlgebraicGeometry.Space.isIso_toPushforwardModuleOfAction`: the comparison is an isomorphism
  when `F` is quasi-coherent.
* `AlgebraicGeometry.Space.toPushforwardModuleOfAction_comp_globalSmul`: it carries `ρ r` to
  multiplication by `pr'^♯ r`.

## References

* [Stacks Project, Tag 08AT](https://stacks.math.columbia.edu/tag/08AT)
* [Stacks Project, Lemma 67.20.10](https://stacks.math.columbia.edu/tag/082A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V W : BigFppfOver B S hS} {X X' : AlgebraicSpaces B S hS}
  (p : X ⟶ schemeSpace V) (q : W ⟶ V) (pr' : X' ⟶ schemeSpace W) (pr : X' ⟶ X)

/-- The pullback along `pr' : X' ⟶ W` of a function on `W`, as a global section of the structure
sheaf of `X'`. -/
abbrev pullbackFunction (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    ↥(GlobalSectionRing ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X'.1 X'.2).O))) :=
  pullbackToGlobalFunctions B S hS X' W pr' r

variable (F : Modules.{u, u} B S hS X.1 X.2)
  (ρ : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) →+* End F)

/-- The relations `pr^*(ρ r) - pr'^♯ r` on `pr^* F`, assembled over all `r ∈ R`. -/
def moduleOfActionRelations :
    (∐ fun _ : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) => (modulePullback B S hS pr).obj F) ⟶
      (modulePullback B S hS pr).obj F :=
  Sigma.desc fun r => (modulePullback B S hS pr).map (ρ r).asHom -
    globalSmul _ (pullbackFunction B S hS pr' r) ((modulePullback B S hS pr).obj F)

/-- **The `𝒪_{X'}`-module attached to an `𝒪_X`-module with an action of `Γ(W)`**: the quotient
of `pr^* F` by the relations `pr^*(ρ r) = pr'^♯ r`. -/
def moduleOfAction : Modules.{u, u} B S hS X'.1 X'.2 :=
  cokernel (moduleOfActionRelations B S hS pr' pr F ρ)

/-- The projection `pr^* F ⟶ F'`. -/
def moduleOfActionπ : (modulePullback B S hS pr).obj F ⟶ moduleOfAction B S hS pr' pr F ρ :=
  cokernel.π _

/-- In `F'`, the endomorphism `pr^*(ρ r)` of `pr^* F` and multiplication by `pr'^♯ r` agree after
composing with the projection `pr^* F ⟶ F'`. -/
theorem ι_moduleOfActionRelations_moduleOfActionπ (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    (modulePullback B S hS pr).map (ρ r).asHom ≫ moduleOfActionπ B S hS pr' pr F ρ =
      globalSmul _ (pullbackFunction B S hS pr' r) _ ≫ moduleOfActionπ B S hS pr' pr F ρ := by
  have h := Sigma.ι _ r ≫= cokernel.condition (moduleOfActionRelations B S hS pr' pr F ρ)
  rw [comp_zero, ← Category.assoc, moduleOfActionRelations, Sigma.ι_comp_desc, Preadditive.sub_comp,
    sub_eq_zero] at h
  exact h

/-- On `F'` multiplication by `pr'^♯ r` is induced by `ρ r`. -/
theorem moduleOfActionπ_globalSmul (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    moduleOfActionπ B S hS pr' pr F ρ ≫
        globalSmul _ (pullbackFunction B S hS pr' r) (moduleOfAction B S hS pr' pr F ρ) =
      (modulePullback B S hS pr).map (ρ r).asHom ≫ moduleOfActionπ B S hS pr' pr F ρ := by
  rw [comp_globalSmul, ι_moduleOfActionRelations_moduleOfActionπ]

/-- The coproduct of copies of `pr^* F` indexed by `Γ(W)` is quasi-coherent when `F` is. -/
private theorem isQuasicoherentOnSite_coproduct_modulePullback (hF : F.IsQuasicoherentOnSite) :
    (∐ fun _ : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) =>
      (modulePullback B S hS pr).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_coproduct_of_isCartesian B S hS X'.1 X'.2 _
    (coproductIsCoproduct fun _ : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) =>
      (modulePullback B S hS pr).obj F)
    fun _ => isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X'.1 X'.2 _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS pr F hF)

/-- `F'` is quasi-coherent when `F` is: it is a cokernel of quasi-coherent modules. -/
theorem isQuasicoherentOnSite_moduleOfAction (hF : F.IsQuasicoherentOnSite) :
    (moduleOfAction B S hS pr' pr F ρ).IsQuasicoherentOnSite :=
  @isQuasicoherentOnSite_cokernel_unconditional B S hS X'.1 X'.2 _ _
    (isQuasicoherentOnSite_coproduct_modulePullback B S hS (W := W) pr F hF)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS pr F hF) _

variable (hrep : yoneda.relativelyRepresentable pr.hom)

/-- The section `[1 ⊗ s]` of `F'` over the base-changed chart `U ×_X X'`. -/
def toModuleOfActionApp (U : SmallEtale B S hS X.1) (s : F.val.obj (op U)) :
    (moduleOfAction B S hS pr' pr F ρ).val.obj (op (baseChangeChart B S hS pr hrep U)) :=
  (moduleOfActionπ B S hS pr' pr F ρ).val.app (op (baseChangeChart B S hS pr hrep U))
    (modulePullbackChartSection B S hS pr F (baseChangeChartDiagram B S hS pr hrep U) s)

/-- The map `s ↦ [1 ⊗ s]` is additive. -/
theorem toModuleOfActionApp_add (U : SmallEtale B S hS X.1) (s t : F.val.obj (op U)) :
    toModuleOfActionApp B S hS pr' pr F ρ hrep U (s + t) =
      toModuleOfActionApp B S hS pr' pr F ρ hrep U s +
        toModuleOfActionApp B S hS pr' pr F ρ hrep U t :=
  (congrArg ((moduleOfActionπ B S hS pr' pr F ρ).val.app
    (op (baseChangeChart B S hS pr hrep U))).hom
    (modulePullbackChartSection_add B S hS pr F (baseChangeChartDiagram B S hS pr hrep U) s
      t)).trans (map_add _ _ _)

/-- The map `s ↦ [1 ⊗ s]` is linear along the restriction `Γ(U) → Γ(U ×_X X')`. -/
theorem toModuleOfActionApp_smul (U : SmallEtale B S hS X.1)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj (op U))
    (s : F.val.obj (op U)) :
    toModuleOfActionApp B S hS pr' pr F ρ hrep U (a • s) =
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X'.1 X'.2).O)).obj.obj
            (op (baseChangeChart B S hS pr hrep U)) from
        chartDiagramRestrict B S hS pr (baseChangeChartDiagram B S hS pr hrep U) a) •
        toModuleOfActionApp B S hS pr' pr F ρ hrep U s :=
  (congrArg ((moduleOfActionπ B S hS pr' pr F ρ).val.app
    (op (baseChangeChart B S hS pr hrep U))).hom
    (modulePullbackChartSection_smul B S hS pr F (baseChangeChartDiagram B S hS pr hrep U) a
      s)).trans (((moduleOfActionπ B S hS pr' pr F ρ).val.app
        (op (baseChangeChart B S hS pr hrep U))).hom.map_smul
        (show ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X'.1 X'.2).O)).obj.obj
            (op (baseChangeChart B S hS pr hrep U)) from
          chartDiagramRestrict B S hS pr (baseChangeChartDiagram B S hS pr hrep U) a) _)

/-- The map `s ↦ [1 ⊗ s]` commutes with restriction along a morphism of charts. -/
theorem toModuleOfActionApp_naturality {U₁ U₂ : SmallEtale B S hS X.1} (g : U₁ ⟶ U₂)
    (s : F.val.obj (op U₂)) :
    (moduleOfAction B S hS pr' pr F ρ).val.map ((smallBaseChange B S hS pr hrep).map g).op
        (toModuleOfActionApp B S hS pr' pr F ρ hrep U₂ s) =
      toModuleOfActionApp B S hS pr' pr F ρ hrep U₁ (F.val.map g.op s) := by
  have h := (modulePullbackChartFMap B S hS pr F).naturality
    (baseChangeChartDiagram B S hS pr hrep U₂) (baseChangeChartDiagram B S hS pr hrep U₁)
    ((smallBaseChange B S hS pr hrep).map g) g (smallBaseChange_map_snd B S hS pr hrep g) s
  have h' : modulePullbackChartSection B S hS pr F (baseChangeChartDiagram B S hS pr hrep U₁)
      (F.val.map g.op s) = ((modulePullback B S hS pr).obj F).val.map
        ((smallBaseChange B S hS pr hrep).map g).op
        (modulePullbackChartSection B S hS pr F (baseChangeChartDiagram B S hS pr hrep U₂) s) :=
    (modulePullbackChartFMap_app B S hS pr F (baseChangeChartDiagram B S hS pr hrep U₁)
      (F.val.map g.op s)).symm.trans
      (h.trans (congrArg (((modulePullback B S hS pr).obj F).val.map
        ((smallBaseChange B S hS pr hrep).map g).op).hom
        (modulePullbackChartFMap_app B S hS pr F (baseChangeChartDiagram B S hS pr hrep U₂) s)))
  refine (PresheafOfModules.naturality_apply (moduleOfActionπ B S hS pr' pr F ρ).val
    ((smallBaseChange B S hS pr hrep).map g).op
    (modulePullbackChartSection B S hS pr F (baseChangeChartDiagram B S hS pr hrep U₂)
      s)).symm.trans
    ?_
  exact congrArg ((moduleOfActionπ B S hS pr' pr F ρ).val.app
    (op (baseChangeChart B S hS pr hrep U₁))).hom h'.symm

/-- **The comparison `F ⟶ pr_* F'`**, with the direct image computed on the base-changed
charts: a section `s` of `F` over `U` goes to the class of `1 ⊗ s` over `U ×_X X'`. -/
def toPushforwardModuleOfAction :
    F ⟶ (smallBaseChangeModulePushforward B S hS pr hrep).obj
      (moduleOfAction B S hS pr' pr F ρ) where
  val := PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := toModuleOfActionApp B S hS pr' pr F ρ hrep U.unop
          map_zero' := by
            have := toModuleOfActionApp_add B S hS pr' pr F ρ hrep U.unop 0 0
            rw [add_zero] at this
            exact left_eq_add.mp this
          map_add' := toModuleOfActionApp_add B S hS pr' pr F ρ hrep U.unop }
      naturality := fun {U₁ U₂} g => by
        ext s
        exact (toModuleOfActionApp_naturality B S hS pr' pr F ρ hrep g.unop s).symm }
    (fun U a s => toModuleOfActionApp_smul B S hS pr' pr F ρ hrep U.unop a s)

/-- On sections over a chart `U`, the comparison `F ⟶ pr_* F'` is `s ↦ [1 ⊗ s]`. -/
theorem toPushforwardModuleOfAction_app (U : SmallEtale B S hS X.1) (s : F.val.obj (op U)) :
    (toPushforwardModuleOfAction B S hS pr' pr F ρ hrep).val.app (op U) s =
      toModuleOfActionApp B S hS pr' pr F ρ hrep U s :=
  rfl

/-! ### The comparison is bijective on affine charts -/

/-- The action of `Γ(W)` on the sections of `F` over a chart `U`, by `S`-linear endomorphisms. -/
def moduleOfActionChartAction (U : SmallEtale B S hS X.1) :
    Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) →+*
      Module.End (chartRing B S hS X.1 X.2 U) (F.val.obj (op U)) where
  toFun r := ((ρ r).asHom.val.app (op U)).hom
  map_one' := by rw [map_one]; rfl
  map_mul' r r' := by rw [map_mul]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_add' r r' := by rw [map_add]; rfl

/-- The action of `r` on `F(U)` is the component of `ρ r` at `U`. -/
theorem moduleOfActionChartAction_apply (U : SmallEtale B S hS X.1)
    (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) (m : F.val.obj (op U)) :
    moduleOfActionChartAction B S hS F ρ U r m = (ρ r).asHom.val.app (op U) m :=
  rfl

/-- The relation `pr^*(ρ r) - pr'^♯ r` on `pr^* F`. -/
abbrev moduleOfActionRelation (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    (modulePullback B S hS pr).obj F ⟶ (modulePullback B S hS pr).obj F :=
  (modulePullback B S hS pr).map (ρ r).asHom -
    globalSmul _ (pullbackFunction B S hS pr' r) ((modulePullback B S hS pr).obj F)

/-- The `r`-th component of `moduleOfActionRelations` is `moduleOfActionRelation r`. -/
theorem ι_moduleOfActionRelations (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    Sigma.ι _ r ≫ moduleOfActionRelations B S hS pr' pr F ρ =
      moduleOfActionRelation B S hS pr' pr F ρ r :=
  Sigma.ι_comp_desc _ r

/-- Each relation `pr^*(ρ r) - pr'^♯ r` vanishes in `F'`. -/
theorem moduleOfActionRelation_moduleOfActionπ (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    moduleOfActionRelation B S hS pr' pr F ρ r ≫ moduleOfActionπ B S hS pr' pr F ρ = 0 := by
  rw [Preadditive.sub_comp, ι_moduleOfActionRelations_moduleOfActionπ, sub_self]

/-- Every section of `∐ pr^* F` over an affine chart is carried by `moduleOfActionRelations`
into the sum of the images of the individual relations. -/
theorem moduleOfActionRelations_app_mem (Z : SmallEtale B S hS X'.1)
    (hZ : IsAffine ((SmallEtale.toOver B S hS X'.1 ⋙ BigFppfOver.toScheme B S hS).obj Z))
    (N : AddSubgroup (((modulePullback B S hS pr).obj F).val.obj (op Z)))
    (hN : ∀ r x, (moduleOfActionRelation B S hS pr' pr F ρ r).val.app (op Z) x ∈ N)
    (x : (∐ fun _ : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) =>
      (modulePullback B S hS pr).obj F).val.obj (op Z)) :
    (moduleOfActionRelations B S hS pr' pr F ρ).val.app (op Z) x ∈ N := by
  classical
  obtain ⟨y, rfl⟩ := (Stacks.Sites.bijective_coproductSectionsMap _
    (coproductIsCoproduct fun _ : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) =>
      (modulePullback B S hS pr).obj F) Z
    (isQuasiCompactObject_of_isAffine B S hS X'.1 Z hZ)).2 x
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]; exact N.zero_mem
  | of r v =>
    have h := Stacks.Sites.coproductSectionsMap_lof
      (Cofan.mk _ (Sigma.ι fun _ : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) =>
        (modulePullback B S hS pr).obj F)) (op Z) r v
    rw [← DirectSum.lof_eq_of (R := ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X'.1 X'.2).O)).obj.obj (op Z)), h]
    have h2 := congrArg (fun φ => φ.val.app (op Z) v)
      (ι_moduleOfActionRelations B S hS pr' pr F ρ r)
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
      LinearMap.coe_comp, Function.comp_apply] at h2
    change (moduleOfActionRelations B S hS pr' pr F ρ).val.app (op Z)
      ((Sigma.ι (fun _ : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) =>
        (modulePullback B S hS pr).obj F) r).val.app (op Z) v) ∈ N
    rw [h2]
    exact hN r v
  | add y y' hy hy' => rw [map_add, map_add]; exact N.add_mem hy hy'

section Bijective

variable {pr' pr} (sq : IsPullback pr' pr (schemeSpaceMap q) p)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]

/-- The comparison `F(U) → F'(U ×_X X')` is bijective on an affine chart `U`; this is the shared
proof of injectivity and surjectivity. -/
private theorem bijective_toModuleOfActionApp_aux (sq : IsPullback pr' pr (schemeSpaceMap q) p)
    (hF : F.IsQuasicoherentOnSite)
    (hρ : ∀ a, (ρ (((BigFppfOver.toScheme B S hS).map q).appTop a)).asHom =
      globalSmul _ (pullbackToGlobalFunctions B S hS X V p a) F)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Bijective (AddMonoidHom.mk' (toModuleOfActionApp B S hS pr' pr F ρ hrep U)
      (toModuleOfActionApp_add B S hS pr' pr F ρ hrep U)) := by
  have hpr : IsAffineHom B S hS pr.hom :=
    IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _ sq)
      (isAffineHom_yoneda_map B S hS q)
  have hU' := isAffine_smallBaseChange_obj B S hS pr hrep hpr U hU
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hU
  set d := baseChangeChartDiagram B S hS pr hrep U
  have hpo := isPushout_appTop_of_isPullback
    ((isPullback_smallBaseChange_of_isPullback B S hS p q sq hrep U).map
      (BigFppfOver.toScheme B S hS))
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map q).appTop.hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (chartRing B S hS X.1 X.2 U) :=
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (U.1.hom ≫ p.hom))).appTop.hom.toAlgebra
  let : Algebra (chartRing B S hS X.1 X.2 U)
      (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) :=
    chartDiagramAlgebra B S hS pr d
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
      (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) :=
    ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (hrep.fst U.1.hom ≫ pr'.hom))).appTop.hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) :=
    ((algebraMap (chartRing B S hS X.1 X.2 U)
      (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U))).comp
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (chartRing B S hS X.1 X.2 U))).toAlgebra
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (chartRing B S hS X.1 X.2 U)
      (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
      (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) :=
    IsScalarTower.of_algebraMap_eq fun x => (ConcreteCategory.congr_hom hpo.w x).symm
  have : Algebra.IsPushout Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) (chartRing B S hS X.1 X.2 U)
      (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) :=
    CommRingCat.isPushout_iff_isPushout.1 hpo
  have : Algebra.IsPushout Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (chartRing B S hS X.1 X.2 U) Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
      (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) :=
    Algebra.IsPushout.symm inferInstance
  set ρU := moduleOfActionChartAction B S hS F ρ U
  have hρU : ∀ a, ρU (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) a) =
      algebraMap (chartRing B S hS X.1 X.2 U) (Module.End (chartRing B S hS X.1 X.2 U)
        (F.val.obj (op U))) (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (chartRing B S hS X.1 X.2 U) a) := by
    intro a
    ext m
    change (ρ (((BigFppfOver.toScheme B S hS).map q).appTop a)).asHom.val.app (op U) m = _
    rw [hρ a]
    rfl
  let bc : chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U) ⊗[
      chartRing B S hS X.1 X.2 U] F.val.obj (op U) →ₗ[chartRing B S hS X'.1 X'.2
        (baseChangeChart B S hS pr hrep U)]
      ((modulePullback B S hS pr).obj F).val.obj (op (baseChangeChart B S hS pr hrep U)) :=
    modulePullbackChartBaseChange B S hS pr F d
  have hbc : Function.Bijective bc :=
    bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS pr F hF d hU' hU
  have key : ∀ r z, bc (Algebra.IsPushout.relationMap
      (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) ρU r z) =
      (moduleOfActionRelation B S hS pr' pr F ρ r).val.app (op (baseChangeChart B S hS pr hrep U))
        (bc z) := by
    intro r z
    have h1 := modulePullbackChartBaseChange_map B S hS pr (ρ r).asHom d z
    have e1 : bc ((ρU r).baseChange
        (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) z) =
        ((modulePullback B S hS pr).map (ρ r).asHom).val.app
          (op (baseChangeChart B S hS pr hrep U)) (bc z) := by
      rw [LinearMap.baseChange_eq_lTensor]
      exact h1.symm
    have e2 : bc ((algebraMap Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
        (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) r • z)) =
        (globalSmul _ (pullbackFunction B S hS pr' r)
          ((modulePullback B S hS pr).obj F)).val.app (op (baseChangeChart B S hS pr hrep U))
          (bc z) :=
      bc.map_smul (algebraMap Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
        (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) r) z
    change bc ((ρU r).baseChange
        (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) z -
      algebraMap Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
        (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) r • z) = _
    refine (bc.map_sub _ _).trans ?_
    rw [e1, e2]
    rfl
  let U' := baseChangeChart B S hS pr hrep U
  let c := ((moduleOfActionπ B S hS pr' pr F ρ).val.app (op U')).hom
  have hσ : ∀ m, modulePullbackChartSection B S hS pr F d m =
      bc ((1 : chartRing B S hS X'.1 X'.2 U') ⊗ₜ[chartRing B S hS X.1 X.2 U] m) := fun m =>
    ((modulePullbackChartBaseChange_tmul B S hS pr F d 1 m).trans (one_smul _ _)).symm
  have hcrel : ∀ n ∈ Algebra.IsPushout.relations (chartRing B S hS X'.1 X'.2 U') ρU,
      c (bc n) = 0 := by
    intro n hn
    refine Submodule.iSup_induction (motive := fun (x : chartRing B S hS X'.1 X'.2 U' ⊗[
      chartRing B S hS X.1 X.2 U] F.val.obj (op U)) => c (bc x) = 0) _ hn ?_ ?_ ?_
    · rintro r _ ⟨z, rfl⟩
      rw [key]
      exact congrArg (fun φ => φ.val.app (op U') (bc z))
        (moduleOfActionRelation_moduleOfActionπ B S hS pr' pr F ρ r)
    · exact (congrArg c (map_zero bc)).trans (map_zero c)
    · intro x y hx hy
      exact (congrArg c (map_add bc x y)).trans ((map_add c _ _).trans (by rw [hx, hy, add_zero]))
  have hP : ((modulePullback B S hS pr).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS pr F hF
  have hSig := isQuasicoherentOnSite_coproduct_modulePullback B S hS (W := W) pr F hF
  have hF' := isQuasicoherentOnSite_moduleOfAction B S hS pr' pr F ρ hF
  have hIm : (Abelian.image (moduleOfActionRelations B S hS pr' pr F ρ)).IsQuasicoherentOnSite :=
    have := isClosedUnderKernels_quasicoherentSheaves_smallEtale B S hS X'.1 X'.2
    (SheafOfModules.isQuasicoherentOnSite _).prop_kernel
      (cokernel.π (moduleOfActionRelations B S hS pr' pr F ρ)) hP hF'
  have hcsurj : Function.Surjective c :=
    surjective_val_app_of_epi_of_isQuasicoherentOnSite
      (moduleOfActionπ B S hS pr' pr F ρ)
      (inferInstanceAs (Epi (cokernel.π (moduleOfActionRelations B S hS pr' pr F ρ)))) hP hF' U' hU'
  have hexact := SheafOfModules.exact_val_app_cokernel_π
    (moduleOfActionRelations B S hS pr' pr F ρ) (op U')
    (surjective_val_app_of_epi_of_isQuasicoherentOnSite
      (Abelian.factorThruImage (moduleOfActionRelations B S hS pr' pr F ρ)) inferInstance hSig hIm
      U' hU')
  refine ⟨(injective_iff_map_eq_zero _).2 fun m hm => ?_, fun w => ?_⟩
  · change c (modulePullbackChartSection B S hS pr F d m) = 0 at hm
    obtain ⟨x, hx⟩ := (hexact _).1 hm
    have hmem := moduleOfActionRelations_app_mem B S hS pr' pr F ρ U' hU'
      ((Algebra.IsPushout.relations (chartRing B S hS X'.1 X'.2 U') ρU).map
        (bc : _ →ₗ[chartRing B S hS X'.1 X'.2 U'] _)).toAddSubgroup
      (fun r y => by
        obtain ⟨z, rfl⟩ := hbc.2 y
        exact ⟨_, Algebra.IsPushout.relationMap_mem_relations _ ρU r z, key r z⟩) x
    rw [hx, hσ m] at hmem
    obtain ⟨n, hn, hn'⟩ := hmem
    have h2 : Algebra.IsPushout.actionLift ρU hρU n = 0 :=
      Algebra.IsPushout.relations_le_ker_actionLift ρU hρU hn
    have h3 : Algebra.IsPushout.actionLift ρU hρU n = m := by
      have h1 : n = 1 ⊗ₜ m := hbc.1 hn'
      subst h1
      exact Algebra.IsPushout.actionLift_tmul_one ρU hρU m
    exact h3.symm.trans h2
  · obtain ⟨x, hx⟩ := hcsurj w
    obtain ⟨z, hz⟩ := hbc.2 x
    refine ⟨Algebra.IsPushout.actionLift ρU hρU z, ?_⟩
    refine (congrArg c (hσ _)).trans ?_
    have h := hcrel _ (Algebra.IsPushout.sub_tmul_actionLift_mem ρU hρU z)
    rw [map_sub, map_sub, sub_eq_zero] at h
    exact h.symm.trans ((congrArg c hz).trans hx)

include sq in
/-- **The comparison `F(U) → F'(U ×_X X')` is injective on an affine chart `U`**, for a
quasi-coherent `F` whose action of `Γ(W)` restricts on `Γ(V)` to multiplication by the pulled
back functions. -/
theorem injective_toModuleOfActionApp (hF : F.IsQuasicoherentOnSite)
    (hρ : ∀ a, (ρ (((BigFppfOver.toScheme B S hS).map q).appTop a)).asHom =
      globalSmul _ (pullbackToGlobalFunctions B S hS X V p a) F)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Injective (AddMonoidHom.mk' (toModuleOfActionApp B S hS pr' pr F ρ hrep U)
      (toModuleOfActionApp_add B S hS pr' pr F ρ hrep U)) :=
  (bijective_toModuleOfActionApp_aux B S hS p q F ρ hrep sq hF hρ U hU).1

include sq in
/-- **The comparison `F(U) → F'(U ×_X X')` is surjective on an affine chart `U`**, for a
quasi-coherent `F` whose action of `Γ(W)` restricts on `Γ(V)` to multiplication by the pulled
back functions. -/
theorem surjective_toModuleOfActionApp (hF : F.IsQuasicoherentOnSite)
    (hρ : ∀ a, (ρ (((BigFppfOver.toScheme B S hS).map q).appTop a)).asHom =
      globalSmul _ (pullbackToGlobalFunctions B S hS X V p a) F)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Surjective (AddMonoidHom.mk' (toModuleOfActionApp B S hS pr' pr F ρ hrep U)
      (toModuleOfActionApp_add B S hS pr' pr F ρ hrep U)) :=
  (bijective_toModuleOfActionApp_aux B S hS p q F ρ hrep sq hF hρ U hU).2

include sq in
/-- **The comparison `F(U) → F'(U ×_X X')` is bijective on an affine chart `U`**, for a
quasi-coherent `F` whose action of `Γ(W)` restricts on `Γ(V)` to multiplication by the pulled
back functions. -/
theorem bijective_toModuleOfActionApp (hF : F.IsQuasicoherentOnSite)
    (hρ : ∀ a, (ρ (((BigFppfOver.toScheme B S hS).map q).appTop a)).asHom =
      globalSmul _ (pullbackToGlobalFunctions B S hS X V p a) F)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Bijective (AddMonoidHom.mk' (toModuleOfActionApp B S hS pr' pr F ρ hrep U)
      (toModuleOfActionApp_add B S hS pr' pr F ρ hrep U)) :=
  ⟨injective_toModuleOfActionApp B S hS p q F ρ hrep sq hF hρ U hU,
    surjective_toModuleOfActionApp B S hS p q F ρ hrep sq hF hρ U hU⟩

include sq in
/-- **`pr_* F' ≅ F`**: the comparison of `AlgebraicGeometry.Space.toPushforwardModuleOfAction`
is an isomorphism for a quasi-coherent `F`. -/
theorem isIso_toPushforwardModuleOfAction (hF : F.IsQuasicoherentOnSite)
    (hρ : ∀ a, (ρ (((BigFppfOver.toScheme B S hS).map q).appTop a)).asHom =
      globalSmul _ (pullbackToGlobalFunctions B S hS X V p a) F) :
    IsIso (toPushforwardModuleOfAction B S hS pr' pr F ρ hrep) :=
  SmallEtale.isIso_of_bijective_app_of_isAffineChart B S hS X.1 X.2 _ fun U hU =>
    bijective_toModuleOfActionApp B S hS p q F ρ hrep sq hF hρ U hU

end Bijective

/-- **The comparison carries `ρ r` to multiplication by `pr'^♯ r`.** -/
theorem toPushforwardModuleOfAction_comp_globalSmul
    (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    toPushforwardModuleOfAction B S hS pr' pr F ρ hrep ≫
        (smallBaseChangeModulePushforward B S hS pr hrep).map
          (globalSmul _ (pullbackFunction B S hS pr' r) (moduleOfAction B S hS pr' pr F ρ)) =
      (ρ r).asHom ≫ toPushforwardModuleOfAction B S hS pr' pr F ρ hrep := by
  ext U s
  have h := congrArg (fun φ => φ.val.app (op (baseChangeChart B S hS pr hrep U.unop))
    (modulePullbackChartSection B S hS pr F (baseChangeChartDiagram B S hS pr hrep U.unop) s))
    (moduleOfActionπ_globalSmul B S hS pr' pr F ρ r)
  refine h.trans ?_
  exact congrArg ((moduleOfActionπ B S hS pr' pr F ρ).val.app
    (op (baseChangeChart B S hS pr hrep U.unop))).hom
    (modulePullbackChartSection_map B S hS pr F (ρ r).asHom
      (baseChangeChartDiagram B S hS pr hrep U.unop) s)

/-- On sections, the comparison carries `ρ r` to multiplication by `pr'^♯ r`. -/
theorem toModuleOfActionApp_action (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (U : SmallEtale B S hS X.1) (s : F.val.obj (op U)) :
    toModuleOfActionApp B S hS pr' pr F ρ hrep U ((ρ r).asHom.val.app (op U) s) =
      (pullbackFunction B S hS pr' r).1 (op (baseChangeChart B S hS pr hrep U)) •
        toModuleOfActionApp B S hS pr' pr F ρ hrep U s :=
  (congrArg (fun φ => φ.val.app (op U) s)
    (toPushforwardModuleOfAction_comp_globalSmul B S hS pr' pr F ρ hrep r)).symm

section Coherent

variable {pr' pr} (sq : IsPullback pr' pr (schemeSpaceMap q) p)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]

include sq in
/-- **`F'` is coherent** on a locally Noetherian `X'` as soon as, over an affine étale chart `U`
of `X` surjective on points, the sections of `F` are generated over `Γ(U)` by the
`ρ(Γ(W))`-translates of finitely many sections. -/
theorem isCoherent_moduleOfAction (hF : F.IsQuasicoherentOnSite)
    (hρ : ∀ a, (ρ (((BigFppfOver.toScheme B S hS).map q).appTop a)).asHom =
      globalSmul _ (pullbackToGlobalFunctions B S hS X V p a) F)
    [Fact (HasEtaleLocalProperty B S hS X'.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hUsurj : IsSurjective B S hS U.1.hom) (g : Finset (F.val.obj (op U)))
    (hg : Submodule.span (chartRing B S hS X.1 X.2 U)
      {x | ∃ r, ∃ y ∈ g, x = (ρ r).asHom.val.app (op U) y} = ⊤) :
    IsCoherent B S hS X'.1 X'.2 (moduleOfAction B S hS pr' pr F ρ) := by
  have hpr : IsAffineHom B S hS pr.hom :=
    IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _ sq)
      (isAffineHom_yoneda_map B S hS q)
  have hrep := relativelyRepresentable_of_isAffineHom B S hS pr hpr
  have hU' := isAffine_smallBaseChange_obj B S hS pr hrep hpr U hU
  have hF' := isQuasicoherentOnSite_moduleOfAction B S hS pr' pr F ρ hF
  have hbij := bijective_toModuleOfActionApp B S hS p q F ρ hrep sq hF hρ U hU
  refine (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS X'.1 X'.2 _).2
    ⟨hF', isFiniteType_of_coversTop_affine_moduleFinite B S hS X'.1 X'.2 _
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X'.1 X'.2 _ hF')
      (fun _ : PUnit.{u + 2} => baseChangeChart B S hS pr hrep U) (fun _ => hU')
      (SmallEtale.coversTop_of_isSurjective B S hS X'.1 X'.2 _
        (isSurjective_smallBaseChange_obj_hom B S hS pr hrep U hUsurj))
      (fun _ => ?_)⟩
  classical
  refine ⟨⟨g.image (toModuleOfActionApp B S hS pr' pr F ρ hrep U), ?_⟩⟩
  rw [eq_top_iff]
  intro y hy
  obtain ⟨m, rfl⟩ := hbij.2 y
  clear hy
  have hm : m ∈ (⊤ : Submodule (chartRing B S hS X.1 X.2 U) (F.val.obj (op U))) :=
    Submodule.mem_top
  rw [← hg] at hm
  change toModuleOfActionApp B S hS pr' pr F ρ hrep U m ∈ _
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, y, hy, rfl⟩ := hx
    rw [toModuleOfActionApp_action]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2
      (Finset.mem_image_of_mem _ hy)))
  | zero =>
    have := toModuleOfActionApp_add B S hS pr' pr F ρ hrep U 0 0
    rw [add_zero, left_eq_add] at this
    rw [this]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [toModuleOfActionApp_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [toModuleOfActionApp_smul]
    exact Submodule.smul_mem _ _ hx

end Coherent

end AlgebraicGeometry.Space

end
