module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeModuleOfAction
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyFlatTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineBijective
public import StacksFrontier.RingTheory.PushoutTensor

/-!
# The direct image of a pullback along an affine base change is a tensor product

Let `p : X ⟶ V` be a morphism from an algebraic space to an affine scheme of the site, let
`q : W ⟶ V` be a morphism of affine schemes, and let `X' = W ×_V X` with projections
`pr : X' ⟶ X` and `pr' : X' ⟶ W`.  Write `A = Γ(V, 𝒪)` and `R = Γ(W, 𝒪)`.  For an
`𝒪_X`-module `ℱ` the abelian sheaf `ℱ ⊗_A R` (the sheafification of `U ↦ ℱ(U) ⊗_A R`,
`AlgebraicGeometry.Space.sectionsTensorSheaf`) maps to the underlying abelian sheaf of
`pr_* pr^* ℱ` by `x ⊗ r ↦ r · pr^* x`, and this is an isomorphism when `ℱ` is quasi-coherent.
Over an affine étale chart `U` of `X` the base change `U ×_X X' = U ×_V W` is affine with ring
`Γ(U) ⊗_A R`, and the sections of `pr^* ℱ` there are `(Γ(U) ⊗_A R) ⊗_{Γ(U)} ℱ(U) = ℱ(U) ⊗_A R`;
the affine charts cover, so the comparison is an isomorphism of sheaves.  The isomorphism
carries multiplication by `r ∈ R` on the right factor to multiplication by the pulled back
function `pr'^♯ r`.

This is the identification `g'_* ℱ_B = ℱ ⊗_{\underline{A}} \underline{B}` in the proof of
[Stacks, Tag 073K].

## Main definitions

* `AlgebraicGeometry.Space.baseChangeTensorModule`: `R = Γ(W)` as a module over `A = Γ(V)`.
* `AlgebraicGeometry.Space.sectionsTensorToPushforwardPullback`: the comparison of presheaves
  `ℱ(U) ⊗_A R ⟶ (pr^* ℱ)(U ×_X X')`, `x ⊗ r ↦ pr'^♯ r · pr^* x`.
* `AlgebraicGeometry.Space.sectionsTensorPushforwardPullbackIso`: the isomorphism of abelian
  sheaves `ℱ ⊗_A R ≅ pr_* pr^* ℱ`, for quasi-coherent `ℱ`.

## Main results

* `AlgebraicGeometry.Space.bijective_sectionsTensorToPushforwardPullbackApp`: the comparison is
  bijective over the affine charts.
* `AlgebraicGeometry.Space.sectionsTensorPushforwardPullbackIso_hom_naturality`: the
  isomorphism carries multiplication by `r` to multiplication by `pr'^♯ r`.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V W : BigFppfOver B S hS} {X X' : AlgebraicSpaces B S hS}

/-- The ring `R = Γ(W, 𝒪)` of an object of the site over `V`, as a module over `A = Γ(V, 𝒪)`
through `q : W ⟶ V`. -/
def baseChangeTensorModule (q : W ⟶ V) :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  letI := ((BigFppfOver.toScheme B S hS).map q).appTop.hom.toAlgebra
  ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)

/-- The functions of an object `V` of the site pulled back along `p : X ⟶ V`, as global sections
of the structure sheaf of the small étale site of `X`.  This is
`AlgebraicGeometry.Space.pullbackToGlobalFunctions`, with its values read in the ring of global
sections over which the cohomology of `𝒪_X`-modules is a module. -/
def baseFunctionsToGlobalSections (p : X ⟶ schemeSpace V) :
    Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+*
      GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) :=
  pullbackToGlobalFunctions B S hS X V p

/-- The value of `baseFunctionsToGlobalSections` at `a` is the global function `p^♯ a`. -/
theorem baseFunctionsToGlobalSections_apply (p : X ⟶ schemeSpace V)
    (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    (baseFunctionsToGlobalSections B S hS p a : GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).1 =
      (pullbackToGlobalFunctions B S hS X V p a).1 :=
  rfl

variable (p : X ⟶ schemeSpace V) (q : W ⟶ V) (pr' : X' ⟶ schemeSpace W) {pr : X' ⟶ X}
  (sq : IsPullback pr' pr (schemeSpaceMap q) p)
  (hrep : yoneda.relativelyRepresentable pr.hom) (F : Modules.{u, u} B S hS X.1 X.2)

/-- Two additive maps out of a tensor product that agree on pure tensors agree everywhere. -/
private theorem tensorProduct_addMonoidHom_ext {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N]
    {f g : M ⊗[R] N →+ P} (h : ∀ x y, f (x ⊗ₜ[R] y) = g (x ⊗ₜ[R] y)) (z : M ⊗[R] N) :
    f z = g z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The chart sections `pr^* x` of the pullback over the base-changed charts are natural in the
chart. -/
theorem modulePullbackChartSection_baseChangeChart_naturality {U₁ U₂ : SmallEtale B S hS X.1}
    (g : U₁ ⟶ U₂) (s : F.val.obj (op U₂)) :
    modulePullbackChartSection B S hS pr F (baseChangeChartDiagram B S hS pr hrep U₁)
        (F.val.map g.op s) = ((modulePullback B S hS pr).obj F).val.map
        ((smallBaseChange B S hS pr hrep).map g).op
        (modulePullbackChartSection B S hS pr F (baseChangeChartDiagram B S hS pr hrep U₂) s) := by
  have h := (modulePullbackChartFMap B S hS pr F).naturality
    (baseChangeChartDiagram B S hS pr hrep U₂) (baseChangeChartDiagram B S hS pr hrep U₁)
    ((smallBaseChange B S hS pr hrep).map g) g (smallBaseChange_map_snd B S hS pr hrep g) s
  exact (modulePullbackChartFMap_app B S hS pr F (baseChangeChartDiagram B S hS pr hrep U₁)
      (F.val.map g.op s)).symm.trans
      (h.trans (congrArg (((modulePullback B S hS pr).obj F).val.map
        ((smallBaseChange B S hS pr hrep).map g).op).hom
        (modulePullbackChartFMap_app B S hS pr F (baseChangeChartDiagram B S hS pr hrep U₂) s)))

/-- The functions of `V` restricted to an étale chart `U` of `X`, through `p : X ⟶ V`. -/
abbrev chartFunctionOfBase (U : SmallEtale B S hS X.1) :
    Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+* chartRing B S hS X.1 X.2 U :=
  chartRingHomOfGlobal B S hS X (baseFunctionsToGlobalSections B S hS p) (op U)

include sq in
/-- **The functions of `V` restricted to a base-changed chart agree through `U` and through
`W`.**  For `a ∈ Γ(V)`, the restriction to `U ×_X X'` of `p^♯ a|_U` is `pr'^♯ (q^♯ a)`. -/
theorem chartDiagramRestrict_pullbackToGlobalFunctions (U : SmallEtale B S hS X.1)
    (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    chartDiagramRestrict B S hS pr (baseChangeChartDiagram B S hS pr hrep U)
        (chartFunctionOfBase B S hS p U a) =
      (pullbackFunction B S hS pr' (((BigFppfOver.toScheme B S hS).map q).appTop a)).1
        (op (baseChangeChart B S hS pr hrep U)) := by
  have h := congrArg (fun f => ((BigFppfOver.toScheme B S hS).map f).appTop a)
    (preimage_comp_eq_of_isPullback B S hS p q sq hrep U)
  simp only [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  exact h

/-! ### The comparison of presheaves -/

/-- The functions of `W` restricted to the base change `U ×_X X'` of an étale chart `U` of `X`,
through `pr' : X' ⟶ W`. -/
abbrev baseChangeChartFunction (U : SmallEtale B S hS X.1) :
    Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) →+*
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj.obj
        (op (baseChangeChart B S hS pr hrep U)) :=
  (globalSectionEval _ (op (baseChangeChart B S hS pr hrep U))).comp
    (pullbackToGlobalFunctions B S hS X' W pr')

/-- The chart sections `x ↦ pr^* x` of the pullback over the base change `U ×_X X'` of an étale
chart `U` of `X`. -/
def baseChangeChartSection (U : SmallEtale B S hS X.1) :
    F.val.obj (op U) →+
      ((modulePullback B S hS pr).obj F).val.obj (op (baseChangeChart B S hS pr hrep U)) where
  toFun := modulePullbackChartSection B S hS pr F (baseChangeChartDiagram B S hS pr hrep U)
  map_zero' := by
    have h := modulePullbackChartSection_add B S hS pr F (baseChangeChartDiagram B S hS pr hrep U)
      0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  map_add' := modulePullbackChartSection_add B S hS pr F (baseChangeChartDiagram B S hS pr hrep U)

/-- The biadditive map `(x, r) ↦ pr'^♯ r · pr^* x` underlying
`AlgebraicGeometry.Space.sectionsTensorToPushforwardPullbackApp`. -/
def sectionsTensorToPushforwardPullbackPairing (U : SmallEtale B S hS X.1) :
    F.val.obj (op U) →+ Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) →+
      ((modulePullback B S hS pr).obj F).val.obj (op (baseChangeChart B S hS pr hrep U)) :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
      (fun r => baseChangeChartFunction B S hS pr' hrep U r •
        baseChangeChartSection B S hS hrep F U x)
      (fun r r' => by simp only [map_add, add_smul]))
    (fun x y => AddMonoidHom.ext fun r => by
      simp only [map_add, smul_add, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply])

/-- The pairing sends `(x, r)` to `pr'^♯ r · pr^* x`. -/
theorem sectionsTensorToPushforwardPullbackPairing_apply (U : SmallEtale B S hS X.1)
    (x : F.val.obj (op U)) (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    sectionsTensorToPushforwardPullbackPairing B S hS pr' hrep F U x r =
      baseChangeChartFunction B S hS pr' hrep U r • baseChangeChartSection B S hS hrep F U x :=
  rfl

include sq in
/-- `pr^*` carries multiplication by the function `p^♯ a` of `V` to multiplication by
`pr'^♯ (q^♯ a)`. -/
theorem baseChangeChartSection_smul (U : SmallEtale B S hS X.1)
    (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (x : F.val.obj (op U)) :
    baseChangeChartSection B S hS hrep F U
        (chartFunctionOfBase B S hS p U a • x) =
      baseChangeChartFunction B S hS pr' hrep U (((BigFppfOver.toScheme B S hS).map q).appTop a) •
        baseChangeChartSection B S hS hrep F U x := by
  have e := modulePullbackChartSection_smul B S hS pr F (baseChangeChartDiagram B S hS pr hrep U)
    (chartFunctionOfBase B S hS p U a) x
  rw [chartDiagramRestrict_pullbackToGlobalFunctions B S hS p q pr' sq hrep U a] at e
  exact e

include sq in
/-- The pairing `(x, r) ↦ pr'^♯ r · pr^* x` is balanced over `A = Γ(V)`. -/
theorem sectionsTensorToPushforwardPullbackPairing_smul (U : SmallEtale B S hS X.1)
    (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (x : F.val.obj (op U))
    (r : baseChangeTensorModule B S hS q) :
    sectionsTensorToPushforwardPullbackPairing B S hS pr' hrep F U
        (chartFunctionOfBase B S hS p U a • x) r =
      sectionsTensorToPushforwardPullbackPairing B S hS pr' hrep F U x (a • r) := by
  have h2 : baseChangeChartFunction B S hS pr' hrep U
      (a • r : baseChangeTensorModule B S hS q) =
      baseChangeChartFunction B S hS pr' hrep U (((BigFppfOver.toScheme B S hS).map q).appTop a) *
        baseChangeChartFunction B S hS pr' hrep U r :=
    map_mul _ _ _
  change baseChangeChartFunction B S hS pr' hrep U r •
      baseChangeChartSection B S hS hrep F U (chartFunctionOfBase B S hS p U a • x) =
    baseChangeChartFunction B S hS pr' hrep U (a • r : baseChangeTensorModule B S hS q) •
      baseChangeChartSection B S hS hrep F U x
  rw [baseChangeChartSection_smul B S hS p q pr' sq hrep F U a x, h2, smul_smul, mul_comm]

include sq in
/-- The comparison `ℱ(U) ⊗_A R ⟶ (pr^* ℱ)(U ×_X X')`, `x ⊗ r ↦ pr'^♯ r · pr^* x`, over an
étale chart `U` of `X`. -/
def sectionsTensorToPushforwardPullbackApp (U : SmallEtale B S hS X.1) :
    ((moduleSectionsOverRing B S hS X (baseFunctionsToGlobalSections B S hS p) F).obj (op U)) ⊗[
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] (baseChangeTensorModule B S hS q) →+
      ((modulePullback B S hS pr).obj F).val.obj (op (baseChangeChart B S hS pr hrep U)) :=
  TensorProduct.liftAddHom (sectionsTensorToPushforwardPullbackPairing B S hS pr' hrep F U)
    (fun a x r => sectionsTensorToPushforwardPullbackPairing_smul B S hS p q pr' sq hrep F U a x r)

/-- The comparison sends `x ⊗ r` to `pr'^♯ r · pr^* x`. -/
theorem sectionsTensorToPushforwardPullbackApp_tmul (U : SmallEtale B S hS X.1)
    (x : (moduleSectionsOverRing B S hS X (baseFunctionsToGlobalSections B S hS p) F).obj (op U))
    (r : baseChangeTensorModule B S hS q) :
    sectionsTensorToPushforwardPullbackApp B S hS p q pr' sq hrep F U (x ⊗ₜ r) =
      baseChangeChartFunction B S hS pr' hrep U r • baseChangeChartSection B S hS hrep F U x :=
  rfl

/-- The restriction of the functions `pr'^♯ r` between base-changed charts. -/
theorem baseChangeChartFunction_naturality {U₁ U₂ : SmallEtale B S hS X.1} (g : U₁ ⟶ U₂)
    (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj.map
        ((smallBaseChange B S hS pr hrep).map g).op (baseChangeChartFunction B S hS pr' hrep U₂ r) =
      baseChangeChartFunction B S hS pr' hrep U₁ r :=
  (pullbackToGlobalFunctions B S hS X' W pr' r).2 ((smallBaseChange B S hS pr hrep).map g).op

/-- The comparison over the étale charts is natural in the chart. -/
theorem sectionsTensorToPushforwardPullbackApp_naturality {U₁ U₂ : SmallEtale B S hS X.1}
    (g : U₁ ⟶ U₂)
    (z : (moduleSectionsOverRing B S hS X (baseFunctionsToGlobalSections B S hS p) F).obj (op U₂)
      ⊗[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] (baseChangeTensorModule B S hS q)) :
    sectionsTensorToPushforwardPullbackApp B S hS p q pr' sq hrep F U₁
        (LinearMap.rTensor (baseChangeTensorModule B S hS q)
          ((moduleSectionsOverRing B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
            g.op).hom z) =
      ((modulePullback B S hS pr).obj F).val.map ((smallBaseChange B S hS pr hrep).map g).op
        (sectionsTensorToPushforwardPullbackApp B S hS p q pr' sq hrep F U₂ z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    exact (((modulePullback B S hS pr).obj F).val.map
      ((smallBaseChange B S hS pr hrep).map g).op).hom.map_add _ _ |>.symm
  | tmul x r =>
    rw [LinearMap.rTensor_tmul, sectionsTensorToPushforwardPullbackApp_tmul,
      sectionsTensorToPushforwardPullbackApp_tmul]
    refine Eq.trans ?_ (((modulePullback B S hS pr).obj F).val.map_smul
      ((smallBaseChange B S hS pr hrep).map g).op _ _).symm
    exact congrArg₂ (· • ·) (baseChangeChartFunction_naturality B S hS pr' hrep g r).symm
      (modulePullbackChartSection_baseChangeChart_naturality B S hS hrep F g x)

/-- **The comparison `ℱ ⊗_A R ⟶ pr_* pr^* ℱ` of presheaves of abelian groups** on the small
étale site of `X`, `x ⊗ r ↦ pr'^♯ r · pr^* x`, with `pr_*` computed on the base-changed charts
and sections raised to the universe `u + 1`. -/
def sectionsTensorToPushforwardPullback :
    (moduleSectionsOverRing B S hS X (baseFunctionsToGlobalSections B S hS p) F ⋙
        (MonoidalCategory.tensoringRight
          (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))).obj
          (baseChangeTensorModule B S hS q)) ⋙
      forget₂ (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} ⟶
    ((moduleToAbelianSheaf B S hS X).obj ((smallBaseChangeModulePushforward B S hS pr hrep).obj
      ((modulePullback B S hS pr).obj F))).obj where
  app U := AddCommGrpCat.uliftFunctor.{u + 1, u}.map
    (AddCommGrpCat.ofHom (sectionsTensorToPushforwardPullbackApp B S hS p q pr' sq hrep F U.unop))
  naturality {U₁ U₂} f := by
    ext ⟨z⟩
    exact congrArg ULift.up
      (sectionsTensorToPushforwardPullbackApp_naturality B S hS p q pr' sq hrep F f.unop z)

section Bijective

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]

include sq in
/-- **The comparison is bijective over the affine charts** when `ℱ` is quasi-coherent: there
`U ×_X X'` is affine with ring `Γ(U) ⊗_A R`, and the sections of `pr^* ℱ` over it are
`(Γ(U) ⊗_A R) ⊗_{Γ(U)} ℱ(U) = ℱ(U) ⊗_A R`. -/
theorem bijective_sectionsTensorToPushforwardPullbackApp (hF : F.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Bijective (sectionsTensorToPushforwardPullbackApp B S hS p q pr' sq hrep F U) := by
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
  let : Module Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (F.val.obj (op U)) :=
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (chartRing B S hS X.1 X.2 U))
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (chartRing B S hS X.1 X.2 U)
      (F.val.obj (op U)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hbc : Function.Bijective (modulePullbackChartBaseChange B S hS pr F d) :=
    bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS pr F hF d hU' hU
  have hc := Stacks.Algebra.PushoutBaseChange.bijective_can
    (A := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (B := chartRing B S hS X.1 X.2 U) (A' := Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (B' := chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) (M := F.val.obj (op U))
  have hcomm := (TensorProduct.comm Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
    ((moduleSectionsOverRing B S hS X (baseFunctionsToGlobalSections B S hS p) F).obj (op U))
    (baseChangeTensorModule B S hS q)).bijective
  set bc := modulePullbackChartBaseChange B S hS pr F d
  set c := Stacks.Algebra.PushoutBaseChange.can Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
    (chartRing B S hS X.1 X.2 U) Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
    (chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U)) (F.val.obj (op U))
  set e := TensorProduct.comm Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
    ((moduleSectionsOverRing B S hS X (baseFunctionsToGlobalSections B S hS p) F).obj (op U))
    (baseChangeTensorModule B S hS q)
  have hfun : ⇑(sectionsTensorToPushforwardPullbackApp B S hS p q pr' sq hrep F U) =
      fun z => bc (c (e z)) :=
    funext (tensorProduct_addMonoidHom_ext (g := bc.toAddMonoidHom.comp
      (c.toAddMonoidHom.comp e.toAddMonoidHom)) fun x r =>
      ((congrArg bc (Stacks.Algebra.PushoutBaseChange.can_tmul
        (A := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (B := chartRing B S hS X.1 X.2 U)
        (A' := Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
        (B' := chartRing B S hS X'.1 X'.2 (baseChangeChart B S hS pr hrep U))
        (M := F.val.obj (op U)) r x)).trans
          (modulePullbackChartBaseChange_tmul B S hS pr F d _ x)).symm)
  rw [hfun]
  exact hbc.comp (hc.comp hcomm)

end Bijective

/-! ### The action of `A` on `ℱ ⊗_A A` -/

/-- Multiplication by `a` on the factor `A` of `M ⊗_A A` is multiplication by `a` on `M`. -/
theorem rid_lTensor_toSpanSingleton {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M]
    [Module R M] (a : R) (z : M ⊗[R] R) :
    TensorProduct.rid R M (LinearMap.lTensor M (LinearMap.toSpanSingleton R R a) z) =
      a • TensorProduct.rid R M z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul x b =>
    simp only [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, TensorProduct.rid_tmul,
      smul_eq_mul, mul_smul]
    exact smul_comm b a x


/-- Multiplication by `a ∈ A` on `A`, as an endomorphism of the `A`-module `A`; under
`AlgebraicGeometry.Space.sectionsTensorSheafUnitIso` it is multiplication by `φ a` on `ℱ`. -/
theorem sectionsTensorSheaf_map_toSpanSingleton_comp_unitIso_hom
    (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) a)) ≫
        (sectionsTensorSheafUnitIso B S hS X (baseFunctionsToGlobalSections B S hS p) F).hom =
      (sectionsTensorSheafUnitIso B S hS X (baseFunctionsToGlobalSections B S hS p) F).hom ≫
        (moduleToAbelianSheaf B S hS X).map
          (globalSmul _ (baseFunctionsToGlobalSections B S hS p a) F) := by
  have hw : Functor.whiskerRight (Functor.whiskerLeft
        (moduleSectionsOverRing B S hS X (baseFunctionsToGlobalSections B S hS p) F)
        ((MonoidalCategory.tensoringRight
          (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))).map
          (ModuleCat.ofHom (LinearMap.toSpanSingleton Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) a))))
        (forget₂ (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) AddCommGrpCat.{u} ⋙
          AddCommGrpCat.uliftFunctor.{u + 1, u}) ≫
        (Functor.isoWhiskerRight (Functor.isoWhiskerLeft
            (moduleSectionsOverRing B S hS X (baseFunctionsToGlobalSections B S hS p) F)
            (MonoidalCategory.rightUnitorNatIso
              (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))))
          (forget₂ (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) AddCommGrpCat.{u} ⋙
            AddCommGrpCat.uliftFunctor.{u + 1, u}) ≪≫
        NatIso.ofComponents
            (F := moduleSectionsOverRing B S hS X (baseFunctionsToGlobalSections B S hS p) F ⋙
              forget₂ (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) AddCommGrpCat.{u} ⋙
                AddCommGrpCat.uliftFunctor.{u + 1, u})
          (G := ((moduleToAbelianSheaf B S hS X).obj F).obj) (fun _ => Iso.refl _)
          (fun _ => rfl)).hom =
      (Functor.isoWhiskerRight (Functor.isoWhiskerLeft
            (moduleSectionsOverRing B S hS X (baseFunctionsToGlobalSections B S hS p) F)
            (MonoidalCategory.rightUnitorNatIso
              (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))))
          (forget₂ (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) AddCommGrpCat.{u} ⋙
            AddCommGrpCat.uliftFunctor.{u + 1, u}) ≪≫
        NatIso.ofComponents
            (F := moduleSectionsOverRing B S hS X (baseFunctionsToGlobalSections B S hS p) F ⋙
              forget₂ (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) AddCommGrpCat.{u} ⋙
                AddCommGrpCat.uliftFunctor.{u + 1, u})
          (G := ((moduleToAbelianSheaf B S hS X).obj F).obj) (fun _ => Iso.refl _)
          (fun _ => rfl)).hom ≫
        ((moduleToAbelianSheaf B S hS X).map
          (globalSmul _ (baseFunctionsToGlobalSections B S hS p a) F)).hom := by
    ext U ⟨z⟩
    exact congrArg ULift.up (rid_lTensor_toSpanSingleton _ a z)
  exact presheafToSheaf_map_comp_counit_of_comp_eq _ _ _ _ hw

/-! ### The isomorphism of sheaves -/

include sq in
/-- **`ℱ ⊗_A R ≅ pr_* pr^* ℱ`** for a quasi-coherent `ℱ`: the comparison
`AlgebraicGeometry.Space.sectionsTensorToPushforwardPullback`, sheafified, as an isomorphism of
abelian sheaves on the small étale site of `X`. -/
def sectionsTensorPushforwardPullbackIso [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (hF : F.IsQuasicoherentOnSite) :
    (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).obj
        (baseChangeTensorModule B S hS q) ≅
      (moduleToAbelianSheaf B S hS X).obj
        ((modulePushforward B S hS pr).obj ((modulePullback B S hS pr).obj F)) :=
  @asIso _ _ _ _ ((presheafToSheaf _ _).map
      (sectionsTensorToPushforwardPullback B S hS p q pr' sq hrep F))
    (SmallEtale.isIso_presheafToSheaf_map_of_bijective_app_of_isAffineChart B S hS X.1 X.2
      (sectionsTensorToPushforwardPullback B S hS p q pr' sq hrep F) fun U hU =>
        ULift.up_bijective.comp
          ((bijective_sectionsTensorToPushforwardPullbackApp B S hS p q pr' sq hrep F hF U
            hU).comp ULift.down_bijective)) ≪≫
    asIso ((sheafificationAdjunction (SmallEtale.topology B S hS X.1)
          AddCommGrpCat.{u + 1}).counit.app
      ((moduleToAbelianSheaf B S hS X).obj ((smallBaseChangeModulePushforward B S hS pr hrep).obj
        ((modulePullback B S hS pr).obj F)))) ≪≫
    (moduleToAbelianSheaf B S hS X).mapIso
      ((modulePushforwardChartIso B S hS pr hrep).app ((modulePullback B S hS pr).obj F)).symm

/-! ### Compatibility with the action of `R` -/

/-- Multiplication by `r ∈ R` on `R`, as an endomorphism of the `A`-module `R`. -/
def baseChangeTensorModuleMul (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    baseChangeTensorModule B S hS q ⟶ baseChangeTensorModule B S hS q :=
  letI := ((BigFppfOver.toScheme B S hS).map q).appTop.hom.toAlgebra
  ModuleCat.ofHom (LinearMap.mulLeft Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) r)

/-- On sections, the comparison carries multiplication by `r` on the factor `R` to
multiplication by `pr'^♯ r`. -/
theorem sectionsTensorToPushforwardPullbackApp_lTensor (U : SmallEtale B S hS X.1)
    (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (z : (moduleSectionsOverRing B S hS X (baseFunctionsToGlobalSections B S hS p) F).obj (op U)
      ⊗[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] (baseChangeTensorModule B S hS q)) :
    sectionsTensorToPushforwardPullbackApp B S hS p q pr' sq hrep F U
        (LinearMap.lTensor _ (baseChangeTensorModuleMul B S hS q r).hom z) =
      baseChangeChartFunction B S hS pr' hrep U r •
        sectionsTensorToPushforwardPullbackApp B S hS p q pr' sq hrep F U z := by
  refine tensorProduct_addMonoidHom_ext
    (f := (sectionsTensorToPushforwardPullbackApp B S hS p q pr' sq hrep F U).comp
      (LinearMap.lTensor _ (baseChangeTensorModuleMul B S hS q r).hom).toAddMonoidHom)
    (g := (DistribSMul.toAddMonoidHom _ (baseChangeChartFunction B S hS pr' hrep U r)).comp
      (sectionsTensorToPushforwardPullbackApp B S hS p q pr' sq hrep F U)) (fun x s => ?_) z
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    DistribSMul.toAddMonoidHom_apply]
  rw [LinearMap.lTensor_tmul, sectionsTensorToPushforwardPullbackApp_tmul,
    sectionsTensorToPushforwardPullbackApp_tmul, smul_smul]
  exact congrArg (· • baseChangeChartSection B S hS hrep F U x)
    (map_mul (baseChangeChartFunction B S hS pr' hrep U) r s)

/-- The comparison of presheaves carries multiplication by `r` on the factor `R` to
multiplication by `pr'^♯ r` on `pr_* pr^* ℱ`. -/
theorem sectionsTensorToPushforwardPullback_comp_smul
    (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    Functor.whiskerRight (Functor.whiskerLeft
        (moduleSectionsOverRing B S hS X (baseFunctionsToGlobalSections B S hS p) F)
        ((MonoidalCategory.tensoringRight
          (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))).map
          (baseChangeTensorModuleMul B S hS q r)))
        (forget₂ (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) AddCommGrpCat.{u} ⋙
          AddCommGrpCat.uliftFunctor.{u + 1, u}) ≫
        sectionsTensorToPushforwardPullback B S hS p q pr' sq hrep F =
      sectionsTensorToPushforwardPullback B S hS p q pr' sq hrep F ≫
        ((moduleToAbelianSheaf B S hS X).map ((smallBaseChangeModulePushforward B S hS pr hrep).map
          (globalSmul _ (pullbackFunction B S hS pr' r)
            ((modulePullback B S hS pr).obj F)))).hom := by
  ext U ⟨z⟩
  exact congrArg ULift.up
    (sectionsTensorToPushforwardPullbackApp_lTensor B S hS p q pr' sq hrep F U.unop r z)

include sq in
/-- **The isomorphism `ℱ ⊗_A R ≅ pr_* pr^* ℱ` carries multiplication by `r ∈ R` to
multiplication by `pr'^♯ r`.** -/
theorem sectionsTensorPushforwardPullbackIso_hom_naturality
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (hF : F.IsQuasicoherentOnSite)
    (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
        (baseChangeTensorModuleMul B S hS q r) ≫
        (sectionsTensorPushforwardPullbackIso B S hS p q pr' sq hrep F hF).hom =
      (sectionsTensorPushforwardPullbackIso B S hS p q pr' sq hrep F hF).hom ≫
        (moduleToAbelianSheaf B S hS X).map ((modulePushforward B S hS pr).map
          (globalSmul _ (pullbackFunction B S hS pr' r) ((modulePullback B S hS pr).obj F))) := by
  have hgen := presheafToSheaf_map_comp_counit_of_comp_eq
    (sectionsTensorToPushforwardPullback B S hS p q pr' sq hrep F)
    (sectionsTensorToPushforwardPullback B S hS p q pr' sq hrep F) _
    ((moduleToAbelianSheaf B S hS X).map ((smallBaseChangeModulePushforward B S hS pr hrep).map
      (globalSmul _ (pullbackFunction B S hS pr' r) ((modulePullback B S hS pr).obj F))))
    (sectionsTensorToPushforwardPullback_comp_smul B S hS p q pr' sq hrep F r)
  have h3 := ((moduleToAbelianSheaf B S hS X).map_comp _ _).symm.trans
    ((congrArg (moduleToAbelianSheaf B S hS X).map
      ((modulePushforwardChartIso B S hS pr hrep).inv.naturality
        (globalSmul _ (pullbackFunction B S hS pr' r) ((modulePullback B S hS pr).obj F)))).trans
      ((moduleToAbelianSheaf B S hS X).map_comp _ _))
  have e : (sectionsTensorPushforwardPullbackIso B S hS p q pr' sq hrep F hF).hom =
      ((presheafToSheaf _ _).map (sectionsTensorToPushforwardPullback B S hS p q pr' sq hrep F) ≫
        (sheafificationAdjunction (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).counit.app
          ((moduleToAbelianSheaf B S hS X).obj
            ((smallBaseChangeModulePushforward B S hS pr hrep).obj
              ((modulePullback B S hS pr).obj F)))) ≫
        (moduleToAbelianSheaf B S hS X).map
          ((modulePushforwardChartIso B S hS pr hrep).inv.app
            ((modulePullback B S hS pr).obj F)) := by
    simp only [sectionsTensorPushforwardPullbackIso, Iso.trans_hom, asIso_hom, Category.assoc]
    rfl
  rw [e]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hgen).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h3).trans (Category.assoc _ _ _).symm)))

end AlgebraicGeometry.Space
