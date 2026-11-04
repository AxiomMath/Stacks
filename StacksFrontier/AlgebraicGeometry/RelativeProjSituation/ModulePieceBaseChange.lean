module

public import StacksFrontier.AlgebraicGeometry.ModuleChartLocality.BaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ChartHypothesisBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.SectionModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.DegreewiseBaseChange

/-!
# The homogeneous pieces of the graded modules of sections base-change along a morphism

Let `g : S' ⟶ S`, let `s` and `s'` be relative `Proj` situations over `S` and `S'`, let `Φ`
identify the graded algebra of `s'` with the pullback of that of `s`, and let `Ψ` identify a graded
`𝒜'`-module `ℳ'` with the pullback of a graded `𝒜`-module `ℳ` degreewise. For affine opens
`W ⊆ S` and `W' ⊆ g⁻¹W ⊆ S'`, this file proves that the base change of the graded modules of
sections `ℳ(W) ⟶ ℳ'(W')` is a base change **degreewise over the degree-zero rings**: the degree-`i`
piece of `ℳ'(W')` is `𝒜'₀(W') ⊗_{𝒜₀(W)} ℳᵢ(W)`.

This is the module companion of
`Stacks.RelativeProj.Situation.isBaseChange_pieceMap_gradedBaseChange` and it is proved the same
way: quasi-coherence of `ℳᵢ` gives the base change over the base rings,
`ℳ'ᵢ(W') = Γ(S', W') ⊗_{Γ(S, W)} ℳᵢ(W)`, and that is re-based along the degree-zero pushout
`Stacks.RelativeProj.Situation.isPushout_gradeZero_baseChange`.

## Main definitions

* `Stacks.RelativeProj.Situation.modPiece`: a homogeneous piece of a graded module, as a module
  over the structure sheaf of the base.
* `Stacks.RelativeProj.Situation.modulePieceLinearEquiv`: the degree-`i` summand of the graded
  module of sections is `Γ(ℳᵢ, W)`, `Γ(S, W)`-linearly.

## Main results

* `Stacks.RelativeProj.isBaseChange_modulePieceMap_of_isPushout`: re-basing, with the conclusion in
  the spelling of `Stacks.AlgebraicGeometry.ModuleChartLocality.modulePieceMap`.
* `Stacks.RelativeProj.Situation.isBaseChange_pieceSectionModuleHom`: the degreewise base change
  over the base rings.
* `Stacks.RelativeProj.Situation.isBaseChange_modulePieceMap_sectionModuleBaseChange`: **the
  degreewise base change over the degree-zero rings.**

## Implementation notes

As in `StacksFrontier/AlgebraicGeometry/RelativeProjSituation/ChartHypothesisBaseChange.lean`, every
`Algebra`, `Module` and `IsScalarTower` structure that the re-basing relates is passed explicitly,
and the re-basing is stated once at abstract graded data so that its conclusion is syntactically
the consumer's.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite DirectSum
open Stacks.AlgebraicGeometry.ModuleChartLocality

universe u

namespace Stacks.RelativeProj

/-- Degrees of a graded ring act on degrees of a graded module over it by addition. -/
local instance : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

/-! ### Re-basing, at abstract graded modules -/

/-- **The degreewise base change of a semilinear map of graded modules over the degree-zero
rings, from the one over a pair of base rings.** This is
`Stacks.RelativeProj.isBaseChange_of_isPushout_of_linearEquiv` with nothing added, stated so that
its conclusion is syntactically `IsBaseChange ↥(ℬ 0) (modulePieceMap ψ f hf halg i)`. -/
public theorem isBaseChange_modulePieceMap_of_isPushout
    {R S A B M N : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B} [GradedRing 𝒜] [GradedRing ℬ]
    {𝒨 : ℤ → AddSubgroup M} {𝒩 : ℤ → AddSubgroup N}
    [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩]
    [SetLike.GradedSMul 𝒜 𝒨] [SetLike.GradedSMul ℬ 𝒩]
    (ψ : 𝒜 →+*ᵍ ℬ) (f : M →ₛₗ[ψ.toRingHom] N) (hf : ∀ (i : ℤ) {m : M}, m ∈ 𝒨 i → f m ∈ 𝒩 i)
    [aCD : Algebra ↥(𝒜 0) ↥(ℬ 0)]
    (halg : ∀ r : ↥(𝒜 0), (algebraMap ↥(𝒜 0) ↥(ℬ 0) r : B) = ψ (r : A)) (i : ℤ)
    (aRS : Algebra R S) (aRC : Algebra R ↥(𝒜 0)) (aRD : Algebra R ↥(ℬ 0))
    (aSD : Algebra S ↥(ℬ 0))
    (tRSD : IsScalarTower R S ↥(ℬ 0)) (tRCD : IsScalarTower R ↥(𝒜 0) ↥(ℬ 0))
    (push : Algebra.IsPushout R S ↥(𝒜 0) ↥(ℬ 0))
    (mRM : Module R ↥(𝒨 i))
    (tRCM : IsScalarTower R ↥(𝒜 0) ↥(𝒨 i))
    (mRN : Module R (TargetPiece ℬ 𝒩 i))
    (mSN : Module S (TargetPiece ℬ 𝒩 i))
    (tRSN : IsScalarTower R S (TargetPiece ℬ 𝒩 i))
    (tRCN : IsScalarTower R ↥(𝒜 0) (TargetPiece ℬ 𝒩 i))
    (tSDN : IsScalarTower S ↥(ℬ 0) (TargetPiece ℬ 𝒩 i))
    {M₀ N₀ : Type u} [AddCommGroup M₀] [AddCommGroup N₀]
    (mRM₀ : Module R M₀) (mRN₀ : Module R N₀) (mSN₀ : Module S N₀)
    (tRSN₀ : IsScalarTower R S N₀)
    {ρ : M₀ →ₗ[R] N₀} (hρ : IsBaseChange S ρ)
    (eM : ↥(𝒨 i) ≃ₗ[R] M₀)
    (eN : TargetPiece ℬ 𝒩 i ≃ₗ[S] N₀)
    (hφ : ∀ x, eN (modulePieceMap ψ f hf halg i x) = ρ (eM x)) :
    IsBaseChange ↥(ℬ 0) (modulePieceMap ψ f hf halg i) :=
  isBaseChange_of_isPushout_of_linearEquiv
    (R := R) (S := S) (C := ↥(𝒜 0)) (D := ↥(ℬ 0))
    (M := ↥(𝒨 i)) (N := TargetPiece ℬ 𝒩 i)
    (M₀ := M₀) (N₀ := N₀)
    aRS aRC aRD aSD aCD tRSD tRCD push
    mRM _ tRCM mRN mSN _ _ tRSN tRCN tSDN _ mRM₀ mRN₀ mSN₀ tRSN₀ _ hρ eM eN hφ

namespace Situation

/-! ### The degree-`i` summand of the graded module of sections -/

variable {s : Situation.{u}} (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)

/-- The homogeneous piece of degree `i` of a graded module, as a module over the structure sheaf
of the base. Its sections are `Stacks.RelativeProj.Situation.sectionModulePieces`, and this
spelling is what makes their `Γ(S, U)`-module structure and quasi-coherence available. -/
public def modPiece (i : ℤ) : s.base.Modules := ℳ.piece i

/-- Two homogeneous summands of degrees that agree, holding heterogeneously equal elements, are
equal. -/
public theorem sectionModule_of_eq_of_heq (U : s.base.Opens) {j i : ℤ} (e : j = i)
    (y : sectionModulePieces ℳ U j) (z : sectionModulePieces ℳ U i) (hyz : HEq y z) :
    DirectSum.of (sectionModulePieces ℳ U) j y = DirectSum.of (sectionModulePieces ℳ U) i z := by
  subst e
  cases hyz
  rfl

/-- Scaling by a function on the base respects heterogeneous equality across equal degrees. -/
public theorem heq_smul_of_heq (U : s.base.Opens) (r : ↥Γ(s.base, U)) {j i : ℤ} (e : j = i)
    (y : ↥Γ(modPiece ℳ j, U)) (z : ↥Γ(modPiece ℳ i, U)) (hyz : HEq y z) :
    HEq (r • y) (r • z) := by
  subst e
  cases hyz
  rfl

/-- **The action of a degree-zero section coming from the base on a homogeneous summand** is the
action of the function on the base. -/
public theorem baseHom_smul_of (U : s.base.Opens) (i : ℤ) (r : ↥Γ(s.base, U))
    (a : ↥Γ(modPiece ℳ i, U)) :
    ((s.baseHom U r : ↥(s.sectionRingGrading U 0)) : s.sectionRing U) •
        DirectSum.of (sectionModulePieces ℳ U) i a
      = DirectSum.of (sectionModulePieces ℳ U) i (r • a) := by
  refine (congrArg (· • DirectSum.of (sectionModulePieces ℳ U) i a) (s.coe_baseHom U r)).trans ?_
  refine (sectionModule_of_smul_of ℳ U (i := 0) (r • s.onePiece U) a).trans ?_
  refine sectionModule_of_eq_of_heq ℳ U (by simp) _ _ ?_
  refine (heq_of_eq (ℳ.smul_smul_left ((0 : ℕ) : ℤ) i (op U) r (s.onePiece U) a)).trans ?_
  refine heq_smul_of_heq ℳ U r (by simp) _ _ ?_
  exact ℳ.one_smul i (op U) a

attribute [local instance] sectionModuleDecomposition

/-- The action of the graded ring of sections respects the internal gradings, at this file's
`VAdd ℕ ℤ`. -/
local instance sectionModuleGradedSMulLocal (U : s.base.Opens) :
    SetLike.GradedSMul (s.sectionRingGrading U) (sectionModuleGrading ℳ U) :=
  sectionModuleGradedSMul ℳ U

/-- The `Γ(S, U)`-module structure on a homogeneous summand of the graded module of sections, by
restriction of scalars along `Stacks.RelativeProj.Situation.baseHom`. -/
public instance modulePieceBaseModule (U : s.base.Opens) (i : ℤ) :
    Module ↥Γ(s.base, U) ↥(sectionModuleGrading ℳ U i) :=
  Module.compHom _ (s.baseHom U).hom

public instance modulePieceBaseTower (U : s.base.Opens) (i : ℤ) :
    IsScalarTower ↥Γ(s.base, U) ↥(s.sectionRingGrading U 0) ↥(sectionModuleGrading ℳ U i) :=
  ⟨fun x y z => mul_smul ((s.baseHom U).hom x) y z⟩

/-- **The degree-`i` summand of the graded module of sections is the sections of `ℳᵢ`,** and
`Γ(S, U)`-linearly so. The inverse is the degree-`i` component of the direct sum. -/
public def modulePieceLinearEquiv (U : s.base.Opens) (i : ℤ) :
    ↥Γ(modPiece ℳ i, U) ≃ₗ[↥Γ(s.base, U)] ↥(sectionModuleGrading ℳ U i) where
  toFun a := ⟨DirectSum.of (sectionModulePieces ℳ U) i a, ⟨a, rfl⟩⟩
  invFun x := (x : sectionModule ℳ U) i
  map_add' a b := Subtype.ext (map_add (DirectSum.of (sectionModulePieces ℳ U) i) a b)
  map_smul' r a := Subtype.ext (baseHom_smul_of ℳ U i r a).symm
  left_inv a := DirectSum.of_eq_same (β := sectionModulePieces ℳ U) i a
  right_inv x := by
    obtain ⟨a, ha⟩ : ∃ a, DirectSum.of (sectionModulePieces ℳ U) i a = (x : sectionModule ℳ U) :=
      x.2
    refine Subtype.ext ?_
    change DirectSum.of (sectionModulePieces ℳ U) i ((x : sectionModule ℳ U) i)
      = (x : sectionModule ℳ U)
    exact (congrArg (DirectSum.of (sectionModulePieces ℳ U) i)
      ((congrArg (fun z : sectionModule ℳ U => z i) ha).symm.trans
        (DirectSum.of_eq_same (β := sectionModulePieces ℳ U) i a))).trans ha

@[simp] public theorem coe_modulePieceLinearEquiv (U : s.base.Opens) (i : ℤ)
    (a : ↥Γ(modPiece ℳ i, U)) :
    (modulePieceLinearEquiv ℳ U i a : sectionModule ℳ U)
      = DirectSum.of (sectionModulePieces ℳ U) i a := rfl

@[simp] public theorem modulePieceLinearEquiv_symm_apply (U : s.base.Opens) (i : ℤ)
    (x : ↥(sectionModuleGrading ℳ U i)) :
    (modulePieceLinearEquiv ℳ U i).symm x = (x : sectionModule ℳ U) i := rfl

/-- The homogeneous pieces of a graded module with quasi-coherent pieces are quasi-coherent, in the
spelling `Stacks.RelativeProj.Situation.modPiece`. -/
public instance isQuasicoherent_modPiece [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] (i : ℤ) :
    (modPiece ℳ i).IsQuasicoherent :=
  inferInstanceAs (ℳ.piece i).IsQuasicoherent

/-! ### The degreewise base change -/

section BaseChange

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)
  {ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra}
  {ℳ' : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s'.algebra}
  (Ψ : ∀ n : ℤ, (Scheme.Modules.pullback g).obj (ℳ.piece n) ⟶ ℳ'.piece n)

/-- **The degreewise components of the base change of graded modules of sections are semilinear
over `appLE`.** -/
public theorem pieceSectionModuleHom_smul (i : ℤ) (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (r : Γ(s.base, W)) (a : sectionModulePieces ℳ W i) :
    pieceSectionModuleHom g Ψ i W W' h
        ((show s.base.ringCatSheaf.obj.obj (op W) from r) • a) =
      (show s'.base.ringCatSheaf.obj.obj (op W') from (g.appLE W W' h).hom r) •
        pieceSectionModuleHom g Ψ i W W' h a := by
  rw [pieceSectionModuleHom_apply, pieceSectionModuleHom_apply,
    pullbackSection_smul_appLE g (ℳ.piece i) W W' h r a]
  exact ((Ψ i).val.app (op W')).hom.map_smul _ _

/-- The degreewise identification of the two graded modules, read on sections over an open as a
linear equivalence. -/
public noncomputable def modPieceLinearEquiv (i : ℤ) (W' : s'.base.Opens) (hΨ : IsIso (Ψ i)) :
    ↥Γ((Scheme.Modules.pullback g).obj (modPiece ℳ i), W')
      ≃ₗ[↥Γ(s'.base, W')] ↥Γ(modPiece ℳ' i, W') :=
  LinearEquiv.ofLinearMap ((Ψ i).val.app (op W')).hom
    ((inv (Ψ i)).val.app (op W')).hom
    (LinearMap.ext fun y =>
      congrArg (fun k : ℳ'.piece i ⟶ ℳ'.piece i => k.val.app (op W') y)
        (IsIso.inv_hom_id (Ψ i)))
    (LinearMap.ext fun x =>
      congrArg (fun k : (Scheme.Modules.pullback g).obj (ℳ.piece i) ⟶
          (Scheme.Modules.pullback g).obj (ℳ.piece i) => k.val.app (op W') x)
        (IsIso.hom_inv_id (Ψ i)))

@[simp] public theorem modPieceLinearEquiv_apply (i : ℤ) (W' : s'.base.Opens)
    (hΨ : IsIso (Ψ i)) (x : ↥Γ((Scheme.Modules.pullback g).obj (modPiece ℳ i), W')) :
    modPieceLinearEquiv g Ψ i W' hΨ x = (Ψ i).val.app (op W') x := rfl

/-- **The degreewise base change over the base rings.** For affine opens `W ⊆ S` and
`W' ⊆ g⁻¹W ⊆ S'`, extending the scalars of `ℳᵢ(W)` along `g.appLE W W'` gives `ℳ'ᵢ(W')`. This is
`AlgebraicGeometry.isBaseChange_pullbackSection_of_isAffineOpen` for the quasi-coherent module
`ℳᵢ`, transported along the degreewise identification `Ψ i`. -/
public theorem isBaseChange_pieceSectionModuleHom [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]
    (i : ℤ) {W : s.base.Opens} {W' : s'.base.Opens}
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W)
    (hΨ : IsIso (Ψ i))
    [inst : Algebra ↥Γ(s.base, W) ↥Γ(s'.base, W')]
    (halg : ∀ r : ↥Γ(s.base, W),
      algebraMap ↥Γ(s.base, W) ↥Γ(s'.base, W') r = (g.appLE W W' h).hom r)
    [Module ↥Γ(s.base, W) ↥Γ(modPiece ℳ' i, W')]
    [IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W') ↥Γ(modPiece ℳ' i, W')]
    (rho : ↥Γ(modPiece ℳ i, W) →ₗ[↥Γ(s.base, W)] ↥Γ(modPiece ℳ' i, W'))
    (hrho : ∀ a, rho a = pieceSectionModuleHom g Ψ i W W' h a) :
    IsBaseChange ↥Γ(s'.base, W') rho := by
  let mP : Module ↥Γ(s.base, W)
      ↥Γ((Scheme.Modules.pullback g).obj (modPiece ℳ i), W') :=
    Module.compHom _ (algebraMap ↥Γ(s.base, W) ↥Γ(s'.base, W'))
  let tP : IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W')
      ↥Γ((Scheme.Modules.pullback g).obj (modPiece ℳ i), W') :=
    ⟨fun x y z => by
      rw [Algebra.smul_def x y]
      exact mul_smul (algebraMap ↥Γ(s.base, W) ↥Γ(s'.base, W') x) y z⟩
  have hrho0 : ∀ a, (modPieceLinearEquiv g Ψ i W' hΨ).symm (rho a) =
      Scheme.Modules.pullbackSection g (modPiece ℳ i) W W' h a := fun a =>
    (congrArg (modPieceLinearEquiv g Ψ i W' hΨ).symm (hrho a)).trans
      ((modPieceLinearEquiv g Ψ i W' hΨ).symm_apply_apply
        (Scheme.Modules.pullbackSection g (modPiece ℳ i) W W' h a))
  exact IsBaseChange.of_linearEquiv
    (isBaseChange_pullbackSection_of_isAffineOpen g (modPiece ℳ i) hW hW' h halg
      (((modPieceLinearEquiv g Ψ i W' hΨ).symm.restrictScalars ↥Γ(s.base, W)).toLinearMap.comp
        rho) hrho0)
    (LinearEquiv.refl _ _) (modPieceLinearEquiv g Ψ i W' hΨ).symm rho
    (fun _ => rfl)

variable (hΨ : ∀ (i : ℕ) (n : ℤ) (W : s.base.Opens) (W' : s'.base.Opens) (h : W' ≤ g ⁻¹ᵁ W)
  (a : s.sectionPieces W i) (x : sectionModulePieces ℳ W n),
  pieceSectionModuleHom g Ψ ((i : ℤ) + n) W W' h (ℳ.smul (i : ℤ) n (op W) a x)
    = ℳ'.smul (i : ℤ) n (op W') (pieceSectionHom g Φ i W W' h a)
        (pieceSectionModuleHom g Ψ n W W' h x))

/-- The `Γ(S', W')`-module structure on a homogeneous piece of the graded module of sections of
`ℳ'`, read as a target piece, by restriction of scalars along
`Stacks.RelativeProj.Situation.baseHom`. -/
@[reducible] public def targetPieceBaseModule (W' : s'.base.Opens) (i : ℤ) :
    Module ↥Γ(s'.base, W')
      (TargetPiece (s'.sectionRingGrading W') (sectionModuleGrading ℳ' W') i) :=
  Module.compHom _ (s'.baseHom W').hom

/-- **The degree-`i` summand of the graded module of sections of `ℳ'`, read as a target piece, is
the sections of `ℳ'ᵢ`**, `Γ(S', W')`-linearly. This is the inverse of
`Stacks.RelativeProj.Situation.modulePieceLinearEquiv`, on the type synonym. -/
public def targetPieceLinearEquiv (W' : s'.base.Opens) (i : ℤ) :
    letI := targetPieceBaseModule (ℳ' := ℳ') W' i
    TargetPiece (s'.sectionRingGrading W') (sectionModuleGrading ℳ' W') i
      ≃ₗ[↥Γ(s'.base, W')] ↥Γ(modPiece ℳ' i, W') :=
  letI := targetPieceBaseModule (ℳ' := ℳ') W' i
  { toFun := fun x => (modulePieceLinearEquiv ℳ' W' i).symm x.toPiece
    invFun := fun a => TargetPiece.ofPiece (modulePieceLinearEquiv ℳ' W' i a)
    map_add' := fun x y => (modulePieceLinearEquiv ℳ' W' i).symm.map_add x.toPiece y.toPiece
    map_smul' := fun r x => (modulePieceLinearEquiv ℳ' W' i).symm.map_smul r x.toPiece
    left_inv := fun x => (modulePieceLinearEquiv ℳ' W' i).apply_symm_apply x.toPiece
    right_inv := fun a => (modulePieceLinearEquiv ℳ' W' i).symm_apply_apply a }

include hΨ in
/-- **The degree-`i` component of the base change of graded modules of sections, read through the
identifications of the homogeneous summands**, is the degreewise base change of sections. -/
public theorem targetPieceLinearEquiv_modulePieceMap (i : ℤ) (W : s.base.Opens)
    (W' : s'.base.Opens) (h : W' ≤ g ⁻¹ᵁ W)
    [Algebra ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0)]
    (halgAB : ∀ r : ↥(s.sectionRingGrading W 0),
      ((algebraMap ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) r :
          s'.sectionRing W'))
        = gradedBaseChange g Φ W W' h (r : s.sectionRing W))
    (x : ↥(sectionModuleGrading ℳ W i)) :
    targetPieceLinearEquiv (ℳ' := ℳ') W' i
        (modulePieceMap (gradedBaseChange g Φ W W' h) (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W W' h)
          (fun i {_} hz => sectionModuleBaseChange_mem_grading g Ψ W W' h i hz) halgAB i x)
      = pieceSectionModuleHom g Ψ i W W' h ((modulePieceLinearEquiv ℳ W i).symm x) := by
  obtain ⟨a, ha⟩ : ∃ a, DirectSum.of (sectionModulePieces ℳ W) i a = (x : sectionModule ℳ W) :=
    x.2
  have hx : (modulePieceLinearEquiv ℳ W i).symm x = a :=
    (congrArg (fun z : sectionModule ℳ W => z i) ha).symm.trans
      (DirectSum.of_eq_same (β := sectionModulePieces ℳ W) i a)
  rw [hx]
  show (sectionModuleBaseChangeAddHom g Ψ W W' h (x : sectionModule ℳ W)) i = _
  rw [← ha, sectionModuleBaseChangeAddHom_of]
  exact DirectSum.of_eq_same (β := sectionModulePieces ℳ' W') i _

include hΨ in
/-- **The degreewise base change of the graded modules of sections, over the degree-zero rings.**
For affine opens `W ⊆ S` and `W' ⊆ g⁻¹W ⊆ S'`, extending the scalars of the degree-`i` piece of
`ℳ(W)` along `𝒜₀(W) ⟶ 𝒜'₀(W')` gives the degree-`i` piece of `ℳ'(W')`.

This is `Stacks.RelativeProj.Situation.isBaseChange_pieceSectionModuleHom`, which gives the same
statement over `Γ(S, W) ⟶ Γ(S', W')`, re-based along the degree-zero pushout
`Stacks.RelativeProj.Situation.isPushout_gradeZero_baseChange`. -/
public theorem isBaseChange_modulePieceMap_sectionModuleBaseChange
    [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] (hΨiso : ∀ n : ℤ, IsIso (Ψ n)) (i : ℤ)
    {W : s.base.Opens} {W' : s'.base.Opens}
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W)
    (hΦ : ∀ m : ℕ, IsIso (Φ.app (m : ℤ)))
    [instCD : Algebra ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0)]
    (halgCD : ∀ a : ↥(s.sectionRingGrading W 0),
      algebraMap ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) a
        = (gradedBaseChange g Φ W W' h).gradedZeroRingHom a)
    (halgAB : ∀ r : ↥(s.sectionRingGrading W 0),
      ((algebraMap ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) r :
          s'.sectionRing W'))
        = gradedBaseChange g Φ W W' h (r : s.sectionRing W)) :
    IsBaseChange ↥(s'.sectionRingGrading W' 0)
      (modulePieceMap (gradedBaseChange g Φ W W' h) (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W W' h)
        (fun i {_} hz => sectionModuleBaseChange_mem_grading g Ψ W W' h i hz) halgAB i) := by
  let aRS : Algebra ↥Γ(s.base, W) ↥Γ(s'.base, W') := (g.appLE W W' h).hom.toAlgebra
  have halgRS : ∀ r : ↥Γ(s.base, W),
      algebraMap ↥Γ(s.base, W) ↥Γ(s'.base, W') r = (g.appLE W W' h).hom r := fun _ => rfl
  let mRN' : Module ↥Γ(s.base, W) ↥Γ(modPiece ℳ' i, W') :=
    Module.compHom _ (g.appLE W W' h).hom
  let tRSN' : IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W') ↥Γ(modPiece ℳ' i, W') :=
    ⟨fun x y z => mul_smul ((g.appLE W W' h).hom x) y z⟩
  let rho : ↥Γ(modPiece ℳ i, W) →ₗ[↥Γ(s.base, W)] ↥Γ(modPiece ℳ' i, W') :=
    { toFun := fun a => pieceSectionModuleHom g Ψ i W W' h a
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => pieceSectionModuleHom_smul g Ψ i W W' h r a }
  have hrho : IsBaseChange ↥Γ(s'.base, W') rho :=
    isBaseChange_pieceSectionModuleHom g Ψ i hW hW' h (hΨiso i) halgRS rho (fun _ => rfl)
  let aRD : Algebra ↥Γ(s.base, W) ↥(s'.sectionRingGrading W' 0) :=
    (((gradedBaseChange g Φ W W' h).gradedZeroRingHom).comp (s.baseHom W).hom).toAlgebra
  let tRCD : IsScalarTower ↥Γ(s.base, W) ↥(s.sectionRingGrading W 0)
      ↥(s'.sectionRingGrading W' 0) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => (halgCD _).symm)
  let tRSD : IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W') ↥(s'.sectionRingGrading W' 0) :=
    IsScalarTower.of_algebraMap_eq'
      (CommRingCat.hom_ext_iff.1 (baseHom_gradedBaseChange g Φ W W' h)).symm
  have hpush : Algebra.IsPushout ↥Γ(s.base, W) ↥Γ(s'.base, W')
      ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) :=
    isPushout_gradeZero_baseChange g Φ W W' hW hW' h (hΦ 0) halgRS halgCD
  let mDN : Module ↥(s'.sectionRingGrading W' 0)
      (TargetPiece (s'.sectionRingGrading W') (sectionModuleGrading ℳ' W') i) :=
    inferInstance
  let mRN : Module ↥Γ(s.base, W)
      (TargetPiece (s'.sectionRingGrading W') (sectionModuleGrading ℳ' W') i) :=
    Module.compHom _ (algebraMap ↥Γ(s.base, W) ↥(s'.sectionRingGrading W' 0))
  let mSN : Module ↥Γ(s'.base, W')
      (TargetPiece (s'.sectionRingGrading W') (sectionModuleGrading ℳ' W') i) :=
    targetPieceBaseModule W' i
  let mCN : Module ↥(s.sectionRingGrading W 0)
      (TargetPiece (s'.sectionRingGrading W') (sectionModuleGrading ℳ' W') i) :=
    inferInstance
  let tRSN : IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W')
      (TargetPiece (s'.sectionRingGrading W') (sectionModuleGrading ℳ' W') i) :=
    isScalarTower_restrictScalars aRS aRD (s'.gradeZeroAlgebra W') tRSD
      mDN mRN mSN (fun _ _ => rfl) (fun _ _ => rfl)
  let tRCN : IsScalarTower ↥Γ(s.base, W) ↥(s.sectionRingGrading W 0)
      (TargetPiece (s'.sectionRingGrading W') (sectionModuleGrading ℳ' W') i) :=
    isScalarTower_restrictScalars (s.gradeZeroAlgebra W) aRD instCD tRCD
      mDN mRN mCN (fun _ _ => rfl) (fun _ _ => rfl)
  let tSDN : IsScalarTower ↥Γ(s'.base, W') ↥(s'.sectionRingGrading W' 0)
      (TargetPiece (s'.sectionRingGrading W') (sectionModuleGrading ℳ' W') i) :=
    ⟨fun x y z => mul_smul ((s'.baseHom W').hom x) y z⟩
  exact isBaseChange_modulePieceMap_of_isPushout
    (R := ↥Γ(s.base, W)) (S := ↥Γ(s'.base, W'))
    (A := s.sectionRing W) (B := s'.sectionRing W')
    (M := sectionModule ℳ W) (N := sectionModule ℳ' W')
    (𝒜 := s.sectionRingGrading W) (ℬ := s'.sectionRingGrading W')
    (𝒨 := sectionModuleGrading ℳ W) (𝒩 := sectionModuleGrading ℳ' W')
    (M₀ := ↥Γ(modPiece ℳ i, W)) (N₀ := ↥Γ(modPiece ℳ' i, W'))
    (aCD := instCD) (gradedBaseChange g Φ W W' h) (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W W' h)
    (fun i {_} hz => sectionModuleBaseChange_mem_grading g Ψ W W' h i hz) halgAB i
    aRS (s.gradeZeroAlgebra W) aRD (s'.gradeZeroAlgebra W') tRSD tRCD hpush
    (modulePieceBaseModule ℳ W i) (modulePieceBaseTower ℳ W i) mRN mSN
    tRSN tRCN tSDN inferInstance mRN' inferInstance tRSN' hrho
    (modulePieceLinearEquiv ℳ W i).symm (targetPieceLinearEquiv W' i)
    (targetPieceLinearEquiv_modulePieceMap g Φ Ψ hΨ i W W' h halgAB)

end BaseChange

end Situation

end Stacks.RelativeProj

end
