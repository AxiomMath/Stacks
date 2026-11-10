module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AffineModel
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel
public import StacksCore.Tactic.StacksAttribute

/-!
# Noetherian approximation of quasi-coherent modules on an affine morphism

Let `f : X ⟶ S` be a morphism of affine schemes of finite presentation and let `F` be a
quasi-coherent `O_X`-module of finite presentation. Then `f` admits an affine finite-type model
`f₀ : X₀ ⟶ S₀` over a base of finite type over `Spec ℤ` carrying a coherent module `F₀` whose
pullback to `X` is `F`; and if `F` is flat over `S`, the model can be chosen so that `F₀` is flat
over `S₀`.

Since a base of finite type over `ℤ` is Noetherian, this reduces statements about finitely
presented modules on finitely presented affine morphisms to the Noetherian case.

## Main results

* `AlgebraicGeometry.exists_finiteTypeAffineModel_isCoherent`: the module descends to a coherent
  module on an affine finite-type model.
* `AlgebraicGeometry.exists_finiteTypeAffineModel_isCoherent_isFlatOver`: a module flat over the
  base descends to a coherent module flat over the base of an affine finite-type model.

## Implementation notes

The approximation diagram is `AlgebraicGeometry.FiniteTypeAffineModel`. Both statements identify
the pullback of the descended module with the original one by an isomorphism of sheaves of
modules rather than by an equality.

Both proofs read the module through global sections. On an affine scheme `X` a quasi-coherent
module is recovered from its module of global sections by `tilde`, so a finitely presented
quasi-coherent `O_X`-module corresponds to a finitely presented `Γ(X, ⊤)`-module, and the
ring-theoretic descent of such a module to a subring of `Γ(S, ⊤)` of finite type over `ℤ` is
`Algebra.exists_subring_finiteType_int_isPushout_isBaseChange` in the first case and
`Module.Flat.exists_finiteType_model` in the second. Passing between `X` and `Spec Γ(X, ⊤)` is
done along `AlgebraicGeometry.Scheme.isoSpec`, and coherence of the descended module is read off
from its finite presentation over the Noetherian model through the equivalence of
[Stacks, Tag 01XZ].

## References

* [Stacks Project, Tag 05FC](https://stacks.math.columbia.edu/tag/05FC)
* [Stacks Project, Tag 05FD](https://stacks.math.columbia.edu/tag/05FD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace AlgebraicGeometry

/-- The pullback of a module of finite presentation along a morphism of schemes is of finite
presentation. This is [Stacks, Tag 01BQ] read on schemes rather than on ringed spaces. -/
private theorem isFinitePresentation_modulesPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Y.Modules) [F.IsFinitePresentation] :
    ((Scheme.Modules.pullback f).obj F).IsFinitePresentation :=
  @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ f.toLRSHom.toShHom F
    ‹F.IsFinitePresentation›

/-- The affine finite-type model of a morphism of affine schemes built from a pushout square of
global sections: the two vertical maps are the spectra of the two ring maps out of the subring
`R₀` of `Γ(S, ⊤)`, and the comparison maps are the spectra of the inclusions. -/
private noncomputable def finiteTypeAffineModelOfIsPushout
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    {R₀ B₀ : Type u} [CommRing R₀] [CommRing B₀] [Algebra R₀ B₀]
    [Algebra R₀ Γ(S, ⊤)] [Algebra B₀ Γ(X, ⊤)] [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    [Algebra R₀ Γ(X, ⊤)] [IsScalarTower R₀ Γ(S, ⊤) Γ(X, ⊤)] [IsScalarTower R₀ B₀ Γ(X, ⊤)]
    (hf : algebraMap Γ(S, ⊤) Γ(X, ⊤) = f.appTop.hom)
    (hp : Algebra.IsPushout R₀ Γ(S, ⊤) B₀ Γ(X, ⊤))
    (hR₀ : Algebra.FiniteType ℤ R₀) (hB₀ : Algebra.FiniteType R₀ B₀) :
    FiniteTypeAffineModel ⊤ f where
  X₀ := Spec (.of B₀)
  S₀ := Spec (.of R₀)
  f₀ := Spec.map (CommRingCat.ofHom (algebraMap R₀ B₀))
  toSource := X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B₀ Γ(X, ⊤)))
  toBase := S.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ Γ(S, ⊤)))
  isPullback := by
    have hp' : IsPushout (CommRingCat.ofHom (algebraMap R₀ B₀))
        (CommRingCat.ofHom (algebraMap R₀ Γ(S, ⊤)))
        (CommRingCat.ofHom (algebraMap B₀ Γ(X, ⊤))) f.appTop := by
      convert CommRingCat.isPushout_iff_isPushout.mpr hp.symm using 1
      ext
      exact congr($hf _).symm
    apply (isPullback_SpecMap_of_isPushout (CommRingCat.ofHom (algebraMap R₀ B₀))
      (CommRingCat.ofHom (algebraMap R₀ Γ(S, ⊤)))
      (CommRingCat.ofHom (algebraMap B₀ Γ(X, ⊤))) f.appTop hp').of_iso
      X.isoSpec.symm (Iso.refl _) S.isoSpec.symm (Iso.refl _)
    all_goals simp [Scheme.isoSpec_inv_naturality]
  source_affine := inferInstance
  base_affine := inferInstance
  base_locallyOfFiniteType := by
    have := hR₀
    exact finiteType_spec_terminal R₀
  base_quasiCompact := inferInstance
  locallyOfFiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr hB₀)
  quasiCompact := inferInstance
  property := trivial

/-- A finitely presented quasi-coherent module on an affine scheme is `M~` for a finitely
presented module `M` of global sections, and the identification is the inverse of the canonical
comparison map. -/
private theorem finitePresentation_moduleSpecΓ {B : Type u} [CommRing B]
    (G : (Spec (.of B)).Modules) [G.IsQuasicoherent] [G.IsFinitePresentation] :
    Module.FinitePresentation B ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj G) := by
  have hiso : tilde ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj G) ≅ G :=
    @asIso _ _ _ _ G.fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G)
  have h : (tilde ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj G)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec (.of B)).ringCatSheaf).prop_of_iso
      hiso.symm inferInstance
  exact (tilde_isFinitePresentation_iff _).mp h

/-- Transporting a quasi-coherent module of finite presentation from an affine scheme to the
spectrum of its ring of global sections keeps both properties. -/
private theorem isFinitePresentation_pullback_isoSpec_inv {X : Scheme.{u}} [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    ((Scheme.Modules.pullback X.isoSpec.inv).obj F).IsQuasicoherent ∧
      ((Scheme.Modules.pullback X.isoSpec.inv).obj F).IsFinitePresentation :=
  ⟨(SheafOfModules.isQuasicoherent (Spec (.of Γ(X, ⊤))).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.inv).app F) inferInstance,
    isFinitePresentation_modulesPullback X.isoSpec.inv F⟩

/-- Pullback along `X.isoSpec.hom` undoes pullback along `X.isoSpec.inv`. -/
private noncomputable def pullbackIsoSpecHomInvIso {X : Scheme.{u}} [IsAffine X]
    (F : X.Modules) :
    (Scheme.Modules.pullback X.isoSpec.hom).obj
      ((Scheme.Modules.pullback X.isoSpec.inv).obj F) ≅ F :=
  (Scheme.Modules.pullbackComp X.isoSpec.hom X.isoSpec.inv).app F ≪≫
    (Scheme.Modules.pullbackCongr
      (by simp : X.isoSpec.hom ≫ X.isoSpec.inv = 𝟙 X)).app F ≪≫
    (Scheme.Modules.pullbackId X).app F

/-- The extension of scalars of a module along `B₀ → B` computes the base change: the canonical
`B`-linear comparison from `B ⊗[B₀] M₀`, read as an object of `ModuleCat B`, to a module `M`
exhibited as a base change of `M₀`. -/
private noncomputable def extendScalarsIsoOfIsBaseChange
    {B₀ B : Type u} [CommRing B₀] [CommRing B] [Algebra B₀ B]
    {M₀ : Type u} [AddCommGroup M₀] [Module B₀ M₀]
    {M : Type u} [AddCommGroup M] [Module B M] [Module B₀ M] [IsScalarTower B₀ B M]
    {φ : M₀ →ₗ[B₀] M} (hφ : IsBaseChange B φ) :
    (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap B₀ B)).hom).obj
        (ModuleCat.of (CommRingCat.of B₀) M₀) ≅
      ModuleCat.of (CommRingCat.of B) M := by
  let ψ := algebraMap B₀ B
  let : IsScalarTower B₀ B ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of B B) : Type u) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let eTensor : ((ModuleCat.extendScalars ψ).obj (ModuleCat.of B₀ M₀) : Type u) ≃ₗ[B]
      TensorProduct B₀ B M₀ :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) (LinearEquiv.refl B₀ M₀)
  exact eTensor.toModuleIso ≪≫ hφ.equiv.toModuleIso

/-- The module of global sections of the transport of `F` to `Spec Γ(X, ⊤)` is `Γ(F, ⊤)`: the
transport is the restriction of `F` along `(isAffineOpen_top X).fromSpec`, whose global sections
are the sections of `F` over `⊤` by `AlgebraicGeometry.affineSectionsLinearEquiv`. -/
private noncomputable def moduleSpecΓPullbackLinearEquiv {X : Scheme.{u}} [IsAffine X]
    (F : X.Modules) :
    (moduleSpecΓFunctor (R := CommRingCat.of Γ(X, ⊤))).obj
        ((Scheme.Modules.pullback X.isoSpec.inv).obj F) ≃ₗ[Γ(X, ⊤)] Γ(F, ⊤) :=
  let e : (Scheme.Modules.pullback X.isoSpec.inv).obj F ≅
      F.restrict (isAffineOpen_top X).fromSpec :=
    ((Scheme.Modules.pullbackCongr (IsAffineOpen.fromSpec_top (X := X))).app F).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback
        (isAffineOpen_top X).fromSpec).app F).symm
  (((moduleSpecΓFunctor (R := CommRingCat.of Γ(X, ⊤))).mapIso e).toLinearEquiv).trans
    (affineSectionsLinearEquiv F (isAffineOpen_top X))

/-- The tilde of a finite module over a Noetherian ring is a coherent module on its spectrum. -/
private theorem isCoherent_tilde_of_finite (B₀ : Type u) [CommRing B₀] [IsNoetherianRing B₀]
    (M₀ : Type u) [AddCommGroup M₀] [Module B₀ M₀] [Module.Finite B₀ M₀] :
    (tilde (ModuleCat.of (CommRingCat.of B₀) M₀) : (Spec (.of B₀)).Modules).IsCoherent := by
  have : IsLocallyNoetherian (Spec (.of B₀)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : (tilde (ModuleCat.of (CommRingCat.of B₀) M₀) : (Spec (.of B₀)).Modules)
      |>.IsFinitePresentation :=
    (tilde_isFinitePresentation_iff (ModuleCat.of (CommRingCat.of B₀) M₀)).mpr
      (Module.finitePresentation_of_finite B₀ M₀)
  exact ((Stacks.AlgebraicGeometry.CoherentKernel.coherent_tfae _ _).out 3 1).mp this

/-- If the module of global sections of the transport of `F` to `Spec Γ(X, ⊤)` is a base change of
`M₀` along `B₀ → Γ(X, ⊤)`, then `F` is the pullback of `M₀~` along the induced map
`X ⟶ Spec B₀`. -/
private noncomputable def pullbackTildeIsoOfIsBaseChange {X : Scheme.{u}} [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    {B₀ : Type u} [CommRing B₀] [Algebra B₀ Γ(X, ⊤)]
    {M₀ : Type u} [AddCommGroup M₀] [Module B₀ M₀]
    [Module B₀ ((moduleSpecΓFunctor (R := CommRingCat.of Γ(X, ⊤))).obj
      ((Scheme.Modules.pullback X.isoSpec.inv).obj F))]
    [IsScalarTower B₀ Γ(X, ⊤) ((moduleSpecΓFunctor (R := CommRingCat.of Γ(X, ⊤))).obj
      ((Scheme.Modules.pullback X.isoSpec.inv).obj F))]
    {φ : M₀ →ₗ[B₀] (moduleSpecΓFunctor (R := CommRingCat.of Γ(X, ⊤))).obj
      ((Scheme.Modules.pullback X.isoSpec.inv).obj F)}
    (hφ : IsBaseChange Γ(X, ⊤) φ) :
    (Scheme.Modules.pullback (X.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap B₀ Γ(X, ⊤))))).obj
        (tilde (ModuleCat.of (CommRingCat.of B₀) M₀)) ≅ F :=
  have := (isFinitePresentation_pullback_isoSpec_inv F).1
  let eSpec : (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap B₀ Γ(X, ⊤))))).obj
        (tilde (ModuleCat.of (CommRingCat.of B₀) M₀)) ≅
      (Scheme.Modules.pullback X.isoSpec.inv).obj F :=
    (pullbackTildeIso (.of B₀) (.of Γ(X, ⊤)) (CommRingCat.ofHom (algebraMap B₀ Γ(X, ⊤)))).app
        (ModuleCat.of (CommRingCat.of B₀) M₀) ≪≫
      (tilde.functor (R := .of Γ(X, ⊤))).mapIso (extendScalarsIsoOfIsBaseChange hφ) ≪≫
      @asIso _ _ _ _ ((Scheme.Modules.pullback X.isoSpec.inv).obj F).fromTildeΓ
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _)
  ((Scheme.Modules.pullbackComp X.isoSpec.hom
      (Spec.map (CommRingCat.ofHom (algebraMap B₀ Γ(X, ⊤))))).app _).symm ≪≫
    (Scheme.Modules.pullback X.isoSpec.hom).mapIso eSpec ≪≫ pullbackIsoSpecHomInvIso F

/-- **Stacks Project, Tag 05FC.** A quasi-coherent module of finite presentation on the source of
a morphism of affine schemes of finite presentation descends to a coherent module on an affine
finite-type model of that morphism over a base of finite type over `ℤ`. -/
@[stacks 05FC]
theorem exists_finiteTypeAffineModel_isCoherent
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) (hf : FinitePresentation f)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    ∃ (m : FiniteTypeAffineModel ⊤ f) (F₀ : m.X₀.Modules),
      F₀.IsCoherent ∧ Nonempty ((Scheme.Modules.pullback m.toSource).obj F₀ ≅ F) := by
  classical
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  let A := Γ(S, ⊤)
  let B := Γ(X, ⊤)
  let : Algebra A B := f.appTop.hom.toAlgebra
  have : Algebra.FinitePresentation A B := f.finitePresentation_appTop
  let G := (Scheme.Modules.pullback X.isoSpec.inv).obj F
  obtain ⟨_, _⟩ : G.IsQuasicoherent ∧ G.IsFinitePresentation :=
    isFinitePresentation_pullback_isoSpec_inv F
  let M := (moduleSpecΓFunctor (R := CommRingCat.of B)).obj G
  have : Module.FinitePresentation B M := finitePresentation_moduleSpecΓ G
  obtain ⟨R₀, B₀, M₀, _, _, _, _, _, _, _, _, φ, hR₀, hB₀, _, hpush, hbase⟩ :=
    Algebra.exists_subring_finiteType_int_isPushout_isBaseChange (R := A) (S := B) M
  have : Algebra.FiniteType ℤ B₀ := Algebra.FiniteType.trans hR₀ hB₀
  have : IsNoetherianRing B₀ := Algebra.FiniteType.isNoetherianRing ℤ B₀
  exact ⟨finiteTypeAffineModelOfIsPushout f rfl hpush hR₀ hB₀, _,
    isCoherent_tilde_of_finite B₀ M₀, ⟨pullbackTildeIsoOfIsBaseChange F hbase⟩⟩

/-- On an affine scheme the restriction to global sections over `⊤` of
`AlgebraicGeometry.Scheme.Hom.appLE` is `AlgebraicGeometry.Scheme.Hom.appTop`. -/
private theorem appLE_top_top {X S : Scheme.{u}} (f : X ⟶ S)
    (htop : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens)) :
    f.appLE ⊤ ⊤ htop = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  congr 1

/-- **Stacks Project, Tag 05FD.** A quasi-coherent module of finite presentation on the source of
a morphism of affine schemes of finite presentation which is moreover flat over the target
descends to a coherent module, flat over the base, on an affine finite-type model of that
morphism over a base of finite type over `ℤ`. -/
@[stacks 05FD]
theorem exists_finiteTypeAffineModel_isCoherent_isFlatOver
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) (hf : FinitePresentation f)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hF : IsFlatOver f.toLRSHom.toShHom F) :
    ∃ (m : FiniteTypeAffineModel ⊤ f) (F₀ : m.X₀.Modules),
      F₀.IsCoherent ∧ Nonempty ((Scheme.Modules.pullback m.toSource).obj F₀ ≅ F) ∧
        IsFlatOver m.f₀.toLRSHom.toShHom F₀ := by
  classical
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  let A := Γ(S, ⊤)
  let B := Γ(X, ⊤)
  let : Algebra A B := f.appTop.hom.toAlgebra
  have : Algebra.FinitePresentation A B := f.finitePresentation_appTop
  let G := (Scheme.Modules.pullback X.isoSpec.inv).obj F
  obtain ⟨_, _⟩ : G.IsQuasicoherent ∧ G.IsFinitePresentation :=
    isFinitePresentation_pullback_isoSpec_inv F
  let M := (moduleSpecΓFunctor (R := CommRingCat.of B)).obj G
  have : Module.FinitePresentation B M := finitePresentation_moduleSpecΓ G
  let : Module A (M : Type u) := Module.compHom (M : Type u) (algebraMap A B)
  have : IsScalarTower A B (M : Type u) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have htop : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens) := by simp
  let : Module A Γ(F, ⊤) := Module.compHom _ (f.appLE ⊤ ⊤ htop).hom
  have : IsScalarTower A B Γ(F, ⊤) := IsScalarTower.of_algebraMap_smul fun r x => by
    change (f.appTop.hom r) • x = (f.appLE ⊤ ⊤ htop).hom r • x
    rw [appLE_top_top f htop]
  have hflat : Module.Flat A Γ(F, ⊤) := by
    have h := ((isFlatOver_tfae f F).out 1 2).mp hF
    exact h ⊤ (isAffineOpen_top X) ⊤ (isAffineOpen_top S) htop
  have : Module.Flat A (M : Type u) :=
    (Module.Flat.equiv_iff ((moduleSpecΓPullbackLinearEquiv F).restrictScalars A)).mpr hflat
  obtain ⟨R₀, T₀, M₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, q,
      hR₀, hT₀, hM₀, hM₀flat, hpush, hbase⟩ :=
    Module.Flat.exists_finiteType_model (R := (A : Type u)) (S := (B : Type u)) (M : Type u)
  let X₀ : Scheme.{u} := Spec (.of T₀)
  let S₀ : Scheme.{u} := Spec (.of R₀)
  let f₀ : X₀ ⟶ S₀ := Spec.map (CommRingCat.ofHom (algebraMap R₀ T₀))
  let m : FiniteTypeAffineModel ⊤ f :=
    finiteTypeAffineModelOfIsPushout f rfl hpush hR₀ hT₀
  have : Algebra.FiniteType ℤ T₀ := Algebra.FiniteType.trans hR₀ hT₀
  have : IsNoetherianRing T₀ := Algebra.FiniteType.isNoetherianRing ℤ T₀
  let F₀ : X₀.Modules := tilde (ModuleCat.of (CommRingCat.of T₀) M₀)
  have hF₀coh : F₀.IsCoherent := isCoherent_tilde_of_finite T₀ M₀
  let γR := Scheme.ΓSpecIso (CommRingCat.of R₀)
  let γT := Scheme.ΓSpecIso (CommRingCat.of T₀)
  let g : CommRingCat.of Γ(S₀, ⊤) ⟶ CommRingCat.of T₀ :=
    γR.hom ≫ CommRingCat.ofHom (algebraMap R₀ T₀)
  let : Algebra (Γ(S₀, ⊤) : Type u) R₀ := γR.hom.hom.toAlgebra
  let : Algebra (Γ(S₀, ⊤) : Type u) T₀ := g.hom.toAlgebra
  let : Module (Γ(S₀, ⊤) : Type u) M₀ := Module.compHom M₀ g.hom
  have : IsScalarTower (Γ(S₀, ⊤) : Type u) T₀ M₀ :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower (Γ(S₀, ⊤) : Type u) R₀ M₀ :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change (γR.hom.hom r) • x = (g.hom r) • x
      exact (IsScalarTower.algebraMap_smul (R := R₀) (A := T₀) (M := M₀)
        (r := γR.hom.hom r) (x := x)).symm
  have : Module.Flat (Γ(S₀, ⊤) : Type u) R₀ :=
    RingHom.flat_algebraMap_iff.mp
      (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso γR.hom))
  have : Module.Flat R₀ M₀ := hM₀flat
  have hM₀Γ : Module.Flat (Γ(S₀, ⊤) : Type u) M₀ :=
    Module.Flat.trans (Γ(S₀, ⊤) : Type u) R₀ M₀
  have htop₀ : (⊤ : X₀.Opens) ≤ f₀ ⁻¹ᵁ (⊤ : S₀.Opens) := by simp
  let : Module T₀ Γ(F₀, ⊤) := Module.compHom _ γT.inv.hom
  let : Module (Γ(S₀, ⊤) : Type u) Γ(F₀, ⊤) := Module.compHom _ (f₀.appLE ⊤ ⊤ htop₀).hom
  have hgT : g ≫ γT.inv = f₀.appLE ⊤ ⊤ htop₀ := by
    rw [appLE_top_top f₀ htop₀]
    dsimp only [g]
    rw [Category.assoc, Scheme.ΓSpecIso_inv_naturality]
    simp [γR, f₀]
  have : IsScalarTower (Γ(S₀, ⊤) : Type u) T₀ Γ(F₀, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change (γT.inv.hom (g.hom r)) • x = (f₀.appLE ⊤ ⊤ htop₀).hom r • x
      exact congrArg (fun k : Γ(S₀, ⊤) →+* Γ(X₀, ⊤) => k r • x)
        (congrArg CommRingCat.Hom.hom hgT)
  have hsections : Module.Flat (Γ(S₀, ⊤) : Type u) Γ(F₀, ⊤) := by
    have e₀ : M₀ ≃ₗ[T₀] Γ(F₀, ⊤) :=
      ((tilde.toTildeΓNatIso (R := CommRingCat.of T₀)).app
        (ModuleCat.of (CommRingCat.of T₀) M₀)).toLinearEquiv
    exact (Module.Flat.equiv_iff (e₀.restrictScalars (Γ(S₀, ⊤) : Type u))).mp hM₀Γ
  have hflat₀ : IsFlatOver f₀.toLRSHom.toShHom F₀ := by
    have hiff := (isFlatOver_tfae f₀ F₀).out 4 1
    apply hiff.mp
    refine ⟨ULift.{u} Unit, fun _ => ⊤, by simp [TopologicalSpace.IsOpenCover],
      fun _ => isAffineOpen_top S₀, fun _ => ?_⟩
    exact ⟨ULift.{u} Unit, fun _ => ⊤, by simp, fun _ => isAffineOpen_top X₀,
      fun _ => by simpa using hsections⟩
  exact ⟨m, F₀, hF₀coh, ⟨pullbackTildeIsoOfIsBaseChange F hbase⟩, hflat₀⟩

end AlgebraicGeometry
