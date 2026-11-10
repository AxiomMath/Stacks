module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderIdealAffine
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysFirstOrderAffineBaseChange

/-!
# The base change of sections along `q₀ : T'' ⟶ T` on `Cris(X/S)`, over an affine object

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `ℱ` be a sheaf
of `𝒪_{X/S}`-modules on the **small** crystalline site `Cris(X/S)` and let `(U, T, δ)` be an
object of `Cris(X/S)` with second-order universal thickening `(U, T'', δ'')` of
[Stacks, Remark 60.14.5, Tag 07J3] and first projection `q₀ : T'' ⟶ T`.  Write `D = Γ(T, 𝒪_T)`,
`D'' = Γ(T'', 𝒪_{T''})` and `Mod = ℱ(U, T, δ)`.

This module proves that the base change of sections along `q₀`,

`...SmallSite.crysSecondExtensionSectionsMap : D'' ⊗_D Mod ⟶ ℱ(U, T'', δ'')`,
`t ⊗ s ↦ t · q₀^* s`,

is **bijective** for `ℱ` a crystal with `ℱ_T` quasi-coherent on an object whose ambient scheme is
affine.  It is the degree-two analogue of `...SmallSite.bijective_crysExtensionSectionsMap`, and
the small-site twin of
`Crystalline.GlobalCrystallineSituation.SecondOrderAffine.bijective_extensionSectionsMap`.

The affine chain is the composite

`D'' ⊗_D Γ(T, ℱ_T) ≅ Γ(T'', q₀^* ℱ_T) ≅ Γ(T'', ℱ_{T''})`,

the first isomorphism `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` at `U = V = ⊤`, the
second the crystal condition of `ℱ` at the morphism `q₀` of `Cris(X/S)`, which is
`...SmallSite.crysAffineChainTailAlong`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crysSecondExtensionSectionsMap` — the base change `D'' ⊗_D Mod ⟶ ℱ(U, T'', δ'')`.
* `crysSecondAffineExtensionHom` — the affine chain.

## Main results

* `crysSecondExtensionSectionsMap_eq_crysSecondAffineExtensionHom` — the chain is the base change.
* `bijective_crysSecondExtensionSectionsMap` — **the base change is bijective** for a crystal on
  an object with affine ambient scheme and quasi-coherent `ℱ_T`.
* `bijective_crysSecondExtensionSectionsMap_of_isQuasicoherentOnSite` — the same for a crystal in
  quasi-coherent modules.

## References

* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry TensorProduct ChangeOfRings

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))
  (B : CrystallineThickening S)

/-! ### The base change of the sections along `q₀` -/

/-- The sections of a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` over the second-order universal
thickening of an object, as a module over the section ring of that thickening written in the
big-site spelling `Crystalline.GlobalCrystallineSituation.crysSheafRing`. -/
instance moduleCrysSheafRingSecondOrderSections :
    Module (crysSheafRing S (secondOrderThickeningObject S B.obj))
      (F.val.obj (op (secondOrderThickeningCrysObject S B))) :=
  inferInstanceAs (Module ((structureSheaf S).obj.obj (op (secondOrderThickeningCrysObject S B)))
    (F.val.obj (op (secondOrderThickeningCrysObject S B))))

/-- **The restriction of sections along the first projection `q₀ : T'' ⟶ T` of
[Stacks, Tag 07J3]**, for a sheaf of modules on the small crystalline site. -/
abbrev crysSectionsQ₀ : F.val.obj (op B) → F.val.obj (op (secondOrderThickeningCrysObject S B)) :=
  F.val.map (secondOrderThickeningCrysQ₀ S B).op

/-- Restriction along `q₀` is additive. -/
theorem crysSectionsQ₀_add (s s' : F.val.obj (op B)) :
    crysSectionsQ₀ F B (s + s') = crysSectionsQ₀ F B s + crysSectionsQ₀ F B s' :=
  map_add _ s s'

/-- Restriction along `q₀` is semilinear for the restriction of the section rings along `q₀`. -/
theorem crysSectionsQ₀_smul (b : crysSheafRing S B.obj) (s : F.val.obj (op B)) :
    crysSectionsQ₀ F B (b • s) =
      crysSheafRingMap (secondOrderThickeningSiteQ₀ S B.obj) b • crysSectionsQ₀ F B s :=
  F.val.map_smul (secondOrderThickeningCrysQ₀ S B).op b s

/-- The bilinear datum of `...SmallSite.crysSecondExtensionSectionsMap`. -/
def crysSecondExtensionSectionsAux :
    crysSheafRing S (secondOrderThickeningObject S B.obj) →+
      (F.val.obj (op B) →+ F.val.obj (op (secondOrderThickeningCrysObject S B))) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk' (fun s ↦ t • crysSectionsQ₀ F B s)
      fun s s' ↦ by rw [crysSectionsQ₀_add, smul_add])
    fun t t' ↦ by
      refine AddMonoidHom.ext fun s ↦ ?_
      change (t + t') • crysSectionsQ₀ F B s = t • crysSectionsQ₀ F B s + t' • crysSectionsQ₀ F B s
      rw [add_smul]

/-- **The base change of the sections of a sheaf of modules on `Cris(X/S)` along `q₀`**, the map

`Γ(T'', 𝒪_{T''}) ⊗_{Γ(T, 𝒪_T)} Γ(T, ℱ) ⟶ Γ(T'', ℱ)`,  `t ⊗ s ↦ t · q₀^* s`,

the small-site twin of
`Crystalline.GlobalCrystallineSituation.SecondOrderAffine.extensionSectionsMap` and the degree-two
analogue of `...SmallSite.crysExtensionSectionsMap`. -/
def crysSecondExtensionSectionsMap :
    crysSheafRing S (secondOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) →+
      F.val.obj (op (secondOrderThickeningCrysObject S B)) :=
  TensorProduct.liftAddHom (crysSecondExtensionSectionsAux F B) fun b t s ↦ by
    change (b • t) • crysSectionsQ₀ F B s = t • crysSectionsQ₀ F B (b • s)
    rw [crysSectionsQ₀_smul, SecondOrderAffine.crysSheafRing_smul_def, smul_smul,
      crysSheafRing_mul_comm]

/-- `crysSecondExtensionSectionsMap` sends a pure tensor `t ⊗ s` to `t · q₀^* s`. -/
@[simp] theorem crysSecondExtensionSectionsMap_tmul
    (t : crysSheafRing S (secondOrderThickeningObject S B.obj)) (s : F.val.obj (op B)) :
    crysSecondExtensionSectionsMap F B (t ⊗ₜ[crysSheafRing S B.obj] s) =
      t • crysSectionsQ₀ F B s :=
  rfl

/-! ### The change of spelling of the two tensor products -/

/-- The bilinear datum of `...SmallSite.crysSecondAffineCross`. -/
def crysSecondAffineCrossAux :
    crysSheafRing S (secondOrderThickeningObject S B.obj) →+
      (F.val.obj (op B) →+
        Γ((secondOrderThickeningObject S B.obj).thickening.target.scheme, ⊤) ⊗[
          Γ(B.obj.thickening.target.scheme, ⊤)] Γ(crysAmbientSchemeModules F B, ⊤)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun s ↦ ambientRingSection (secondOrderThickeningObject S B.obj) t ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, ⊤)]
        crysAmbientModuleSection F B (crysSiteRestrict F (B.restrictOpenHom ⊤) s))
      (fun s s' ↦ (congrArg
          (fun y ↦ ambientRingSection (secondOrderThickeningObject S B.obj) t ⊗ₜ[
            Γ(B.obj.thickening.target.scheme, ⊤)] crysAmbientModuleSection F B y)
          (crysSiteRestrict_add F (B.restrictOpenHom ⊤) s s')).trans
        (TensorProduct.tmul_add _ _ _)))
    (fun _ _ ↦ AddMonoidHom.ext fun _ ↦ TensorProduct.add_tmul _ _ _)

/-- The bilinear datum of `crysSecondAffineCross`, on a pair. -/
@[simp]
theorem crysSecondAffineCrossAux_apply (t : crysSheafRing S (secondOrderThickeningObject S B.obj))
    (s : F.val.obj (op B)) :
    crysSecondAffineCrossAux F B t s =
      ambientRingSection (secondOrderThickeningObject S B.obj) t ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, ⊤)]
        crysAmbientModuleSection F B (crysSiteRestrict F (B.restrictOpenHom ⊤) s) := rfl

/-- **The base change of the sections of `ℱ` along `q₀`, carried into the tensor product of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`**: the map
`D'' ⊗_D Mod ⟶ Γ(T'', 𝒪_{T''}) ⊗_{Γ(T, 𝒪_T)} Γ(T, ℱ_T)` sending `t ⊗ s` to `t ⊗ q₀^* s`. -/
def crysSecondAffineCross :
    crysSheafRing S (secondOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) →+
      Γ((secondOrderThickeningObject S B.obj).thickening.target.scheme, ⊤) ⊗[
        Γ(B.obj.thickening.target.scheme, ⊤)] Γ(crysAmbientSchemeModules F B, ⊤) :=
  TensorProduct.liftAddHom (crysSecondAffineCrossAux F B) (fun b t s ↦ by
    rw [crysSecondAffineCrossAux_apply, crysSecondAffineCrossAux_apply,
      ← SecondOrderAffine.ambientRingSection_smul,
      TensorProduct.smul_tmul, crysAmbientModuleSection_smul, crysSiteRestrict_smul])

/-- `crysSecondAffineCross` on a pure tensor. -/
@[simp]
theorem crysSecondAffineCross_tmul (t : crysSheafRing S (secondOrderThickeningObject S B.obj))
    (s : F.val.obj (op B)) :
    crysSecondAffineCross F B (t ⊗ₜ[crysSheafRing S B.obj] s) =
      ambientRingSection (secondOrderThickeningObject S B.obj) t ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, ⊤)]
        crysAmbientModuleSection F B (crysSiteRestrict F (B.restrictOpenHom ⊤) s) :=
  TensorProduct.liftAddHom_tmul _ _ t s

/-- The bilinear datum of `...SmallSite.crysSecondAffineCrossInv`. -/
def crysSecondAffineCrossInvAux :
    Γ((secondOrderThickeningObject S B.obj).thickening.target.scheme, ⊤) →+
      (Γ(crysAmbientSchemeModules F B, ⊤) →+
        crysSheafRing S (secondOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
          F.val.obj (op B)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun x ↦ siteRingSection (secondOrderThickeningObject S B.obj) t ⊗ₜ[crysSheafRing S B.obj]
        (crysRestrictOpenTopEquiv F B).symm (crysSiteModuleSection F B x))
      (fun x y ↦ (congrArg
          (fun z ↦ siteRingSection (secondOrderThickeningObject S B.obj) t ⊗ₜ[
            crysSheafRing S B.obj] z)
          (map_add (crysRestrictOpenTopEquiv F B).symm (crysSiteModuleSection F B x)
            (crysSiteModuleSection F B y))).trans
        (TensorProduct.tmul_add _ _ _)))
    (fun _ _ ↦ AddMonoidHom.ext fun _ ↦ TensorProduct.add_tmul _ _ _)

/-- The bilinear datum of `crysSecondAffineCrossInv`, on a pair. -/
@[simp]
theorem crysSecondAffineCrossInvAux_apply
    (t : Γ((secondOrderThickeningObject S B.obj).thickening.target.scheme, ⊤))
    (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    crysSecondAffineCrossInvAux F B t x =
      siteRingSection (secondOrderThickeningObject S B.obj) t ⊗ₜ[crysSheafRing S B.obj]
        (crysRestrictOpenTopEquiv F B).symm (crysSiteModuleSection F B x) := rfl

/-- **The inverse of `...SmallSite.crysSecondAffineCross`**, the map
`Γ(T'', 𝒪_{T''}) ⊗_{Γ(T, 𝒪_T)} Γ(T, ℱ_T) ⟶ D'' ⊗_D Mod` sending `t ⊗ x` to `t ⊗ (q₀^*)⁻¹ x`. -/
def crysSecondAffineCrossInv :
    Γ((secondOrderThickeningObject S B.obj).thickening.target.scheme, ⊤) ⊗[
        Γ(B.obj.thickening.target.scheme, ⊤)] Γ(crysAmbientSchemeModules F B, ⊤) →+
      crysSheafRing S (secondOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) :=
  TensorProduct.liftAddHom (crysSecondAffineCrossInvAux F B) (fun r t x ↦ by
    rw [crysSecondAffineCrossInvAux_apply, crysSecondAffineCrossInvAux_apply,
      SecondOrderAffine.smul_eq_ambientRingSection,
      siteRingSection_ambientRingSection, TensorProduct.smul_tmul,
      crysRestrictOpenTopEquiv_symm_smul])

/-- `crysSecondAffineCrossInv` on a pure tensor. -/
@[simp]
theorem crysSecondAffineCrossInv_tmul
    (t : Γ((secondOrderThickeningObject S B.obj).thickening.target.scheme, ⊤))
    (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    crysSecondAffineCrossInv F B (t ⊗ₜ[Γ(B.obj.thickening.target.scheme, ⊤)] x) =
      siteRingSection (secondOrderThickeningObject S B.obj) t ⊗ₜ[crysSheafRing S B.obj]
        (crysRestrictOpenTopEquiv F B).symm (crysSiteModuleSection F B x) :=
  TensorProduct.liftAddHom_tmul _ _ t x

/-- **The two tensor products of the affine computation of the base change agree**, as an additive
equivalence

`D'' ⊗_D Mod ≅ Γ(T'', 𝒪_{T''}) ⊗_{Γ(T, 𝒪_T)} Γ(T, ℱ_T)`. -/
def crysSecondAffineCrossEquiv :
    crysSheafRing S (secondOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) ≃+
      Γ((secondOrderThickeningObject S B.obj).thickening.target.scheme, ⊤) ⊗[
        Γ(B.obj.thickening.target.scheme, ⊤)] Γ(crysAmbientSchemeModules F B, ⊤) where
  toFun := crysSecondAffineCross F B
  invFun := crysSecondAffineCrossInv F B
  map_add' := map_add (crysSecondAffineCross F B)
  left_inv z := by
    induction z using TensorProduct.inductionOn with
    | tmul t s =>
        rw [crysSecondAffineCross_tmul, crysSecondAffineCrossInv_tmul,
          siteRingSection_ambientRingSection,
          crysSiteModuleSection_crysAmbientModuleSection, ← crysRestrictOpenTopEquiv_apply,
          AddEquiv.symm_apply_apply]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  right_inv w := by
    induction w using TensorProduct.inductionOn with
    | tmul t x =>
        rw [crysSecondAffineCrossInv_tmul, crysSecondAffineCross_tmul,
          crysSiteRestrict_crysRestrictOpenTopEquiv_symm]
        rfl
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-! ### The base change of scalars in the form the tail of the chain produces -/

/-- The base change of scalars on a pure tensor `t ⊗ s`, written through the restriction of
sections along `crysRestrictOpenMapTop q₀`. -/
theorem crysSecondExtensionSectionsMap_tmul_crysRestrictOpenMapTop
    (t : crysSheafRing S (secondOrderThickeningObject S B.obj)) (s : F.val.obj (op B)) :
    crysSecondExtensionSectionsMap F B (t ⊗ₜ[crysSheafRing S B.obj] s) =
      t • (crysRestrictOpenTopEquiv F (secondOrderThickeningCrysObject S B)).symm
        (crysSiteRestrict F (crysRestrictOpenMapTop (secondOrderThickeningCrysQ₀ S B))
          (crysSiteModuleSection F B
            (crysAmbientModuleSection F B
              (crysSiteRestrict F (B.restrictOpenHom ⊤) s)))) := by
  rw [crysSecondExtensionSectionsMap_tmul, crysSiteModuleSection_crysAmbientModuleSection]
  refine congrArg (fun y ↦ t • y) (Eq.symm ?_)
  rw [AddEquiv.symm_apply_eq, crysRestrictOpenTopEquiv_apply]
  exact crysSiteRestrict_crysRestrictOpenMapTop F (secondOrderThickeningCrysQ₀ S B) s

/-! ### The chain on an affine object -/

section Affine

variable [IsAffine B.obj.thickening.target.scheme]
  [(crysAmbientSchemeModules F B).IsQuasicoherent]

/-- The affine base-change comparison of [Stacks, Tag 01I9] at the whole of the two ambient
schemes, which are affine. -/
abbrev crysSecondAffineBaseChangeTopIso :=
  affinePullbackSectionsBaseChangeIso (secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom
    (crysAmbientSchemeModules F B) (isAffineOpen_top _) (isAffineOpen_top _)
    (SecondOrderAffine.top_le_preimage_siteQ₀ B.obj)

/-- `crysSecondAffineCross`, with its target named at the extension of scalars of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`. -/
def crysSecondAffineCrossModule :
    crysSheafRing S (secondOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) →+
      ((ModuleCat.extendScalars ((secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
          (SecondOrderAffine.top_le_preimage_siteQ₀ B.obj)).hom).obj
        (ModuleCat.of Γ(B.obj.thickening.target.scheme, ⊤) Γ(crysAmbientSchemeModules F B, ⊤)) :
          Type u) :=
  crysSecondAffineCross F B

omit [IsAffine B.obj.thickening.target.scheme]
  [SheafOfModules.IsQuasicoherent (crysAmbientSchemeModules F B)] in
/-- `crysSecondAffineCrossModule` is a bijection. -/
theorem bijective_crysSecondAffineCrossModule :
    Function.Bijective (crysSecondAffineCrossModule F B) :=
  (crysSecondAffineCrossEquiv F B).bijective

omit [IsAffine B.obj.thickening.target.scheme]
  [SheafOfModules.IsQuasicoherent (crysAmbientSchemeModules F B)] in
/-- `crysSecondAffineCrossModule` on a pure tensor. -/
theorem crysSecondAffineCrossModule_tmul (t : crysSheafRing S (secondOrderThickeningObject S B.obj))
    (s : F.val.obj (op B)) :
    crysSecondAffineCrossModule F B (t ⊗ₜ[crysSheafRing S B.obj] s) =
      ambientRingSection (secondOrderThickeningObject S B.obj) t ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, ⊤),
        ((secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
          (SecondOrderAffine.top_le_preimage_siteQ₀ B.obj)).hom]
        crysAmbientModuleSection F B (crysSiteRestrict F (B.restrictOpenHom ⊤) s) :=
  crysSecondAffineCross_tmul F B t s

/-- The base-change comparison at `⊤, ⊤`, as an additive map. -/
def crysSecondAffineBaseChangeTopHom :
    ((ModuleCat.extendScalars ((secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
        (SecondOrderAffine.top_le_preimage_siteQ₀ B.obj)).hom).obj
      (ModuleCat.of Γ(B.obj.thickening.target.scheme, ⊤) Γ(crysAmbientSchemeModules F B, ⊤)) :
        Type u) →+
      ((ModuleCat.of Γ((secondOrderThickeningObject S B.obj).thickening.target.scheme, ⊤)
        Γ((Scheme.Modules.pullback (secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom).obj
          (crysAmbientSchemeModules F B), ⊤)) : Type u) :=
  (crysSecondAffineBaseChangeTopIso F B).hom.hom.toAddMonoidHom

/-- The base-change comparison, written out. -/
theorem crysSecondAffineBaseChangeTopHom_apply
    (w : ((ModuleCat.extendScalars ((secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
        (SecondOrderAffine.top_le_preimage_siteQ₀ B.obj)).hom).obj
      (ModuleCat.of Γ(B.obj.thickening.target.scheme, ⊤) Γ(crysAmbientSchemeModules F B, ⊤)) :
        Type u)) :
    crysSecondAffineBaseChangeTopHom F B w = (crysSecondAffineBaseChangeTopIso F B).hom w := rfl

/-- **The base-change comparison is bijective** under quasi-coherence and affineness. -/
theorem bijective_crysSecondAffineBaseChangeTopHom :
    Function.Bijective (crysSecondAffineBaseChangeTopHom F B) := by
  have h : (crysSecondAffineBaseChangeTopHom F B : _ → _) =
      fun w ↦ (crysSecondAffineBaseChangeTopIso F B).hom w :=
    funext fun w ↦ crysSecondAffineBaseChangeTopHom_apply F B w
  rw [h]
  exact ConcreteCategory.bijective_of_isIso (crysSecondAffineBaseChangeTopIso F B).hom

/-- `crysAmbientPullbackSectionTopAlong`, with its type named at the codomain of the base-change
comparison. -/
def crysSecondAmbientPullbackSectionTopModule (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    ((ModuleCat.of Γ((secondOrderThickeningObject S B.obj).thickening.target.scheme, ⊤)
      Γ((Scheme.Modules.pullback (secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom).obj
        (crysAmbientSchemeModules F B), ⊤)) : Type u) :=
  crysAmbientPullbackSectionTopAlong F (secondOrderThickeningCrysQ₀ S B) x

omit [IsAffine B.obj.thickening.target.scheme]
  [SheafOfModules.IsQuasicoherent (crysAmbientSchemeModules F B)] in
/-- `...SmallSite.crysAffineChainTailAlong_smul_crysAmbientPullbackSectionTopAlong`, read at the
codomain of the base-change comparison. -/
theorem crysAffineChainTailAlong_smul_crysSecondAmbientPullbackSectionTopModule
    (t : crysSheafRing S (secondOrderThickeningObject S B.obj))
    (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    crysAffineChainTailAlong F (secondOrderThickeningCrysQ₀ S B)
        (ambientRingSection (secondOrderThickeningObject S B.obj) t •
          crysSecondAmbientPullbackSectionTopModule F B x) =
      t • (crysRestrictOpenTopEquiv F (secondOrderThickeningCrysObject S B)).symm
        (crysSiteRestrict F (crysRestrictOpenMapTop (secondOrderThickeningCrysQ₀ S B))
          (crysSiteModuleSection F B x)) :=
  crysAffineChainTailAlong_smul_crysAmbientPullbackSectionTopAlong F
    (secondOrderThickeningCrysQ₀ S B) t x

/-- **The affine chain, as an additive map `D'' ⊗_D Mod ⟶ ℱ(U, T'', δ'')`.** -/
def crysSecondAffineExtensionHom :
    crysSheafRing S (secondOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) →+
      F.val.obj (op (secondOrderThickeningCrysObject S B)) :=
  ((crysAffineChainTailAlong F (secondOrderThickeningCrysQ₀ S B)).comp
    (crysSecondAffineBaseChangeTopHom F B)).comp (crysSecondAffineCrossModule F B)

/-- **The chain is bijective** for a crystal, on an object with affine ambient scheme and with
`ℱ_T` quasi-coherent. -/
theorem bijective_crysSecondAffineExtensionHom (hF : IsSheafCrystal F) :
    Function.Bijective (crysSecondAffineExtensionHom F B) :=
  ((bijective_crysAffineChainTailAlong F (secondOrderThickeningCrysQ₀ S B) hF).comp
    (bijective_crysSecondAffineBaseChangeTopHom F B)).comp
      (bijective_crysSecondAffineCrossModule F B)

/-! ### The chain is the base change of scalars -/

/-- The base-change comparison at `⊤, ⊤` carries `1 ⊗ a` to the pullback of `a`. -/
theorem crysSecondAffineBaseChangeTop_one_tmul
    (a : Γ(crysAmbientSchemeModules F B, (⊤ : B.obj.thickening.target.scheme.Opens))) :
    (affinePullbackSectionsBaseChangeIso (secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom
        (crysAmbientSchemeModules F B) (isAffineOpen_top _) (isAffineOpen_top _)
        (SecondOrderAffine.top_le_preimage_siteQ₀ B.obj)).hom ((1 : Γ(
        (secondOrderThickeningObject S B.obj).thickening.target.scheme,
        (⊤ : (secondOrderThickeningObject S B.obj).thickening.target.scheme.Opens))) ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, (⊤ : B.obj.thickening.target.scheme.Opens)),
        ((secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
          (SecondOrderAffine.top_le_preimage_siteQ₀ B.obj)).hom] a) =
      crysSecondAmbientPullbackSectionTopModule F B a :=
  affinePullbackSectionsBaseChangeIso_one_tmul
    (secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom
    (crysAmbientSchemeModules F B) (isAffineOpen_top _) (isAffineOpen_top _)
    (SecondOrderAffine.top_le_preimage_siteQ₀ B.obj) a

/-- The base-change comparison at `⊤, ⊤` carries `t ⊗ a` to `t` times the pullback of `a`. -/
theorem crysSecondAffineBaseChangeTop_tmul
    (r : Γ((secondOrderThickeningObject S B.obj).thickening.target.scheme,
      (⊤ : (secondOrderThickeningObject S B.obj).thickening.target.scheme.Opens)))
    (a : Γ(crysAmbientSchemeModules F B, (⊤ : B.obj.thickening.target.scheme.Opens))) :
    (affinePullbackSectionsBaseChangeIso (secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom
        (crysAmbientSchemeModules F B) (isAffineOpen_top _) (isAffineOpen_top _)
        (SecondOrderAffine.top_le_preimage_siteQ₀ B.obj)).hom (r ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, (⊤ : B.obj.thickening.target.scheme.Opens)),
        ((secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
          (SecondOrderAffine.top_le_preimage_siteQ₀ B.obj)).hom] a) =
      r • crysSecondAmbientPullbackSectionTopModule F B a :=
  (affinePullbackSectionsBaseChangeIso_tmul
    (secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom
    (crysAmbientSchemeModules F B) (isAffineOpen_top _) (isAffineOpen_top _)
    (SecondOrderAffine.top_le_preimage_siteQ₀ B.obj) r a).trans
      (congrArg (fun z ↦ r • z) (crysSecondAffineBaseChangeTop_one_tmul F B a))

/-- **The abbreviation naming the affine base-change comparison is that comparison.** -/
theorem crysSecondAffineBaseChangeTopIso_eq :
    crysSecondAffineBaseChangeTopIso F B =
      affinePullbackSectionsBaseChangeIso (secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom
        (crysAmbientSchemeModules F B) (isAffineOpen_top _) (isAffineOpen_top _)
        (SecondOrderAffine.top_le_preimage_siteQ₀ B.obj) := rfl

/-- `...SmallSite.crysSecondAffineBaseChangeTop_tmul`, read through the abbreviation
`...SmallSite.crysSecondAffineBaseChangeTopIso`. -/
theorem crysSecondAffineBaseChangeTopIso_hom_tmul
    (r : Γ((secondOrderThickeningObject S B.obj).thickening.target.scheme,
      (⊤ : (secondOrderThickeningObject S B.obj).thickening.target.scheme.Opens)))
    (a : Γ(crysAmbientSchemeModules F B, (⊤ : B.obj.thickening.target.scheme.Opens))) :
    (crysSecondAffineBaseChangeTopIso F B).hom (r ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, (⊤ : B.obj.thickening.target.scheme.Opens)),
        ((secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
          (SecondOrderAffine.top_le_preimage_siteQ₀ B.obj)).hom] a) =
      r • crysSecondAmbientPullbackSectionTopModule F B a := by
  rw [crysSecondAffineBaseChangeTopIso_eq]
  exact crysSecondAffineBaseChangeTop_tmul F B r a

/-- **The affine chain as a function**: the composite of `crysSecondAffineCrossModule`, the
base-change comparison applied as a morphism of `ModuleCat`, and `crysAffineChainTailAlong`. -/
def crysSecondAffineExtensionFun
    (z : crysSheafRing S (secondOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
      F.val.obj (op B)) : F.val.obj (op (secondOrderThickeningCrysObject S B)) :=
  crysAffineChainTailAlong F (secondOrderThickeningCrysQ₀ S B)
    ((crysSecondAffineBaseChangeTopIso F B).hom (crysSecondAffineCrossModule F B z))

/-- The function and the additive map are the same map. -/
theorem crysSecondAffineExtensionFun_eq_crysSecondAffineExtensionHom
    (z : crysSheafRing S (secondOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
      F.val.obj (op B)) :
    crysSecondAffineExtensionFun F B z = crysSecondAffineExtensionHom F B z := rfl

/-- **The chain and the base change of scalars agree on a pure tensor.** -/
theorem crysSecondAffineExtensionFun_tmul
    (t : crysSheafRing S (secondOrderThickeningObject S B.obj)) (s : F.val.obj (op B)) :
    crysSecondAffineExtensionFun F B (t ⊗ₜ[crysSheafRing S B.obj] s) =
      crysSecondExtensionSectionsMap F B (t ⊗ₜ[crysSheafRing S B.obj] s) := by
  have hcross : crysSecondAffineExtensionFun F B (t ⊗ₜ[crysSheafRing S B.obj] s) =
      crysAffineChainTailAlong F (secondOrderThickeningCrysQ₀ S B)
        ((crysSecondAffineBaseChangeTopIso F B).hom
          (ambientRingSection (secondOrderThickeningObject S B.obj) t ⊗ₜ[
            Γ(B.obj.thickening.target.scheme, (⊤ : B.obj.thickening.target.scheme.Opens)),
            ((secondOrderThickeningSiteQ₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
              (SecondOrderAffine.top_le_preimage_siteQ₀ B.obj)).hom]
            crysAmbientModuleSection F B (crysSiteRestrict F (B.restrictOpenHom ⊤) s))) :=
    congrArg (fun w ↦ crysAffineChainTailAlong F (secondOrderThickeningCrysQ₀ S B)
        ((crysSecondAffineBaseChangeTopIso F B).hom w))
      (crysSecondAffineCrossModule_tmul F B t s)
  have hcomp := congrArg
    (fun y ↦ crysAffineChainTailAlong F (secondOrderThickeningCrysQ₀ S B) y)
    (crysSecondAffineBaseChangeTopIso_hom_tmul F B
      (ambientRingSection (secondOrderThickeningObject S B.obj) t)
      (crysAmbientModuleSection F B (crysSiteRestrict F (B.restrictOpenHom ⊤) s)))
  have htail := crysAffineChainTailAlong_smul_crysSecondAmbientPullbackSectionTopModule F B t
    (crysAmbientModuleSection F B (crysSiteRestrict F (B.restrictOpenHom ⊤) s))
  exact ((hcross.trans hcomp).trans htail).trans
    (crysSecondExtensionSectionsMap_tmul_crysRestrictOpenMapTop F B t s).symm

/-- `...SmallSite.crysSecondAffineExtensionFun_tmul`, for the additive map. -/
theorem crysSecondAffineExtensionHom_tmul
    (t : crysSheafRing S (secondOrderThickeningObject S B.obj)) (s : F.val.obj (op B)) :
    crysSecondAffineExtensionHom F B (t ⊗ₜ[crysSheafRing S B.obj] s) =
      crysSecondExtensionSectionsMap F B (t ⊗ₜ[crysSheafRing S B.obj] s) :=
  (crysSecondAffineExtensionFun_eq_crysSecondAffineExtensionHom F B
      (t ⊗ₜ[crysSheafRing S B.obj] s)).symm.trans
    (crysSecondAffineExtensionFun_tmul F B t s)

/-- **The affine chain is the base change of scalars.** -/
theorem crysSecondExtensionSectionsMap_eq_crysSecondAffineExtensionHom :
    (crysSecondExtensionSectionsMap F B : _ → _) = (crysSecondAffineExtensionHom F B : _ → _) := by
  funext w
  induction w using TensorProduct.inductionOn with
  | tmul t s => exact (crysSecondAffineExtensionHom_tmul F B t s).symm
  | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-- **The base change of sections `D'' ⊗_D Mod ⟶ ℱ(U, T'', δ'')` on `Cris(X/S)` is bijective**
for a crystal on an object whose ambient scheme is affine and with `ℱ_T` quasi-coherent. -/
theorem bijective_crysSecondExtensionSectionsMap (hF : IsSheafCrystal F) :
    Function.Bijective (crysSecondExtensionSectionsMap F B) := by
  rw [crysSecondExtensionSectionsMap_eq_crysSecondAffineExtensionHom F B]
  exact bijective_crysSecondAffineExtensionHom F B hF

end Affine

/-- **The base change of sections on `Cris(X/S)` is bijective for a crystal in quasi-coherent
`𝒪_{X/S}`-modules over an object with affine ambient scheme.** -/
theorem bijective_crysSecondExtensionSectionsMap_of_isQuasicoherentOnSite
    [IsAffine B.obj.thickening.target.scheme] (hF : F.IsQuasicoherentOnSite) :
    Function.Bijective (crysSecondExtensionSectionsMap F B) :=
  have := isQuasicoherent_crysAmbientSchemeModules F B
    ((isQuasicoherentOnSite_iff F).1 hF).1
  bijective_crysSecondExtensionSectionsMap F B ((isQuasicoherentOnSite_iff F).1 hF).2

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
