module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineComparisonAlong
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentOfCrystal

/-!
# The base change of sections of [Stacks, Tag 07J6] on `Cris(X/S)`, over an affine object

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `ℱ` be a sheaf
of `𝒪_{X/S}`-modules on the **small** crystalline site `Cris(X/S)` and let `(U, T, δ)` be an
object of `Cris(X/S)` with first-order universal thickening `(U, T', δ')` of [Stacks, Tag 07J2].
Write `D = Γ(T, 𝒪_T)`, `D' = Γ(T', 𝒪_{T'})` and `Mod = ℱ(U, T, δ)`.

The base change of sections along `p₀` is

`...SmallSite.crysExtensionSectionsMap : D' ⊗_D Mod ⟶ ℱ(U, T', δ')`,  `t ⊗ s ↦ t · p₀^* s`.

**This module proves that map bijective** for `ℱ` a crystal with `ℱ_T` quasi-coherent on an
object whose ambient scheme is affine, which is the affine statement of [Stacks, Tag 07J6] read on
the small site. It is the composite (the *affine chain*)

`D' ⊗_D Γ(T, ℱ_T) ≅ Γ(T', p₀^* ℱ_T) ≅ Γ(T', ℱ_{T'})`,

the first isomorphism `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` at `U = V = ⊤` under
quasi-coherence and affineness, and the second the crystal condition of `ℱ` at the single morphism
`p₀` of `Cris(X/S)`, which is `...SmallSite.crysAffineChainTailAlong`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crysAffineCrossEquiv` — the change of spelling `D' ⊗_D Mod ≅ Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)}
  Γ(T, ℱ_T)` between the source of the base-change map and the source of the affine comparison.
  No hypothesis.
* `crysAffineExtensionHom` — the affine chain itself, an additive map `D' ⊗_D Mod ⟶ ℱ(U, T', δ')`.

## Main results

* `bijective_crysAffineExtensionHom` — each factor of the chain is a bijection, and so is the
  chain.
* `crysExtensionSectionsMap_eq_crysAffineExtensionHom` — the chain **is** the base change of
  scalars.
* `bijective_crysExtensionSectionsMap` — **the base change of sections of a crystal on
  `Cris(X/S)` over an object with affine ambient scheme and quasi-coherent `ℱ_T` is bijective.**
* `bijective_crysExtensionSectionsMap_of_isQuasicoherentOnSite` — the same for a crystal in
  quasi-coherent modules, the two side conditions being read off [Stacks, Tag 07IT].

## References

* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
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

/-! ### The restriction to the ambient scheme of a locally quasi-coherent sheaf -/

/-- **The restriction `ℱ_T` of a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)`
to the ambient scheme of an object is quasi-coherent**. -/
theorem isQuasicoherent_crysAmbientSchemeModules (hF : IsLocallyQuasiCoherent F) :
    (crysAmbientSchemeModules F B).IsQuasicoherent :=
  isQuasicoherent_ambientModuleRestriction hF B

/-! ### The change of spelling of the two tensor products -/

/-- The bilinear datum of `...SmallSite.crysAffineCross`. -/
def crysAffineCrossAux :
    crysSheafRing S (firstOrderThickeningObject S B.obj) →+
      (F.val.obj (op B) →+
        Γ((firstOrderThickeningObject S B.obj).thickening.target.scheme, ⊤) ⊗[
          Γ(B.obj.thickening.target.scheme, ⊤)] Γ(crysAmbientSchemeModules F B, ⊤)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun s ↦ ambientRingSection (firstOrderThickeningObject S B.obj) t ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, ⊤)]
        crysAmbientModuleSection F B (crysSiteRestrict F (B.restrictOpenHom ⊤) s))
      (fun s s' ↦ (congrArg
          (fun y ↦ ambientRingSection (firstOrderThickeningObject S B.obj) t ⊗ₜ[
            Γ(B.obj.thickening.target.scheme, ⊤)] crysAmbientModuleSection F B y)
          (crysSiteRestrict_add F (B.restrictOpenHom ⊤) s s')).trans
        (TensorProduct.tmul_add _ _ _)))
    (fun _ _ ↦ AddMonoidHom.ext fun _ ↦ TensorProduct.add_tmul _ _ _)

/-- `crysAffineCrossAux` sends a section `t` of `𝒪_{T'}` and a section `s` of `ℱ` on `T` to
`t ⊗ p₀^* s`. -/
@[simp]
theorem crysAffineCrossAux_apply (t : crysSheafRing S (firstOrderThickeningObject S B.obj))
    (s : F.val.obj (op B)) :
    crysAffineCrossAux F B t s =
      ambientRingSection (firstOrderThickeningObject S B.obj) t ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, ⊤)]
        crysAmbientModuleSection F B (crysSiteRestrict F (B.restrictOpenHom ⊤) s) := rfl

/-- **The base change of the sections of `ℱ` along `p₀`, carried into the tensor product of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`**: the map
`D' ⊗_D Mod ⟶ Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, ℱ_T)` sending `t ⊗ s` to `t ⊗ p₀^* s`.  No
hypothesis. -/
def crysAffineCross :
    crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) →+
      Γ((firstOrderThickeningObject S B.obj).thickening.target.scheme, ⊤) ⊗[
        Γ(B.obj.thickening.target.scheme, ⊤)] Γ(crysAmbientSchemeModules F B, ⊤) :=
  TensorProduct.liftAddHom (crysAffineCrossAux F B) (fun b t s ↦ by
    rw [crysAffineCrossAux_apply, crysAffineCrossAux_apply, ← ambientRingSection_smul,
      TensorProduct.smul_tmul, crysAmbientModuleSection_smul, crysSiteRestrict_smul])

/-- `crysAffineCross` sends the pure tensor `t ⊗ s` to `t ⊗ p₀^* s`. -/
@[simp]
theorem crysAffineCross_tmul (t : crysSheafRing S (firstOrderThickeningObject S B.obj))
    (s : F.val.obj (op B)) :
    crysAffineCross F B (t ⊗ₜ[crysSheafRing S B.obj] s) =
      ambientRingSection (firstOrderThickeningObject S B.obj) t ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, ⊤)]
        crysAmbientModuleSection F B (crysSiteRestrict F (B.restrictOpenHom ⊤) s) :=
  TensorProduct.liftAddHom_tmul _ _ t s

/-- The bilinear datum of `...SmallSite.crysAffineCrossInv`. -/
def crysAffineCrossInvAux :
    Γ((firstOrderThickeningObject S B.obj).thickening.target.scheme, ⊤) →+
      (Γ(crysAmbientSchemeModules F B, ⊤) →+
        crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
          F.val.obj (op B)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun x ↦ siteRingSection (firstOrderThickeningObject S B.obj) t ⊗ₜ[crysSheafRing S B.obj]
        (crysRestrictOpenTopEquiv F B).symm (crysSiteModuleSection F B x))
      (fun x y ↦ (congrArg
          (fun z ↦ siteRingSection (firstOrderThickeningObject S B.obj) t ⊗ₜ[
            crysSheafRing S B.obj] z)
          (map_add (crysRestrictOpenTopEquiv F B).symm (crysSiteModuleSection F B x)
            (crysSiteModuleSection F B y))).trans
        (TensorProduct.tmul_add _ _ _)))
    (fun _ _ ↦ AddMonoidHom.ext fun _ ↦ TensorProduct.add_tmul _ _ _)

/-- `crysAffineCrossInvAux` sends a section `t` of `𝒪_{T'}` and a section `x` of `ℱ_T` to
`t ⊗ (p₀^*)⁻¹ x`. -/
@[simp]
theorem crysAffineCrossInvAux_apply
    (t : Γ((firstOrderThickeningObject S B.obj).thickening.target.scheme, ⊤))
    (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    crysAffineCrossInvAux F B t x =
      siteRingSection (firstOrderThickeningObject S B.obj) t ⊗ₜ[crysSheafRing S B.obj]
        (crysRestrictOpenTopEquiv F B).symm (crysSiteModuleSection F B x) := rfl

/-- **The inverse of `...SmallSite.crysAffineCross`**, the map
`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, ℱ_T) ⟶ D' ⊗_D Mod` sending `t ⊗ x` to `t ⊗ (p₀^*)⁻¹ x`. -/
def crysAffineCrossInv :
    Γ((firstOrderThickeningObject S B.obj).thickening.target.scheme, ⊤) ⊗[
        Γ(B.obj.thickening.target.scheme, ⊤)] Γ(crysAmbientSchemeModules F B, ⊤) →+
      crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) :=
  TensorProduct.liftAddHom (crysAffineCrossInvAux F B) (fun r t x ↦ by
    rw [crysAffineCrossInvAux_apply, crysAffineCrossInvAux_apply, smul_eq_ambientRingSection,
      siteRingSection_ambientRingSection, TensorProduct.smul_tmul,
      crysRestrictOpenTopEquiv_symm_smul])

/-- `crysAffineCrossInv` sends the pure tensor `t ⊗ x` to `t ⊗ (p₀^*)⁻¹ x`. -/
@[simp]
theorem crysAffineCrossInv_tmul
    (t : Γ((firstOrderThickeningObject S B.obj).thickening.target.scheme, ⊤))
    (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    crysAffineCrossInv F B (t ⊗ₜ[Γ(B.obj.thickening.target.scheme, ⊤)] x) =
      siteRingSection (firstOrderThickeningObject S B.obj) t ⊗ₜ[crysSheafRing S B.obj]
        (crysRestrictOpenTopEquiv F B).symm (crysSiteModuleSection F B x) :=
  TensorProduct.liftAddHom_tmul _ _ t x

/-- **The two tensor products of the affine computation of the base change agree**, as an additive
equivalence

`D' ⊗_D Mod ≅ Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, ℱ_T)`.

It is unconditional: no crystal hypothesis, no quasi-coherence, no affineness. -/
def crysAffineCrossEquiv :
    crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) ≃+
      Γ((firstOrderThickeningObject S B.obj).thickening.target.scheme, ⊤) ⊗[
        Γ(B.obj.thickening.target.scheme, ⊤)] Γ(crysAmbientSchemeModules F B, ⊤) where
  toFun := crysAffineCross F B
  invFun := crysAffineCrossInv F B
  map_add' := map_add (crysAffineCross F B)
  left_inv z := by
    induction z using TensorProduct.inductionOn with
    | tmul t s =>
        rw [crysAffineCross_tmul, crysAffineCrossInv_tmul, siteRingSection_ambientRingSection,
          crysSiteModuleSection_crysAmbientModuleSection, ← crysRestrictOpenTopEquiv_apply,
          AddEquiv.symm_apply_apply]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  right_inv w := by
    induction w using TensorProduct.inductionOn with
    | tmul t x =>
        rw [crysAffineCrossInv_tmul, crysAffineCross_tmul,
          crysSiteRestrict_crysRestrictOpenTopEquiv_symm]
        rfl
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-! ### The base change of scalars on a pure tensor -/

/-- **The base change of scalars on a pure tensor**: `t ⊗ s` goes to `t` times the restriction
along `p₀` of `s`, passed through the sections of `ℱ_T` over `⊤`. -/
theorem crysExtensionSectionsMap_tmul_crysRestrictOpenMapTop
    (t : crysSheafRing S (firstOrderThickeningObject S B.obj)) (s : F.val.obj (op B)) :
    crysExtensionSectionsMap F B (t ⊗ₜ[crysSheafRing S B.obj] s) =
      t • (crysRestrictOpenTopEquiv F (firstOrderThickeningCrysObject S B)).symm
        (crysSiteRestrict F (crysRestrictOpenMapTop (firstOrderThickeningCrysP₀ S B))
          (crysSiteModuleSection F B
            (crysAmbientModuleSection F B
              (crysSiteRestrict F (B.restrictOpenHom ⊤) s)))) := by
  rw [crysExtensionSectionsMap_tmul, crysSiteModuleSection_crysAmbientModuleSection]
  refine congrArg (fun y ↦ t • y) (Eq.symm ?_)
  rw [AddEquiv.symm_apply_eq, crysRestrictOpenTopEquiv_apply]
  exact crysSiteRestrict_crysRestrictOpenMapTop F (firstOrderThickeningCrysP₀ S B) s

/-! ### The chain on an affine object -/

section Affine

variable [IsAffine B.obj.thickening.target.scheme]
  [(crysAmbientSchemeModules F B).IsQuasicoherent]

/-- The affine base-change comparison of [Stacks, Tag 01I9] at the whole of the two ambient
schemes, which are affine. -/
abbrev crysAffineBaseChangeTopIso :=
  affinePullbackSectionsBaseChangeIso (firstOrderThickeningSiteP₀ S B.obj).targetHom.hom
    (crysAmbientSchemeModules F B) (isAffineOpen_top _) (isAffineOpen_top _)
    (top_le_preimage_siteP₀ B.obj)

/-- `crysAffineCross`, with its target named at the extension of scalars of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`. -/
def crysAffineCrossModule :
    crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) →+
      ((ModuleCat.extendScalars ((firstOrderThickeningSiteP₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteP₀ B.obj)).hom).obj
        (ModuleCat.of Γ(B.obj.thickening.target.scheme, ⊤) Γ(crysAmbientSchemeModules F B, ⊤)) :
          Type u) :=
  crysAffineCross F B

omit [IsAffine B.obj.thickening.target.scheme]
  [SheafOfModules.IsQuasicoherent (crysAmbientSchemeModules F B)] in
/-- `crysAffineCrossModule` is a bijection, being `crysAffineCrossEquiv`. -/
theorem bijective_crysAffineCrossModule : Function.Bijective (crysAffineCrossModule F B) :=
  (crysAffineCrossEquiv F B).bijective

omit [IsAffine B.obj.thickening.target.scheme]
  [SheafOfModules.IsQuasicoherent (crysAmbientSchemeModules F B)] in
/-- `crysAffineCrossModule` sends the pure tensor `t ⊗ s` to `t ⊗ p₀^* s`. -/
theorem crysAffineCrossModule_tmul (t : crysSheafRing S (firstOrderThickeningObject S B.obj))
    (s : F.val.obj (op B)) :
    crysAffineCrossModule F B (t ⊗ₜ[crysSheafRing S B.obj] s) =
      ambientRingSection (firstOrderThickeningObject S B.obj) t ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, ⊤),
        ((firstOrderThickeningSiteP₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteP₀ B.obj)).hom]
        crysAmbientModuleSection F B (crysSiteRestrict F (B.restrictOpenHom ⊤) s) :=
  crysAffineCross_tmul F B t s

/-- The base-change comparison at `⊤, ⊤`, as an additive map. -/
def crysAffineBaseChangeTopHom :
    ((ModuleCat.extendScalars ((firstOrderThickeningSiteP₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
        (top_le_preimage_siteP₀ B.obj)).hom).obj
      (ModuleCat.of Γ(B.obj.thickening.target.scheme, ⊤) Γ(crysAmbientSchemeModules F B, ⊤)) :
        Type u) →+
      ((ModuleCat.of Γ((firstOrderThickeningObject S B.obj).thickening.target.scheme, ⊤)
        Γ((Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S B.obj).targetHom.hom).obj
          (crysAmbientSchemeModules F B), ⊤)) : Type u) :=
  (crysAffineBaseChangeTopIso F B).hom.hom.toAddMonoidHom

/-- The base-change comparison, written out. -/
theorem crysAffineBaseChangeTopHom_apply
    (w : ((ModuleCat.extendScalars ((firstOrderThickeningSiteP₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
        (top_le_preimage_siteP₀ B.obj)).hom).obj
      (ModuleCat.of Γ(B.obj.thickening.target.scheme, ⊤) Γ(crysAmbientSchemeModules F B, ⊤)) :
        Type u)) :
    crysAffineBaseChangeTopHom F B w = (crysAffineBaseChangeTopIso F B).hom w := rfl

/-- **The base-change comparison is bijective** under quasi-coherence and affineness, being an
isomorphism of `ModuleCat`. -/
theorem bijective_crysAffineBaseChangeTopHom :
    Function.Bijective (crysAffineBaseChangeTopHom F B) := by
  have h : (crysAffineBaseChangeTopHom F B : _ → _) =
      fun w ↦ (crysAffineBaseChangeTopIso F B).hom w :=
    funext fun w ↦ crysAffineBaseChangeTopHom_apply F B w
  rw [h]
  exact ConcreteCategory.bijective_of_isIso (crysAffineBaseChangeTopIso F B).hom

/-- `crysAmbientPullbackSectionTopAlong`, with its type named at the codomain of the base-change
comparison. -/
def crysAmbientPullbackSectionTopModule (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    ((ModuleCat.of Γ((firstOrderThickeningObject S B.obj).thickening.target.scheme, ⊤)
      Γ((Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S B.obj).targetHom.hom).obj
        (crysAmbientSchemeModules F B), ⊤)) : Type u) :=
  crysAmbientPullbackSectionTopAlong F (firstOrderThickeningCrysP₀ S B) x

omit [IsAffine B.obj.thickening.target.scheme]
  [SheafOfModules.IsQuasicoherent (crysAmbientSchemeModules F B)] in
/-- `...SmallSite.crysAffineChainTailAlong_smul_crysAmbientPullbackSectionTopAlong`, read at the
codomain of the base-change comparison. -/
theorem crysAffineChainTailAlong_smul_crysAmbientPullbackSectionTopModule
    (t : crysSheafRing S (firstOrderThickeningObject S B.obj))
    (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    crysAffineChainTailAlong F (firstOrderThickeningCrysP₀ S B)
        (ambientRingSection (firstOrderThickeningObject S B.obj) t •
          crysAmbientPullbackSectionTopModule F B x) =
      t • (crysRestrictOpenTopEquiv F (firstOrderThickeningCrysObject S B)).symm
        (crysSiteRestrict F (crysRestrictOpenMapTop (firstOrderThickeningCrysP₀ S B))
          (crysSiteModuleSection F B x)) :=
  crysAffineChainTailAlong_smul_crysAmbientPullbackSectionTopAlong F
    (firstOrderThickeningCrysP₀ S B) t x

/-- **The affine chain, as an additive map `D' ⊗_D Mod ⟶ ℱ(U, T', δ')`.** -/
def crysAffineExtensionHom :
    crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) →+
      F.val.obj (op (firstOrderThickeningCrysObject S B)) :=
  ((crysAffineChainTailAlong F (firstOrderThickeningCrysP₀ S B)).comp
    (crysAffineBaseChangeTopHom F B)).comp (crysAffineCrossModule F B)

/-- **The chain is bijective** for a crystal, on an object with affine ambient scheme and with
`ℱ_T` quasi-coherent: each of its three factors is. -/
theorem bijective_crysAffineExtensionHom (hF : IsSheafCrystal F) :
    Function.Bijective (crysAffineExtensionHom F B) :=
  ((bijective_crysAffineChainTailAlong F (firstOrderThickeningCrysP₀ S B) hF).comp
    (bijective_crysAffineBaseChangeTopHom F B)).comp (bijective_crysAffineCrossModule F B)

/-! ### The chain is the base change of scalars -/

/-- The base-change comparison at `⊤, ⊤` carries `1 ⊗ a` to the pullback of `a`. -/
theorem crysAffineBaseChangeTop_one_tmul
    (a : Γ(crysAmbientSchemeModules F B, (⊤ : B.obj.thickening.target.scheme.Opens))) :
    (affinePullbackSectionsBaseChangeIso (firstOrderThickeningSiteP₀ S B.obj).targetHom.hom
        (crysAmbientSchemeModules F B) (isAffineOpen_top _) (isAffineOpen_top _)
        (top_le_preimage_siteP₀ B.obj)).hom ((1 : Γ(
        (firstOrderThickeningObject S B.obj).thickening.target.scheme,
        (⊤ : (firstOrderThickeningObject S B.obj).thickening.target.scheme.Opens))) ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, (⊤ : B.obj.thickening.target.scheme.Opens)),
        ((firstOrderThickeningSiteP₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteP₀ B.obj)).hom] a) =
      crysAmbientPullbackSectionTopModule F B a :=
  affinePullbackSectionsBaseChangeIso_one_tmul
    (firstOrderThickeningSiteP₀ S B.obj).targetHom.hom
    (crysAmbientSchemeModules F B) (isAffineOpen_top _) (isAffineOpen_top _)
    (top_le_preimage_siteP₀ B.obj) a

/-- The base-change comparison at `⊤, ⊤` carries `t ⊗ a` to `t` times the pullback of `a`. -/
theorem crysAffineBaseChangeTop_tmul
    (r : Γ((firstOrderThickeningObject S B.obj).thickening.target.scheme,
      (⊤ : (firstOrderThickeningObject S B.obj).thickening.target.scheme.Opens)))
    (a : Γ(crysAmbientSchemeModules F B, (⊤ : B.obj.thickening.target.scheme.Opens))) :
    (affinePullbackSectionsBaseChangeIso (firstOrderThickeningSiteP₀ S B.obj).targetHom.hom
        (crysAmbientSchemeModules F B) (isAffineOpen_top _) (isAffineOpen_top _)
        (top_le_preimage_siteP₀ B.obj)).hom (r ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, (⊤ : B.obj.thickening.target.scheme.Opens)),
        ((firstOrderThickeningSiteP₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteP₀ B.obj)).hom] a) =
      r • crysAmbientPullbackSectionTopModule F B a :=
  (affinePullbackSectionsBaseChangeIso_tmul
    (firstOrderThickeningSiteP₀ S B.obj).targetHom.hom
    (crysAmbientSchemeModules F B) (isAffineOpen_top _) (isAffineOpen_top _)
    (top_le_preimage_siteP₀ B.obj) r a).trans
      (congrArg (fun z ↦ r • z) (crysAffineBaseChangeTop_one_tmul F B a))

/-- **The abbreviation naming the affine base-change comparison is that comparison.** -/
theorem crysAffineBaseChangeTopIso_eq :
    crysAffineBaseChangeTopIso F B =
      affinePullbackSectionsBaseChangeIso (firstOrderThickeningSiteP₀ S B.obj).targetHom.hom
        (crysAmbientSchemeModules F B) (isAffineOpen_top _) (isAffineOpen_top _)
        (top_le_preimage_siteP₀ B.obj) := rfl

/-- `...SmallSite.crysAffineBaseChangeTop_tmul`, stated for `crysAffineBaseChangeTopIso`. -/
theorem crysAffineBaseChangeTopIso_hom_tmul
    (r : Γ((firstOrderThickeningObject S B.obj).thickening.target.scheme,
      (⊤ : (firstOrderThickeningObject S B.obj).thickening.target.scheme.Opens)))
    (a : Γ(crysAmbientSchemeModules F B, (⊤ : B.obj.thickening.target.scheme.Opens))) :
    (crysAffineBaseChangeTopIso F B).hom (r ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, (⊤ : B.obj.thickening.target.scheme.Opens)),
        ((firstOrderThickeningSiteP₀ S B.obj).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteP₀ B.obj)).hom] a) =
      r • crysAmbientPullbackSectionTopModule F B a := by
  rw [crysAffineBaseChangeTopIso_eq]
  exact crysAffineBaseChangeTop_tmul F B r a

/-- **The affine chain as a function**: the composite of `crysAffineCrossModule`, the base-change
comparison applied as a morphism of `ModuleCat`, and `crysAffineChainTailAlong`. -/
def crysAffineExtensionFun
    (z : crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
      F.val.obj (op B)) : F.val.obj (op (firstOrderThickeningCrysObject S B)) :=
  crysAffineChainTailAlong F (firstOrderThickeningCrysP₀ S B)
    ((crysAffineBaseChangeTopIso F B).hom (crysAffineCrossModule F B z))

/-- The function and the additive map are the same map. -/
theorem crysAffineExtensionFun_eq_crysAffineExtensionHom
    (z : crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
      F.val.obj (op B)) :
    crysAffineExtensionFun F B z = crysAffineExtensionHom F B z := rfl

/-- **The chain and the base change of scalars agree on a pure tensor.** -/
theorem crysAffineExtensionFun_tmul
    (t : crysSheafRing S (firstOrderThickeningObject S B.obj)) (s : F.val.obj (op B)) :
    crysAffineExtensionFun F B (t ⊗ₜ[crysSheafRing S B.obj] s) =
      crysExtensionSectionsMap F B (t ⊗ₜ[crysSheafRing S B.obj] s) := by
  rw [crysExtensionSectionsMap_tmul_crysRestrictOpenMapTop,
    ← crysAffineChainTailAlong_smul_crysAmbientPullbackSectionTopModule,
    ← crysAffineBaseChangeTopIso_hom_tmul]
  exact congrArg (fun w ↦ crysAffineChainTailAlong F (firstOrderThickeningCrysP₀ S B)
    ((crysAffineBaseChangeTopIso F B).hom w)) (crysAffineCrossModule_tmul F B t s)

/-- `...SmallSite.crysAffineExtensionFun_tmul`, for the additive map. -/
theorem crysAffineExtensionHom_tmul
    (t : crysSheafRing S (firstOrderThickeningObject S B.obj)) (s : F.val.obj (op B)) :
    crysAffineExtensionHom F B (t ⊗ₜ[crysSheafRing S B.obj] s) =
      crysExtensionSectionsMap F B (t ⊗ₜ[crysSheafRing S B.obj] s) :=
  (crysAffineExtensionFun_eq_crysAffineExtensionHom F B
      (t ⊗ₜ[crysSheafRing S B.obj] s)).symm.trans
    (crysAffineExtensionFun_tmul F B t s)

/-- **The affine chain is the base change of scalars**: two additive maps agreeing on every pure
tensor agree. -/
theorem crysExtensionSectionsMap_eq_crysAffineExtensionHom :
    (crysExtensionSectionsMap F B : _ → _) = (crysAffineExtensionHom F B : _ → _) := by
  funext w
  induction w using TensorProduct.inductionOn with
  | tmul t s => exact (crysAffineExtensionHom_tmul F B t s).symm
  | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-- **The base change of sections `D' ⊗_D Mod ⟶ ℱ(U, T', δ')` on `Cris(X/S)` is bijective** for a
crystal on an object whose ambient scheme is affine and with `ℱ_T` quasi-coherent.  This is the
affine statement of [Stacks, Tag 07J6] on the small crystalline site. -/
theorem bijective_crysExtensionSectionsMap (hF : IsSheafCrystal F) :
    Function.Bijective (crysExtensionSectionsMap F B) := by
  rw [crysExtensionSectionsMap_eq_crysAffineExtensionHom F B]
  exact bijective_crysAffineExtensionHom F B hF

end Affine

/-- **The base change of sections on `Cris(X/S)` is bijective for a crystal in quasi-coherent
`𝒪_{X/S}`-modules over an object with affine ambient scheme.**  Both side conditions of
`...SmallSite.bijective_crysExtensionSectionsMap` are read off [Stacks, Tag 07IT]: quasi-coherence
on the site gives local quasi-coherence, hence quasi-coherence of `ℱ_T`, and the crystal
condition. -/
theorem bijective_crysExtensionSectionsMap_of_isQuasicoherentOnSite
    [IsAffine B.obj.thickening.target.scheme] (hF : F.IsQuasicoherentOnSite) :
    Function.Bijective (crysExtensionSectionsMap F B) :=
  have := isQuasicoherent_crysAmbientSchemeModules F B
    ((isQuasicoherentOnSite_iff F).1 hF).1
  bijective_crysExtensionSectionsMap F B ((isQuasicoherentOnSite_iff F).1 hF).2

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
