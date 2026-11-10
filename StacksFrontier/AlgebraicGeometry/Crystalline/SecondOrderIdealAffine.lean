module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineComparisonAlong
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalConnectionIntegrable

/-!
# The base change of the sections along `q₀ : T'' ⟶ T` on an affine object

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the big crystalline site, let `(U, T, δ)` be an object of `CRIS(X/S)`, and
let `(U, T'', δ'')` be the second-order universal thickening of [Stacks, Remark 60.14.5,
Tag 07J3] with first projection `q₀ : T'' ⟶ T`.  Write `D = Γ(T, 𝒪_T)`,
`D'' = Γ(T'', 𝒪_{T''})` and `M = F(U, T, δ)`.

This module proves that

`D'' ⊗_D M ⟶ F(U, T'', δ'')`,   `t ⊗ s ↦ t · q₀^* s`

is **bijective** for a locally quasi-coherent sheaf crystal on an object whose ambient scheme is
affine.  The map is written as the chain

`D'' ⊗_D M ≅ Γ(T'', 𝒪_{T''}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T) ⟶ Γ(T'', q₀^* F_T) ⟶ Γ(T'', F_{T''})`

of a change of spelling, the affine base-change comparison
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` of [Stacks, Tag 01I9], and the comparison
map of [Stacks, Tag 07IQ] at `q₀`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.extensionSectionsMap` — the base
  change of the sections of `F` along `q₀`, on the algebraic tensor product of global sections.
* `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineCrossEquiv` — the change of
  spelling between the two tensor products of the computation.
* `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineExtensionHom` — the chain above.

## Main results

* `...GlobalCrystallineSituation.SecondOrderAffine.extensionSectionsMap_eq_affineExtensionHom`
  — the chain **is** the base change of scalars.
* `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.bijective_extensionSectionsMap` —
  **the base change of the sections along `q₀` is bijective** for a sheaf crystal on an object
  with affine ambient scheme and quasi-coherent `F_T`.

## References

* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry TensorProduct ChangeOfRings

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

namespace SecondOrderAffine

variable {S : GlobalCrystallineSituation.{u}}
  (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)

/-! ### The base change of the sections along `q₀` -/

/-- The sections of `𝒪_{X/S}` over the second-order universal thickening, as an algebra over the
sections over the object, through `q₀`. -/
instance algebraCrysSheafRingSiteQ₀ :
    Algebra (crysSheafRing S A) (crysSheafRing S (secondOrderThickeningObject S A)) :=
  (crysSheafRingMap (secondOrderThickeningSiteQ₀ S A)).toAlgebra

/-- The scalars of `Γ(T, 𝒪_T)` act on `Γ(T'', 𝒪_{T''})` by multiplication after `q₀`. -/
theorem crysSheafRing_smul_def (b : crysSheafRing S A)
    (t : crysSheafRing S (secondOrderThickeningObject S A)) :
    b • t = crysSheafRingMap (secondOrderThickeningSiteQ₀ S A) b * t := rfl

/-- The bilinear datum of
`Crystalline.GlobalCrystallineSituation.SecondOrderAffine.extensionSectionsMap`. -/
def extensionSectionsAux :
    crysSheafRing S (secondOrderThickeningObject S A) →+
      (M.val.obj (op A) →+ M.val.obj (op (secondOrderThickeningObject S A))) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun s ↦ t • moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s)
      (fun s s' ↦ by rw [map_add, smul_add]))
    (fun _ _ ↦ AddMonoidHom.ext fun _ ↦ add_smul _ _ _)

/-- **The base change of the sections of `F` along `q₀`**, on the algebraic tensor product of
global sections: the map `Γ(T'', 𝒪_{T''}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T) ⟶ Γ(T'', F_{T''})` sending
`t ⊗ s` to `t · q₀^* s`. -/
def extensionSectionsMap :
    crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) →+
      M.val.obj (op (secondOrderThickeningObject S A)) :=
  TensorProduct.liftAddHom (extensionSectionsAux M A) (fun b t s ↦ by
    change (b • t) • moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s =
      t • moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) (b • s)
    rw [map_smulₛₗ, crysSheafRing_smul_def, smul_smul, mul_comm])

/-- **The base change of scalars on a pure tensor**: `t ⊗ s ↦ t · q₀^* s`. -/
@[simp]
theorem extensionSectionsMap_tmul (t : crysSheafRing S (secondOrderThickeningObject S A))
    (s : M.val.obj (op A)) :
    extensionSectionsMap M A (t ⊗ₜ[crysSheafRing S A] s) =
      t • moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s :=
  TensorProduct.liftAddHom_tmul _ _ t s

/-! ### The change of spelling between the two tensor products -/

/-- The whole of the ambient scheme of the second-order universal thickening is contained in the
preimage of the whole of the ambient scheme of the object. -/
theorem top_le_preimage_siteQ₀ :
    (⊤ : (secondOrderThickeningObject S A).thickening.target.scheme.Opens) ≤
      (secondOrderThickeningSiteQ₀ S A).targetHom.hom ⁻¹ᵁ ⊤ :=
  top_le_preimage_ambient (secondOrderThickeningSiteQ₀ S A)

/-- **The sections of `𝒪_{T''}` over the ambient scheme, as a module over the sections of `𝒪_T`
over the ambient scheme, through the morphism `q₀ : T'' ⟶ T` of ambient schemes.** -/
instance moduleAmbientSiteQ₀ :
    Module Γ(A.thickening.target.scheme, ⊤)
      Γ((secondOrderThickeningObject S A).thickening.target.scheme, ⊤) :=
  Module.compHom _
    ((secondOrderThickeningSiteQ₀ S A).targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_siteQ₀ A)).hom

/-- **The two actions of the sections of `𝒪_T` on the sections of `𝒪_{T''}` agree** — the one
through the restriction map of the site along `q₀` and the one through the map on sections of the
morphism `q₀` of ambient schemes. -/
theorem ambientRingSection_smul (b : crysSheafRing S A)
    (t : crysSheafRing S (secondOrderThickeningObject S A)) :
    ambientRingSection A b • ambientRingSection (secondOrderThickeningObject S A) t =
      ambientRingSection (secondOrderThickeningObject S A) (b • t) :=
  congrArg (fun y ↦ y * ambientRingSection (secondOrderThickeningObject S A) t)
    (appLE_top_eq_crysSheafRingMap (secondOrderThickeningSiteQ₀ S A)
      (top_le_preimage_siteQ₀ A) (ambientRingSection A b))

/-- `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.ambientRingSection_smul`, read with
the scalar and the section in the spelling of the ambient schemes. -/
theorem smul_eq_ambientRingSection (r : Γ(A.thickening.target.scheme, ⊤))
    (t : Γ((secondOrderThickeningObject S A).thickening.target.scheme, ⊤)) :
    r • t = ambientRingSection (secondOrderThickeningObject S A)
      (siteRingSection A r • siteRingSection (secondOrderThickeningObject S A) t) :=
  ambientRingSection_smul A (siteRingSection A r)
    (siteRingSection (secondOrderThickeningObject S A) t)

/-- The bilinear datum of
`Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineCross`. -/
def affineCrossAux :
    crysSheafRing S (secondOrderThickeningObject S A) →+
      (M.val.obj (op A) →+
        Γ((secondOrderThickeningObject S A).thickening.target.scheme, ⊤) ⊗[
          Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeModules M A, ⊤)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun s ↦ ambientRingSection (secondOrderThickeningObject S A) t ⊗ₜ[
        Γ(A.thickening.target.scheme, ⊤)]
        ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s))
      (fun s s' ↦ (congrArg
          (fun y ↦ ambientRingSection (secondOrderThickeningObject S A) t ⊗ₜ[
            Γ(A.thickening.target.scheme, ⊤)] ambientModuleSection M A y)
          (map_add (moduleSiteRestrict M (A.restrictOpenHom ⊤)) s s')).trans
        (TensorProduct.tmul_add _ _ _)))
    (fun _ _ ↦ AddMonoidHom.ext fun _ ↦ TensorProduct.add_tmul _ _ _)

/-- `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineCrossAux`, written out. -/
@[simp]
theorem affineCrossAux_apply (t : crysSheafRing S (secondOrderThickeningObject S A))
    (s : M.val.obj (op A)) :
    affineCrossAux M A t s =
      ambientRingSection (secondOrderThickeningObject S A) t ⊗ₜ[
        Γ(A.thickening.target.scheme, ⊤)]
        ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s) := rfl

/-- **The base change of the sections of `F` along `q₀`, carried into the tensor product of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`**: the map
`D'' ⊗_D M ⟶ Γ(T'', 𝒪_{T''}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T)` sending `t ⊗ s` to `t ⊗ q₀^* s`, the two
tensor products being over the two actions of
`Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap`. -/
def affineCross :
    crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) →+
      Γ((secondOrderThickeningObject S A).thickening.target.scheme, ⊤) ⊗[
        Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeModules M A, ⊤) :=
  TensorProduct.liftAddHom (affineCrossAux M A) (fun b t s ↦ by
    rw [affineCrossAux_apply, affineCrossAux_apply, ← ambientRingSection_smul,
      TensorProduct.smul_tmul, ambientModuleSection_smul, map_smulₛₗ])

/-- `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineCross` on a pure tensor. -/
@[simp]
theorem affineCross_tmul (t : crysSheafRing S (secondOrderThickeningObject S A))
    (s : M.val.obj (op A)) :
    affineCross M A (t ⊗ₜ[crysSheafRing S A] s) =
      ambientRingSection (secondOrderThickeningObject S A) t ⊗ₜ[
        Γ(A.thickening.target.scheme, ⊤)]
        ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s) :=
  TensorProduct.liftAddHom_tmul _ _ t s

/-- The bilinear datum of
`Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineCrossInv`. -/
def affineCrossInvAux :
    Γ((secondOrderThickeningObject S A).thickening.target.scheme, ⊤) →+
      (Γ(ambientSchemeModules M A, ⊤) →+
        crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A]
          M.val.obj (op A)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun x ↦ siteRingSection (secondOrderThickeningObject S A) t ⊗ₜ[crysSheafRing S A]
        (restrictOpenTopEquiv M A).symm (siteModuleSection M A x))
      (fun x y ↦ (congrArg
          (fun z ↦ siteRingSection (secondOrderThickeningObject S A) t ⊗ₜ[crysSheafRing S A] z)
          (map_add (restrictOpenTopEquiv M A).symm (siteModuleSection M A x)
            (siteModuleSection M A y))).trans
        (TensorProduct.tmul_add _ _ _)))
    (fun _ _ ↦ AddMonoidHom.ext fun _ ↦ TensorProduct.add_tmul _ _ _)

/-- `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineCrossInvAux`, written out. -/
@[simp]
theorem affineCrossInvAux_apply
    (t : Γ((secondOrderThickeningObject S A).thickening.target.scheme, ⊤))
    (x : Γ(ambientSchemeModules M A, ⊤)) :
    affineCrossInvAux M A t x =
      siteRingSection (secondOrderThickeningObject S A) t ⊗ₜ[crysSheafRing S A]
        (restrictOpenTopEquiv M A).symm (siteModuleSection M A x) := rfl

/-- **The inverse of `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineCross`**, the
map `Γ(T'', 𝒪_{T''}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T) ⟶ D'' ⊗_D M` sending `t ⊗ x` to `t ⊗ (q₀^*)⁻¹ x`. -/
def affineCrossInv :
    Γ((secondOrderThickeningObject S A).thickening.target.scheme, ⊤) ⊗[
        Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeModules M A, ⊤) →+
      crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A]
        M.val.obj (op A) :=
  TensorProduct.liftAddHom (affineCrossInvAux M A) (fun r t x ↦ by
    rw [affineCrossInvAux_apply, affineCrossInvAux_apply, smul_eq_ambientRingSection,
      siteRingSection_ambientRingSection, TensorProduct.smul_tmul,
      restrictOpenTopEquiv_symm_smul])

/-- `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineCrossInv` on a pure
tensor. -/
@[simp]
theorem affineCrossInv_tmul
    (t : Γ((secondOrderThickeningObject S A).thickening.target.scheme, ⊤))
    (x : Γ(ambientSchemeModules M A, ⊤)) :
    affineCrossInv M A (t ⊗ₜ[Γ(A.thickening.target.scheme, ⊤)] x) =
      siteRingSection (secondOrderThickeningObject S A) t ⊗ₜ[crysSheafRing S A]
        (restrictOpenTopEquiv M A).symm (siteModuleSection M A x) :=
  TensorProduct.liftAddHom_tmul _ _ t x

/-- **The two tensor products of the affine computation of the base change agree**, as an additive
equivalence

`D'' ⊗_D M ≅ Γ(T'', 𝒪_{T''}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T)`

between the source of
`Crystalline.GlobalCrystallineSituation.SecondOrderAffine.extensionSectionsMap` and the source of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` at `⊤, ⊤`. -/
def affineCrossEquiv :
    crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) ≃+
      Γ((secondOrderThickeningObject S A).thickening.target.scheme, ⊤) ⊗[
        Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeModules M A, ⊤) where
  toFun := affineCross M A
  invFun := affineCrossInv M A
  map_add' := map_add (affineCross M A)
  left_inv z := by
    induction z using TensorProduct.inductionOn with
    | tmul t s =>
        rw [affineCross_tmul, affineCrossInv_tmul, siteRingSection_ambientRingSection,
          siteModuleSection_ambientModuleSection, ← restrictOpenTopEquiv_apply,
          AddEquiv.symm_apply_apply]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  right_inv w := by
    induction w using TensorProduct.inductionOn with
    | tmul t x =>
        rw [affineCrossInv_tmul, affineCross_tmul,
          moduleSiteRestrict_restrictOpenTopEquiv_symm]
        rfl
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-- **The base change of scalars on a pure tensor**, with `q₀^* s` written through the
restrictions of `s` to the whole of the ambient schemes. -/
theorem extensionSectionsMap_tmul_restrictOpenMapTop
    (t : crysSheafRing S (secondOrderThickeningObject S A)) (s : M.val.obj (op A)) :
    extensionSectionsMap M A (t ⊗ₜ[crysSheafRing S A] s) =
      t • (restrictOpenTopEquiv M (secondOrderThickeningObject S A)).symm
        (moduleSiteRestrict M (restrictOpenMapTop (secondOrderThickeningSiteQ₀ S A))
          (siteModuleSection M A
            (ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s)))) := by
  rw [extensionSectionsMap_tmul, siteModuleSection_ambientModuleSection]
  refine congrArg (fun y ↦ t • y) (Eq.symm ?_)
  rw [AddEquiv.symm_apply_eq, restrictOpenTopEquiv_apply]
  exact moduleSiteRestrict_restrictOpenMapTop M (secondOrderThickeningSiteQ₀ S A) s

/-! ### The chain on an affine object -/

/-- **The ambient scheme of the second-order universal thickening of an affine object is
affine.** -/
theorem isAffine_secondOrderThickeningObject [IsAffine A.thickening.target.scheme] :
    IsAffine (secondOrderThickeningObject S A).thickening.target.scheme :=
  Stacks.Thickenings.isAffine_of_isThickening
    (secondOrderThickeningιT_isThickening A.thickening.target S.S.scheme A.toBase.hom)

/-- The ambient scheme of the second-order universal thickening of an affine object is affine, as
an instance. -/
instance isAffine_target_secondOrderThickeningObject [IsAffine A.thickening.target.scheme] :
    IsAffine (secondOrderThickeningObject S A).thickening.target.scheme :=
  isAffine_secondOrderThickeningObject A

section Affine

variable [IsAffine A.thickening.target.scheme] [(ambientSchemeModules M A).IsQuasicoherent]

/-- The affine base-change comparison of [Stacks, Tag 01I9] at the whole of the two ambient
schemes, which are affine. -/
abbrev affineBaseChangeTopIso :=
  affinePullbackSectionsBaseChangeIso (secondOrderThickeningSiteQ₀ S A).targetHom.hom
    (ambientSchemeModules M A) (isAffineOpen_top _) (isAffineOpen_top _)
    (top_le_preimage_siteQ₀ A)

/-- `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineCross`, with its target named
at the extension of scalars of `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`. -/
def affineCrossModule :
    crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) →+
      ((ModuleCat.extendScalars ((secondOrderThickeningSiteQ₀ S A).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteQ₀ A)).hom).obj
        (ModuleCat.of Γ(A.thickening.target.scheme, ⊤) Γ(ambientSchemeModules M A, ⊤)) :
          Type u) :=
  affineCross M A

omit [IsAffine A.thickening.target.scheme] [(ambientSchemeModules M A).IsQuasicoherent] in
/-- `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineCrossModule` is a
bijection. -/
theorem bijective_affineCrossModule :
    Function.Bijective (SecondOrderAffine.affineCrossModule M A) :=
  (affineCrossEquiv M A).bijective

omit [IsAffine A.thickening.target.scheme] [(ambientSchemeModules M A).IsQuasicoherent] in
/-- `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineCrossModule` on a pure
tensor. -/
theorem affineCrossModule_tmul (t : crysSheafRing S (secondOrderThickeningObject S A))
    (s : M.val.obj (op A)) :
    affineCrossModule M A (t ⊗ₜ[crysSheafRing S A] s) =
      ambientRingSection (secondOrderThickeningObject S A) t ⊗ₜ[
        Γ(A.thickening.target.scheme, ⊤),
        ((secondOrderThickeningSiteQ₀ S A).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteQ₀ A)).hom]
        ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s) :=
  affineCross_tmul M A t s

/-- The base-change comparison at `⊤, ⊤`, as an additive map. -/
def affineBaseChangeTopHom :
    ((ModuleCat.extendScalars ((secondOrderThickeningSiteQ₀ S A).targetHom.hom.appLE ⊤ ⊤
        (top_le_preimage_siteQ₀ A)).hom).obj
      (ModuleCat.of Γ(A.thickening.target.scheme, ⊤) Γ(ambientSchemeModules M A, ⊤)) :
        Type u) →+
      ((ModuleCat.of Γ((secondOrderThickeningObject S A).thickening.target.scheme, ⊤)
        Γ((Scheme.Modules.pullback (secondOrderThickeningSiteQ₀ S A).targetHom.hom).obj
          (ambientSchemeModules M A), ⊤)) : Type u) :=
  (affineBaseChangeTopIso M A).hom.hom.toAddMonoidHom

/-- The base-change comparison, written out. -/
theorem affineBaseChangeTopHom_apply
    (w : ((ModuleCat.extendScalars ((secondOrderThickeningSiteQ₀ S A).targetHom.hom.appLE ⊤ ⊤
        (top_le_preimage_siteQ₀ A)).hom).obj
      (ModuleCat.of Γ(A.thickening.target.scheme, ⊤) Γ(ambientSchemeModules M A, ⊤)) :
        Type u)) :
    affineBaseChangeTopHom M A w = (affineBaseChangeTopIso M A).hom w := rfl

/-- `Crystalline.GlobalCrystallineSituation.ambientPullbackSectionTopAlong`, with its type named
at the codomain of the base-change comparison. -/
def ambientPullbackSectionTopModule (x : Γ(ambientSchemeModules M A, ⊤)) :
    ((ModuleCat.of Γ((secondOrderThickeningObject S A).thickening.target.scheme, ⊤)
      Γ((Scheme.Modules.pullback (secondOrderThickeningSiteQ₀ S A).targetHom.hom).obj
        (ambientSchemeModules M A), ⊤)) : Type u) :=
  ambientPullbackSectionTopAlong M (secondOrderThickeningSiteQ₀ S A) x

omit [IsAffine A.thickening.target.scheme] [(ambientSchemeModules M A).IsQuasicoherent] in
/-- `...GlobalCrystallineSituation.affineChainTailAlong_smul_ambientPullbackSectionTopAlong`,
read at the codomain of the base-change comparison. -/
theorem affineChainTailAlong_smul_ambientPullbackSectionTopModule
    (t : crysSheafRing S (secondOrderThickeningObject S A))
    (x : Γ(ambientSchemeModules M A, ⊤)) :
    affineChainTailAlong M (secondOrderThickeningSiteQ₀ S A)
        (ambientRingSection (secondOrderThickeningObject S A) t •
          ambientPullbackSectionTopModule M A x) =
      t • (restrictOpenTopEquiv M (secondOrderThickeningObject S A)).symm
        (moduleSiteRestrict M (restrictOpenMapTop (secondOrderThickeningSiteQ₀ S A))
          (siteModuleSection M A x)) :=
  affineChainTailAlong_smul_ambientPullbackSectionTopAlong M
    (secondOrderThickeningSiteQ₀ S A) t x

/-- **The base-change comparison is bijective** under quasi-coherence and affineness. -/
theorem bijective_affineBaseChangeTopHom :
    Function.Bijective (SecondOrderAffine.affineBaseChangeTopHom M A) :=
  ConcreteCategory.bijective_of_isIso (affineBaseChangeTopIso M A).hom

/-- **The affine chain, as an additive map `D'' ⊗_D M ⟶ F(U, T'', δ'')`.** -/
def affineExtensionHom :
    crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) →+
      M.val.obj (op (secondOrderThickeningObject S A)) :=
  ((affineChainTailAlong M (secondOrderThickeningSiteQ₀ S A)).comp
    (affineBaseChangeTopHom M A)).comp (affineCrossModule M A)

/-- **The chain is bijective** for a crystal, on an object with affine ambient scheme and with
`F_T` quasi-coherent. -/
theorem bijective_affineExtensionHom (hM : IsSheafCrystal M) :
    Function.Bijective (SecondOrderAffine.affineExtensionHom M A) :=
  ((bijective_affineChainTailAlong M (secondOrderThickeningSiteQ₀ S A) hM).comp
      (bijective_affineBaseChangeTopHom M A)).comp (bijective_affineCrossModule M A)

/-! ### The chain is the base change of scalars -/

/-- The base-change comparison at `⊤, ⊤` carries `1 ⊗ a` to the pullback of `a`. -/
theorem affineBaseChangeTop_one_tmul
    (a : Γ(ambientSchemeModules M A, (⊤ : A.thickening.target.scheme.Opens))) :
    (affinePullbackSectionsBaseChangeIso (secondOrderThickeningSiteQ₀ S A).targetHom.hom
        (ambientSchemeModules M A) (isAffineOpen_top _) (isAffineOpen_top _)
        (top_le_preimage_siteQ₀ A)).hom ((1 : Γ(
        (secondOrderThickeningObject S A).thickening.target.scheme,
        (⊤ : (secondOrderThickeningObject S A).thickening.target.scheme.Opens))) ⊗ₜ[
        Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
        ((secondOrderThickeningSiteQ₀ S A).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteQ₀ A)).hom] a) = ambientPullbackSectionTopModule M A a :=
  affinePullbackSectionsBaseChangeIso_one_tmul (secondOrderThickeningSiteQ₀ S A).targetHom.hom
    (ambientSchemeModules M A) (isAffineOpen_top _) (isAffineOpen_top _)
    (top_le_preimage_siteQ₀ A) a

/-- The base-change comparison at `⊤, ⊤` carries `t ⊗ a` to `t` times the pullback of `a`. -/
theorem affineBaseChangeTop_tmul
    (r : Γ((secondOrderThickeningObject S A).thickening.target.scheme,
      (⊤ : (secondOrderThickeningObject S A).thickening.target.scheme.Opens)))
    (a : Γ(ambientSchemeModules M A, (⊤ : A.thickening.target.scheme.Opens))) :
    (affinePullbackSectionsBaseChangeIso (secondOrderThickeningSiteQ₀ S A).targetHom.hom
        (ambientSchemeModules M A) (isAffineOpen_top _) (isAffineOpen_top _)
        (top_le_preimage_siteQ₀ A)).hom (r ⊗ₜ[
        Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
        ((secondOrderThickeningSiteQ₀ S A).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteQ₀ A)).hom] a) =
      r • ambientPullbackSectionTopModule M A a :=
  (affinePullbackSectionsBaseChangeIso_tmul (secondOrderThickeningSiteQ₀ S A).targetHom.hom
    (ambientSchemeModules M A) (isAffineOpen_top _) (isAffineOpen_top _)
    (top_le_preimage_siteQ₀ A) r a).trans
      (congrArg (fun z ↦ r • z) (affineBaseChangeTop_one_tmul M A a))

/-- `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineBaseChangeTopIso` is the
affine base-change comparison `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` at
`⊤, ⊤`. -/
theorem affineBaseChangeTopIso_eq :
    affineBaseChangeTopIso M A =
      affinePullbackSectionsBaseChangeIso (secondOrderThickeningSiteQ₀ S A).targetHom.hom
        (ambientSchemeModules M A) (isAffineOpen_top _) (isAffineOpen_top _)
        (top_le_preimage_siteQ₀ A) := rfl

/-- `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineBaseChangeTop_tmul`, for
`Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineBaseChangeTopIso`. -/
theorem affineBaseChangeTopIso_hom_tmul
    (r : Γ((secondOrderThickeningObject S A).thickening.target.scheme,
      (⊤ : (secondOrderThickeningObject S A).thickening.target.scheme.Opens)))
    (a : Γ(ambientSchemeModules M A, (⊤ : A.thickening.target.scheme.Opens))) :
    (affineBaseChangeTopIso M A).hom (r ⊗ₜ[
        Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
        ((secondOrderThickeningSiteQ₀ S A).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteQ₀ A)).hom] a) =
      r • ambientPullbackSectionTopModule M A a := by
  rw [affineBaseChangeTopIso_eq]
  exact affineBaseChangeTop_tmul M A r a

/-- **The affine chain as a function**: the composite of
`Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineCrossModule`, the base-change
comparison applied as a morphism of `ModuleCat`, and
`Crystalline.GlobalCrystallineSituation.affineChainTailAlong`. -/
def affineExtensionFun
    (z : crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A]
      M.val.obj (op A)) : M.val.obj (op (secondOrderThickeningObject S A)) :=
  affineChainTailAlong M (secondOrderThickeningSiteQ₀ S A)
    ((affineBaseChangeTopIso M A).hom (affineCrossModule M A z))

/-- `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineExtensionFun` is
`Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineExtensionHom`. -/
theorem affineExtensionFun_eq_affineExtensionHom
    (z : crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A]
      M.val.obj (op A)) :
    affineExtensionFun M A z = affineExtensionHom M A z := rfl

/-- **The chain and the base change of scalars agree on a pure tensor.** -/
theorem affineExtensionFun_tmul (t : crysSheafRing S (secondOrderThickeningObject S A))
    (s : M.val.obj (op A)) :
    affineExtensionFun M A (t ⊗ₜ[crysSheafRing S A] s) =
      extensionSectionsMap M A (t ⊗ₜ[crysSheafRing S A] s) := by
  have hcross : affineExtensionFun M A (t ⊗ₜ[crysSheafRing S A] s) =
      affineChainTailAlong M (secondOrderThickeningSiteQ₀ S A) ((affineBaseChangeTopIso M A).hom
        (ambientRingSection (secondOrderThickeningObject S A) t ⊗ₜ[
          Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
          ((secondOrderThickeningSiteQ₀ S A).targetHom.hom.appLE ⊤ ⊤
            (top_le_preimage_siteQ₀ A)).hom]
          ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s))) :=
    congrArg (fun w ↦ affineChainTailAlong M (secondOrderThickeningSiteQ₀ S A)
      ((affineBaseChangeTopIso M A).hom w)) (affineCrossModule_tmul M A t s)
  have hcomp := congrArg (fun y ↦ affineChainTailAlong M (secondOrderThickeningSiteQ₀ S A) y)
    (affineBaseChangeTopIso_hom_tmul M A
      (ambientRingSection (secondOrderThickeningObject S A) t)
      (ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s)))
  have htail := affineChainTailAlong_smul_ambientPullbackSectionTopModule M A t
    (ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s))
  exact ((hcross.trans hcomp).trans htail).trans
    (extensionSectionsMap_tmul_restrictOpenMapTop M A t s).symm

/-- `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.affineExtensionFun_tmul`, for the
additive map. -/
theorem affineExtensionHom_tmul (t : crysSheafRing S (secondOrderThickeningObject S A))
    (s : M.val.obj (op A)) :
    affineExtensionHom M A (t ⊗ₜ[crysSheafRing S A] s) =
      extensionSectionsMap M A (t ⊗ₜ[crysSheafRing S A] s) :=
  (affineExtensionFun_eq_affineExtensionHom M A (t ⊗ₜ[crysSheafRing S A] s)).symm.trans
    (affineExtensionFun_tmul M A t s)

/-- **The affine chain is the base change of scalars.** -/
theorem extensionSectionsMap_eq_affineExtensionHom :
    (SecondOrderAffine.extensionSectionsMap M A : _ → _) =
      (SecondOrderAffine.affineExtensionHom M A : _ → _) := by
  funext w
  induction w using TensorProduct.inductionOn with
  | tmul t s => exact (affineExtensionHom_tmul M A t s).symm
  | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-- **The base change of the sections of `F` along `q₀ : T'' ⟶ T` is bijective** for a crystal on
an object whose ambient scheme is affine and with `F_T` quasi-coherent. -/
theorem bijective_extensionSectionsMap (hM : IsSheafCrystal M) :
    Function.Bijective (SecondOrderAffine.extensionSectionsMap M A) :=
  extensionSectionsMap_eq_affineExtensionHom M A ▸ bijective_affineExtensionHom M A hM

end Affine

end SecondOrderAffine

end Crystalline.GlobalCrystallineSituation

end

end
