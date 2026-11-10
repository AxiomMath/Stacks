module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineBaseChangeSmall
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineComparisonAlong
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineBaseChangeAlong

/-!
# The base change of sections of a crystal on `Cris(X/S)` along an arbitrary morphism

Let `ℱ` be a sheaf of `𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)` and let
`k : (U', T', δ') ⟶ (U, T, δ)` be a morphism of `Cris(X/S)`.  This module writes the base change
of sections

`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} ℱ(U, T, δ) ⟶ ℱ(U', T', δ')`,  `t ⊗ s ↦ t · k^* s`,

and proves it bijective when `ℱ` is a crystal, the two ambient schemes are affine and `ℱ_T` is
quasi-coherent.  The bijectivity is `...SmallSite.bijective_crysAmbientBaseChange`, read from the
ambient sections back to the sections of `ℱ` over the objects.

This is the step "since `ℱ` is a crystal, `Γ(T(1)_e, ℱ) = D(1)_e ⊗_{D_e} Γ(T_e, ℱ)`" of the proof
of [Stacks, Lemma 60.17.3, Tag 07JG].

## Main definitions

* `...SmallSite.crysBaseChangeAlong` — the base change of sections along `k`.

## Main results

* `...SmallSite.crysBaseChangeAlong_tmul` — `t ⊗ s ↦ t · k^* s`.
* `...SmallSite.bijective_crysBaseChangeAlong` — it is bijective for a crystal on affine objects
  with quasi-coherent `ℱ_T`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))
  {A A' : CrystallineThickening S} (k : A' ⟶ A)

/-- **The restriction of a section to the whole ambient scheme is semilinear** over the reading
of the sections of `𝒪_{X/S}` as the global sections of the ambient scheme. -/
theorem crysSectionTopAlong_smul (B : CrystallineThickening S) (b : crysSheafRing S B.obj)
    (s : F.val.obj (op B)) :
    crysSectionTop F B (b • s) = ambientRingSection B.obj b • crysSectionTop F B s := by
  change crysSiteRestrict F (B.restrictOpenHom ⊤) (b • s) = _
  rw [crysSiteRestrict_smul]
  exact (crysAmbientModuleSection_smul F B b _).symm

/-! ### The change of spelling of the two tensor products -/

/-- The bilinear datum of `...SmallSite.crysCrossAlong`. -/
def crysCrossAlongAux :
    ringAlong k.hom →+ (F.val.obj (op A) →+
      ringAlong k.hom ⊗[Γ(A.obj.thickening.target.scheme, ⊤)]
        Γ(ambientSchemeOf A.obj (moduleRestrictionSheaf F A), ⊤)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk' (fun s ↦ t ⊗ₜ crysSectionTop F A s)
      (fun s s' ↦ (congrArg (fun y ↦ t ⊗ₜ[Γ(A.obj.thickening.target.scheme, ⊤)] y)
          (map_add (crysSectionTopHom F A) s s')).trans (TensorProduct.tmul_add _ _ _)))
    (fun t t' ↦ AddMonoidHom.ext fun s ↦ TensorProduct.add_tmul t t' (crysSectionTop F A s))

/-- **The base change of sections along `k`, carried to the tensor product over the ambient
sections**, `t ⊗ s ↦ t ⊗ s|_{T}`. -/
def crysCrossAlong :
    ringAlong k.hom ⊗[crysSheafRing S A.obj] F.val.obj (op A) →+
      ringAlong k.hom ⊗[Γ(A.obj.thickening.target.scheme, ⊤)]
        Γ(ambientSchemeOf A.obj (moduleRestrictionSheaf F A), ⊤) :=
  TensorProduct.liftAddHom (crysCrossAlongAux F k) (fun b t s ↦ by
    change (b • t) ⊗ₜ crysSectionTop F A s = t ⊗ₜ crysSectionTop F A (b • s)
    rw [crysSectionTopAlong_smul, ← ambientRingSection_smul_eq_smul, TensorProduct.smul_tmul])

/-- `...SmallSite.crysCrossAlong` sends `t ⊗ s` to `t ⊗ s|_{T}`. -/
@[simp] theorem crysCrossAlong_tmul (t : ringAlong k.hom) (s : F.val.obj (op A)) :
    crysCrossAlong F k (t ⊗ₜ s) = t ⊗ₜ crysSectionTop F A s :=
  TensorProduct.liftAddHom_tmul _ _ t s

/-- The bilinear datum of `...SmallSite.crysCrossInvAlong`. -/
def crysCrossInvAlongAux :
    ringAlong k.hom →+ (Γ(ambientSchemeOf A.obj (moduleRestrictionSheaf F A), ⊤) →+
      ringAlong k.hom ⊗[crysSheafRing S A.obj] F.val.obj (op A)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk' (fun x ↦ t ⊗ₜ (crysSectionTopEquiv F A).symm x)
      (fun x y ↦ (congrArg (fun z ↦ t ⊗ₜ[crysSheafRing S A.obj] z)
          (map_add (crysSectionTopEquiv F A).symm x y)).trans (TensorProduct.tmul_add _ _ _)))
    (fun t t' ↦ AddMonoidHom.ext fun x ↦
      TensorProduct.add_tmul t t' ((crysSectionTopEquiv F A).symm x))

/-- The inverse of `...SmallSite.crysCrossAlong`. -/
def crysCrossInvAlong :
    ringAlong k.hom ⊗[Γ(A.obj.thickening.target.scheme, ⊤)]
        Γ(ambientSchemeOf A.obj (moduleRestrictionSheaf F A), ⊤) →+
      ringAlong k.hom ⊗[crysSheafRing S A.obj] F.val.obj (op A) :=
  TensorProduct.liftAddHom (crysCrossInvAlongAux F k) (fun r t x ↦ by
    change (r • t) ⊗ₜ (crysSectionTopEquiv F A).symm x =
      t ⊗ₜ (crysSectionTopEquiv F A).symm (r • x)
    have hx : (crysSectionTopEquiv F A).symm (r • x) =
        siteRingSection A.obj r • (crysSectionTopEquiv F A).symm x := by
      rw [AddEquiv.symm_apply_eq, crysSectionTopEquiv_apply, crysSectionTopAlong_smul]
      change r • x = r • crysSectionTopEquiv F A ((crysSectionTopEquiv F A).symm x)
      rw [AddEquiv.apply_symm_apply]
    rw [hx, ambientSmul_eq_siteSmul, TensorProduct.smul_tmul])

/-- `...SmallSite.crysCrossInvAlong` sends `t ⊗ x` to `t ⊗ s`, where `s` is the section of `ℱ`
whose restriction to the whole ambient scheme is `x`. -/
@[simp] theorem crysCrossInvAlong_tmul (t : ringAlong k.hom)
    (x : Γ(ambientSchemeOf A.obj (moduleRestrictionSheaf F A), ⊤)) :
    crysCrossInvAlong F k (t ⊗ₜ x) = t ⊗ₜ (crysSectionTopEquiv F A).symm x :=
  TensorProduct.liftAddHom_tmul _ _ t x

/-- **The two tensor products agree.** -/
def crysCrossEquivAlong :
    ringAlong k.hom ⊗[crysSheafRing S A.obj] F.val.obj (op A) ≃+
      ringAlong k.hom ⊗[Γ(A.obj.thickening.target.scheme, ⊤)]
        Γ(ambientSchemeOf A.obj (moduleRestrictionSheaf F A), ⊤) where
  toFun := crysCrossAlong F k
  invFun := crysCrossInvAlong F k
  map_add' := map_add (crysCrossAlong F k)
  left_inv z := by
    induction z using TensorProduct.inductionOn with
    | tmul t s =>
        rw [crysCrossAlong_tmul, crysCrossInvAlong_tmul, ← crysSectionTopEquiv_apply,
          AddEquiv.symm_apply_apply]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  right_inv w := by
    induction w using TensorProduct.inductionOn with
    | tmul t x =>
        rw [crysCrossInvAlong_tmul, crysCrossAlong_tmul, ← crysSectionTopEquiv_apply,
          AddEquiv.apply_symm_apply]
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-! ### The base change -/

/-- The bilinear datum of `...SmallSite.crysBaseChangeAlong`. -/
def crysBaseChangeAlongAux :
    ringAlong k.hom →+ (F.val.obj (op A) →+ F.val.obj (op A')) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk' (fun s ↦ siteRingAlong k.hom t • crysRestrict F k s)
      (fun s s' ↦ by rw [map_add, smul_add]))
    (fun t t' ↦ AddMonoidHom.ext fun s ↦ add_smul _ _ _)

/-- **The base change of sections of `ℱ` along a morphism `k : T' ⟶ T` of `Cris(X/S)`**,
`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} ℱ(T) ⟶ ℱ(T')`, `t ⊗ s ↦ t · k^* s`. -/
def crysBaseChangeAlong :
    ringAlong k.hom ⊗[crysSheafRing S A.obj] F.val.obj (op A) →+ F.val.obj (op A') :=
  TensorProduct.liftAddHom (crysBaseChangeAlongAux F k) (fun b t s ↦ by
    change siteRingAlong k.hom (b • t) • crysRestrict F k s =
      siteRingAlong k.hom t • crysRestrict F k (b • s)
    rw [siteRingAlong_smul, map_smulₛₗ, mul_smul, smul_comm]
    rfl)

/-- `...SmallSite.crysBaseChangeAlong` sends `t ⊗ s` to `t · k^* s`. -/
@[simp] theorem crysBaseChangeAlong_tmul (t : ringAlong k.hom) (s : F.val.obj (op A)) :
    crysBaseChangeAlong F k (t ⊗ₜ s) = siteRingAlong k.hom t • crysRestrict F k s :=
  TensorProduct.liftAddHom_tmul _ _ t s

/-- `...SmallSite.crysCrossAlong`, with its target named at the extension of scalars of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`. -/
def crysCrossModuleAlong :
    ringAlong k.hom ⊗[crysSheafRing S A.obj] F.val.obj (op A) →+
      ((ModuleCat.extendScalars (k.hom.targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_ambient k.hom)).hom).obj
        (ModuleCat.of Γ(A.obj.thickening.target.scheme, ⊤)
          Γ(ambientSchemeOf A.obj (moduleRestrictionSheaf F A), ⊤)) : Type u) :=
  crysCrossAlong F k

/-- `...SmallSite.crysCrossModuleAlong` is bijective, being `...SmallSite.crysCrossEquivAlong`. -/
theorem bijective_crysCrossModuleAlong : Function.Bijective (crysCrossModuleAlong F k) :=
  (crysCrossEquivAlong F k).bijective

/-- `...SmallSite.crysCrossModuleAlong` on a pure tensor. -/
theorem crysCrossModuleAlong_tmul (t : ringAlong k.hom) (s : F.val.obj (op A)) :
    crysCrossModuleAlong F k (t ⊗ₜ[crysSheafRing S A.obj] s) =
      ambientRingSection A'.obj (siteRingAlong k.hom t) ⊗ₜ[
        Γ(A.obj.thickening.target.scheme, ⊤),
        (k.hom.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient k.hom)).hom]
        crysSectionTop F A s :=
  crysCrossAlong_tmul F k t s

section Affine

variable [IsAffine A.obj.thickening.target.scheme] [IsAffine A'.obj.thickening.target.scheme]
  [(ambientSchemeOf A.obj (moduleRestrictionSheaf F A)).IsQuasicoherent]

/-- **The affine chain along `k`**: the change of spelling, the base-change comparison of
[Stacks, Tag 01I9] and the comparison map of [Stacks, Tag 07IQ] on global sections. -/
def crysAmbientChainAlong :
    ringAlong k.hom ⊗[crysSheafRing S A.obj] F.val.obj (op A) →+
      Γ(ambientSchemeOf A'.obj (moduleRestrictionSheaf F A'), ⊤) :=
  ((ambientComparisonAbstractTop k.hom (moduleRestrictionSheaf F A)
      (moduleRestrictionSheaf F A') (moduleFMapSheaf F k)).comp
    (affineBaseChangeTopHomAbstract k.hom (moduleRestrictionSheaf F A))).comp
      (crysCrossModuleAlong F k)

/-- The affine chain is bijective for a crystal: each of its three factors is. -/
theorem bijective_crysAmbientChainAlong (hF : IsSheafCrystal F) :
    Function.Bijective (crysAmbientChainAlong F k) :=
  ((bijective_ambientComparisonAbstractTop k.hom _ _ _
      (isIso_comparisonAbstract_of_isSheafCrystal F k hF)).comp
    (bijective_affineBaseChangeTopHomAbstract k.hom _)).comp (bijective_crysCrossModuleAlong F k)

/-- The affine chain with its middle factor not bundled. -/
def crysAmbientChainFunAlong (z : ringAlong k.hom ⊗[crysSheafRing S A.obj] F.val.obj (op A)) :
    Γ(ambientSchemeOf A'.obj (moduleRestrictionSheaf F A'), ⊤) :=
  ambientComparisonAbstractTop k.hom (moduleRestrictionSheaf F A)
    (moduleRestrictionSheaf F A') (moduleFMapSheaf F k)
    ((affineBaseChangeTopIsoAbstract k.hom (moduleRestrictionSheaf F A)).hom
      (crysCrossModuleAlong F k z))

/-- `...SmallSite.crysAmbientChainFunAlong` agrees with `...SmallSite.crysAmbientChainAlong`. -/
theorem crysAmbientChainFunAlong_eq
    (z : ringAlong k.hom ⊗[crysSheafRing S A.obj] F.val.obj (op A)) :
    crysAmbientChainFunAlong F k z = crysAmbientChainAlong F k z := rfl

/-- The affine chain on a pure tensor. -/
theorem crysAmbientChainFunAlong_tmul (t : ringAlong k.hom) (s : F.val.obj (op A)) :
    crysAmbientChainFunAlong F k (t ⊗ₜ[crysSheafRing S A.obj] s) =
      ambientRingSection A'.obj (siteRingAlong k.hom t) •
        crysSectionTop F A' (crysRestrict F k s) := by
  have hcross : crysAmbientChainFunAlong F k (t ⊗ₜ[crysSheafRing S A.obj] s) =
      ambientComparisonAbstractTop k.hom (moduleRestrictionSheaf F A)
        (moduleRestrictionSheaf F A') (moduleFMapSheaf F k)
        ((affineBaseChangeTopIsoAbstract k.hom (moduleRestrictionSheaf F A)).hom
          (ambientRingSection A'.obj (siteRingAlong k.hom t) ⊗ₜ[
            Γ(A.obj.thickening.target.scheme, (⊤ : A.obj.thickening.target.scheme.Opens)),
            (k.hom.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient k.hom)).hom]
            crysSectionTop F A s)) :=
    congrArg (fun w ↦ ambientComparisonAbstractTop k.hom (moduleRestrictionSheaf F A)
        (moduleRestrictionSheaf F A') (moduleFMapSheaf F k)
        ((affineBaseChangeTopIsoAbstract k.hom (moduleRestrictionSheaf F A)).hom w))
      (crysCrossModuleAlong_tmul F k t s)
  have hcomp := congrArg (fun y ↦ ambientComparisonAbstractTop k.hom
      (moduleRestrictionSheaf F A) (moduleRestrictionSheaf F A') (moduleFMapSheaf F k) y)
    (affineBaseChangeTopIsoAbstract_hom_tmul k.hom (moduleRestrictionSheaf F A)
      (ambientRingSection A'.obj (siteRingAlong k.hom t)) (crysSectionTop F A s))
  have htail := ambientComparisonAbstractTop_smul_ambientPullbackSectionTopModuleAbstract k.hom
    (moduleRestrictionSheaf F A) (moduleRestrictionSheaf F A') (moduleFMapSheaf F k)
    (ambientRingSection A'.obj (siteRingAlong k.hom t)) (crysSectionTop F A s)
  rw [hcross, hcomp, htail, fmapTopSection_crysSectionTop]

/-- The affine chain on a pure tensor, for the additive map. -/
theorem crysAmbientChainAlong_tmul (t : ringAlong k.hom) (s : F.val.obj (op A)) :
    crysAmbientChainAlong F k (t ⊗ₜ[crysSheafRing S A.obj] s) =
      ambientRingSection A'.obj (siteRingAlong k.hom t) •
        crysSectionTop F A' (crysRestrict F k s) :=
  (crysAmbientChainFunAlong_eq F k _).symm.trans (crysAmbientChainFunAlong_tmul F k t s)

/-- **The base change of sections is the affine chain**, read through the restriction to the
whole ambient scheme. -/
theorem crysSectionTop_crysBaseChangeAlong
    (z : ringAlong k.hom ⊗[crysSheafRing S A.obj] F.val.obj (op A)) :
    crysSectionTopHom F A' (crysBaseChangeAlong F k z) = crysAmbientChainAlong F k z := by
  induction z using TensorProduct.inductionOn with
  | tmul t s =>
      rw [crysBaseChangeAlong_tmul, crysAmbientChainAlong_tmul, crysSectionTopHom_apply,
        crysSectionTopAlong_smul]
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']

/-- **The base change of sections of a crystal along a morphism of `Cris(X/S)` between objects
with affine ambient schemes is bijective**, when `ℱ_T` is quasi-coherent. -/
theorem bijective_crysBaseChangeAlong (hF : IsSheafCrystal F) :
    Function.Bijective (crysBaseChangeAlong F k) := by
  have h : ⇑(crysBaseChangeAlong F k) =
      (crysSectionTopEquiv F A').symm ∘ crysAmbientChainAlong F k := by
    funext z
    rw [Function.comp_apply, AddEquiv.eq_symm_apply, crysSectionTopEquiv_apply]
    exact crysSectionTop_crysBaseChangeAlong F k z
  rw [h]
  exact (crysSectionTopEquiv F A').symm.bijective.comp (bijective_crysAmbientChainAlong F k hF)

end Affine

end Crystalline.GlobalCrystallineSituation.SmallSite

end
