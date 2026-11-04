module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineBaseChangeSmall
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineComparisonAlong
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentOfCrystal

/-!
# The base change of sections of a crystal on `Cris(X/S)` along an arbitrary morphism

Let `ℱ` be a sheaf of `𝒪_{X/S}`-modules on the **small** crystalline site `Cris(X/S)` and let
`k : (U₁, T₁, δ₁) ⟶ (U₀, T₀, δ₀)` be a morphism of `Cris(X/S)`.  The base change of sections
along `k` is the map

`Γ(T₁, 𝒪_{T₁}) ⊗_{Γ(T₀, 𝒪_{T₀})} ℱ(U₀, T₀, δ₀) ⟶ ℱ(U₁, T₁, δ₁)`,  `t ⊗ s ↦ t · k^* s`.

This module proves it bijective for a locally quasi-coherent crystal when the two ambient schemes
are affine.

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crisBaseChangeAlong` — the base change of sections along `k`, as an additive map.
* `bijective_crisBaseChangeAlong` — **it is bijective** for a locally quasi-coherent crystal on
  objects with affine ambient schemes.
* `bijective_crisBaseChangeAlong_of_isQuasicoherentOnSite` — the same for a quasi-coherent
  sheaf on `Cris(X/S)`.
* `exists_sum_eq_crisBaseChangeAlong` — every section over the source of `k` is a finite sum
  `∑ tᵢ · k^* sᵢ`.

## References

* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

/-- **The base change of ambient sections is additive.** -/
theorem ambientBaseChangeTensorFun_map_add {S : GlobalCrystallineSituation.{u}}
    {A A' : Thickening S}
    (g : A' ⟶ A) (NA : SheafOfModules.{u} A.ringRestrictionSheaf)
    (NA' : SheafOfModules.{u} A'.ringRestrictionSheaf)
    (fmap : NA ⟶ (SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g)).obj NA')
    [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
    [(ambientSchemeOf A NA).IsQuasicoherent]
    (z z' : ringAlong g ⊗[Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeOf A NA, ⊤)) :
    ambientBaseChangeTensorFun g NA NA' fmap (z + z') =
      ambientBaseChangeTensorFun g NA NA' fmap z + ambientBaseChangeTensorFun g NA NA' fmap z' := by
  have h : ∀ w, ambientBaseChangeTensorFun g NA NA' fmap w =
      ambientComparisonAbstractTop g NA NA' fmap
        (affineBaseChangeTopHomAbstract g NA (ambientCrossAbstract g NA w)) := fun w ↦ rfl
  have hc : ambientCrossAbstract g NA (z + z') =
      ambientCrossAbstract g NA z + ambientCrossAbstract g NA z' := rfl
  rw [h, h, h, hc, map_add, map_add]

end Crystalline.GlobalCrystallineSituation

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))

/-! ### The restriction of sections to the whole ambient scheme is semilinear -/

/-- **The restriction of a section to the whole of the ambient scheme is semilinear** for the
identification `...ambientRingSection` of the two spellings of the section ring. -/
theorem crisSectionTop_smul (B : CrystallineThickening S) (b : crysSheafRing S B.obj)
    (x : F.val.obj (op B)) :
    crysSectionTop F B (b • x) = ambientRingSection B.obj b • crysSectionTop F B x :=
  F.val.map_smul _ b x

/-- **The inverse of the restriction of sections to the whole of the ambient scheme is
semilinear**, with the scalar in the spelling of the ambient scheme. -/
theorem crisSectionTopEquiv_symm_smul (B : CrystallineThickening S)
    (r : Γ(B.obj.thickening.target.scheme, ⊤))
    (x : Γ(ambientSchemeOf B.obj (moduleRestrictionSheaf F B), ⊤)) :
    siteRingSection B.obj r • (crysSectionTopEquiv F B).symm x =
      (crysSectionTopEquiv F B).symm (r • x) := by
  refine (crysSectionTopEquiv F B).injective ?_
  rw [AddEquiv.apply_symm_apply, crysSectionTopEquiv_apply, crisSectionTop_smul,
    ← crysSectionTopEquiv_apply, AddEquiv.apply_symm_apply]
  rfl

variable {A₀ A₁ : CrystallineThickening S} (k : A₁ ⟶ A₀)

/-! ### The base change of sections along `k` -/

/-- The bilinear datum of `...SmallSite.crisBaseChangeAlong`. -/
def crisBaseChangeAlongAux :
    ringAlong k.hom →+ (F.val.obj (op A₀) →+ F.val.obj (op A₁)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk' (fun s ↦ siteRingAlong k.hom t • crysSiteRestrict F k s)
      (fun s s' ↦ by rw [crysSiteRestrict_add, smul_add]))
    (fun t t' ↦ by
      refine AddMonoidHom.ext fun s ↦ ?_
      change siteRingAlong k.hom (t + t') • crysSiteRestrict F k s =
        siteRingAlong k.hom t • crysSiteRestrict F k s +
          siteRingAlong k.hom t' • crysSiteRestrict F k s
      rw [siteRingAlong_add, add_smul])

/-- `crisBaseChangeAlongAux` written out on elements. -/
@[simp]
theorem crisBaseChangeAlongAux_apply (t : ringAlong k.hom) (s : F.val.obj (op A₀)) :
    crisBaseChangeAlongAux F k t s = siteRingAlong k.hom t • crysSiteRestrict F k s := rfl

/-- **The base change of the sections of `ℱ` along a morphism `k` of `Cris(X/S)`**, the map

`Γ(T₁, 𝒪_{T₁}) ⊗_{Γ(T₀, 𝒪_{T₀})} ℱ(U₀, T₀, δ₀) ⟶ ℱ(U₁, T₁, δ₁)`,  `t ⊗ s ↦ t · k^* s`. -/
def crisBaseChangeAlong :
    ringAlong k.hom ⊗[crysSheafRing S A₀.obj] F.val.obj (op A₀) →+ F.val.obj (op A₁) :=
  TensorProduct.liftAddHom (crisBaseChangeAlongAux F k) (fun b t s ↦ by
    rw [crisBaseChangeAlongAux_apply, crisBaseChangeAlongAux_apply, siteRingAlong_smul,
      crysSiteRestrict_smul, smul_smul, mul_comm])

/-- `crisBaseChangeAlong` on a pure tensor. -/
@[simp]
theorem crisBaseChangeAlong_tmul (t : ringAlong k.hom) (s : F.val.obj (op A₀)) :
    crisBaseChangeAlong F k (t ⊗ₜ s) = siteRingAlong k.hom t • crysSiteRestrict F k s :=
  TensorProduct.liftAddHom_tmul _ _ t s

/-! ### The two tensor products agree -/

/-- The bilinear datum of `...SmallSite.crisBaseChangeCross`. -/
def crisBaseChangeCrossAux :
    ringAlong k.hom →+ (F.val.obj (op A₀) →+
      ringAlong k.hom ⊗[Γ(A₀.obj.thickening.target.scheme, ⊤)]
        Γ(ambientSchemeOf A₀.obj (moduleRestrictionSheaf F A₀), ⊤)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun s ↦ t ⊗ₜ[Γ(A₀.obj.thickening.target.scheme, ⊤)] crysSectionTopHom F A₀ s)
      (fun s s' ↦ by rw [map_add, TensorProduct.tmul_add]))
    (fun t t' ↦ AddMonoidHom.ext fun s ↦ TensorProduct.add_tmul _ _ _)

/-- `crisBaseChangeCrossAux` written out on elements. -/
@[simp]
theorem crisBaseChangeCrossAux_apply (t : ringAlong k.hom) (s : F.val.obj (op A₀)) :
    crisBaseChangeCrossAux F k t s =
      t ⊗ₜ[Γ(A₀.obj.thickening.target.scheme, ⊤)] crysSectionTop F A₀ s := rfl

/-- **The change of spelling of the source of the base change**, `t ⊗ s ↦ t ⊗ s|_{T₀}`, from the
tensor product over the section ring of the site to the one over the section ring of the ambient
scheme. -/
def crisBaseChangeCross :
    ringAlong k.hom ⊗[crysSheafRing S A₀.obj] F.val.obj (op A₀) →+
      ringAlong k.hom ⊗[Γ(A₀.obj.thickening.target.scheme, ⊤)]
        Γ(ambientSchemeOf A₀.obj (moduleRestrictionSheaf F A₀), ⊤) :=
  TensorProduct.liftAddHom (crisBaseChangeCrossAux F k) (fun b t s ↦ by
    rw [crisBaseChangeCrossAux_apply, crisBaseChangeCrossAux_apply,
      ← ambientRingSection_smul_eq_smul, TensorProduct.smul_tmul, crisSectionTop_smul])

/-- `crisBaseChangeCross` on a pure tensor. -/
@[simp]
theorem crisBaseChangeCross_tmul (t : ringAlong k.hom) (s : F.val.obj (op A₀)) :
    crisBaseChangeCross F k (t ⊗ₜ[crysSheafRing S A₀.obj] s) =
      t ⊗ₜ[Γ(A₀.obj.thickening.target.scheme, ⊤)] crysSectionTop F A₀ s :=
  TensorProduct.liftAddHom_tmul _ _ t s

/-- The bilinear datum of `...SmallSite.crisBaseChangeCrossInv`. -/
def crisBaseChangeCrossInvAux :
    ringAlong k.hom →+ (Γ(ambientSchemeOf A₀.obj (moduleRestrictionSheaf F A₀), ⊤) →+
      ringAlong k.hom ⊗[crysSheafRing S A₀.obj] F.val.obj (op A₀)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun x ↦ t ⊗ₜ[crysSheafRing S A₀.obj] (crysSectionTopEquiv F A₀).symm x)
      (fun x y ↦ by rw [map_add, TensorProduct.tmul_add]))
    (fun t t' ↦ AddMonoidHom.ext fun x ↦ TensorProduct.add_tmul _ _ _)

/-- `crisBaseChangeCrossInvAux` written out on elements. -/
@[simp]
theorem crisBaseChangeCrossInvAux_apply (t : ringAlong k.hom)
    (x : Γ(ambientSchemeOf A₀.obj (moduleRestrictionSheaf F A₀), ⊤)) :
    crisBaseChangeCrossInvAux F k t x =
      t ⊗ₜ[crysSheafRing S A₀.obj] (crysSectionTopEquiv F A₀).symm x := rfl

/-- **The inverse of `...SmallSite.crisBaseChangeCross`**, `t ⊗ x ↦ t ⊗ x|_{T₀}⁻¹`. -/
def crisBaseChangeCrossInv :
    ringAlong k.hom ⊗[Γ(A₀.obj.thickening.target.scheme, ⊤)]
        Γ(ambientSchemeOf A₀.obj (moduleRestrictionSheaf F A₀), ⊤) →+
      ringAlong k.hom ⊗[crysSheafRing S A₀.obj] F.val.obj (op A₀) :=
  TensorProduct.liftAddHom (crisBaseChangeCrossInvAux F k) (fun r t x ↦ by
    rw [crisBaseChangeCrossInvAux_apply, crisBaseChangeCrossInvAux_apply,
      ambientSmul_eq_siteSmul, TensorProduct.smul_tmul, crisSectionTopEquiv_symm_smul])

/-- `crisBaseChangeCrossInv` on a pure tensor. -/
@[simp]
theorem crisBaseChangeCrossInv_tmul (t : ringAlong k.hom)
    (x : Γ(ambientSchemeOf A₀.obj (moduleRestrictionSheaf F A₀), ⊤)) :
    crisBaseChangeCrossInv F k (t ⊗ₜ[Γ(A₀.obj.thickening.target.scheme, ⊤)] x) =
      t ⊗ₜ[crysSheafRing S A₀.obj] (crysSectionTopEquiv F A₀).symm x :=
  TensorProduct.liftAddHom_tmul _ _ t x

/-- **The two tensor products of the base change agree**, as an additive equivalence

`Γ(T₁, 𝒪_{T₁}) ⊗_{Γ(T₀, 𝒪_{T₀})} ℱ(U₀, T₀, δ₀) ≅ Γ(T₁, 𝒪_{T₁}) ⊗_{Γ(T₀, 𝒪_{T₀})} Γ(T₀, ℱ_{T₀})`. -/
def crisBaseChangeCrossEquiv :
    ringAlong k.hom ⊗[crysSheafRing S A₀.obj] F.val.obj (op A₀) ≃+
      ringAlong k.hom ⊗[Γ(A₀.obj.thickening.target.scheme, ⊤)]
        Γ(ambientSchemeOf A₀.obj (moduleRestrictionSheaf F A₀), ⊤) where
  toFun := crisBaseChangeCross F k
  invFun := crisBaseChangeCrossInv F k
  map_add' := map_add (crisBaseChangeCross F k)
  left_inv z := by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul t s =>
        rw [crisBaseChangeCross_tmul, crisBaseChangeCrossInv_tmul, ← crysSectionTopEquiv_apply,
          AddEquiv.symm_apply_apply]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  right_inv w := by
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul t x =>
        rw [crisBaseChangeCrossInv_tmul, crisBaseChangeCross_tmul, ← crysSectionTopEquiv_apply,
          AddEquiv.apply_symm_apply]
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-- `crisBaseChangeCrossEquiv` written out on elements. -/
@[simp]
theorem crisBaseChangeCrossEquiv_apply
    (z : ringAlong k.hom ⊗[crysSheafRing S A₀.obj] F.val.obj (op A₀)) :
    crisBaseChangeCrossEquiv F k z = crisBaseChangeCross F k z := rfl

/-! ### The square with the base change of ambient sections -/

/-- **The base change of sections, read on the ambient sections over the whole of `T₁`, is the
base change of ambient sections** after the change of spelling of the source. -/
theorem crisSectionTop_crisBaseChangeAlong
    [IsAffine A₀.obj.thickening.target.scheme] [IsAffine A₁.obj.thickening.target.scheme]
    [(ambientSchemeOf A₀.obj (moduleRestrictionSheaf F A₀)).IsQuasicoherent]
    (z : ringAlong k.hom ⊗[crysSheafRing S A₀.obj] F.val.obj (op A₀)) :
    crysSectionTop F A₁ (crisBaseChangeAlong F k z) =
      ambientBaseChangeTensorFun k.hom (moduleRestrictionSheaf F A₀)
        (moduleRestrictionSheaf F A₁) (moduleFMapSheaf F k) (crisBaseChangeCross F k z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero, ← crysSectionTopHom_apply, map_zero,
        ambientBaseChangeTensorFun_zero]
  | tmul t s =>
      rw [crisBaseChangeAlong_tmul, crisBaseChangeCross_tmul, ambientBaseChangeTensorFun_tmul,
        fmapTopSection_crysSectionTop, crisSectionTop_smul]
      rfl
  | add z z' hz hz' =>
      rw [map_add, ← crysSectionTopHom_apply, map_add, crysSectionTopHom_apply,
        crysSectionTopHom_apply, hz, hz', map_add, ambientBaseChangeTensorFun_map_add]

/-! ### Bijectivity -/

/-- **The base change of sections of a crystal on `Cris(X/S)` along a morphism is bijective**:

`Γ(T₁, 𝒪_{T₁}) ⊗_{Γ(T₀, 𝒪_{T₀})} ℱ(U₀, T₀, δ₀) ≅ ℱ(U₁, T₁, δ₁)`,  `t ⊗ s ↦ t · k^* s`,

for a locally quasi-coherent crystal `ℱ` and a morphism `k` of `Cris(X/S)` whose two ambient
schemes are affine. -/
theorem bijective_crisBaseChangeAlong
    [IsAffine A₀.obj.thickening.target.scheme] [IsAffine A₁.obj.thickening.target.scheme]
    (hF : IsLocallyQuasiCoherent F) (hcrys : IsSheafCrystal F) :
    Function.Bijective (crisBaseChangeAlong F k) := by
  have := isQuasicoherent_ambientSchemeOf F hF A₀
  refine (Function.Bijective.of_comp_iff' (bijective_crysSectionTop F A₁)
    (crisBaseChangeAlong F k)).1 ?_
  rw [show crysSectionTop F A₁ ∘ crisBaseChangeAlong F k = _ from
    funext (crisSectionTop_crisBaseChangeAlong F k)]
  exact (bijective_crysAmbientBaseChange F k hcrys).comp
    (crisBaseChangeCrossEquiv F k).bijective

/-- **The base change of sections of a crystal along a morphism**, as an additive equivalence,
under the hypotheses of `...SmallSite.bijective_crisBaseChangeAlong`. -/
def crisBaseChangeAlongEquiv
    [IsAffine A₀.obj.thickening.target.scheme] [IsAffine A₁.obj.thickening.target.scheme]
    (hF : IsLocallyQuasiCoherent F) (hcrys : IsSheafCrystal F) :
    ringAlong k.hom ⊗[crysSheafRing S A₀.obj] F.val.obj (op A₀) ≃+ F.val.obj (op A₁) :=
  AddEquiv.ofBijective (crisBaseChangeAlong F k) (bijective_crisBaseChangeAlong F k hF hcrys)

/-- `crisBaseChangeAlongEquiv` written out on elements. -/
@[simp]
theorem crisBaseChangeAlongEquiv_apply
    [IsAffine A₀.obj.thickening.target.scheme] [IsAffine A₁.obj.thickening.target.scheme]
    (hF : IsLocallyQuasiCoherent F) (hcrys : IsSheafCrystal F)
    (z : ringAlong k.hom ⊗[crysSheafRing S A₀.obj] F.val.obj (op A₀)) :
    crisBaseChangeAlongEquiv F k hF hcrys z = crisBaseChangeAlong F k z := rfl

/-- **The base change of sections along a morphism `k` is bijective for a quasi-coherent sheaf
on `Cris(X/S)`**, when the two ambient schemes of `k` are affine. -/
theorem bijective_crisBaseChangeAlong_of_isQuasicoherentOnSite
    [IsAffine A₀.obj.thickening.target.scheme] [IsAffine A₁.obj.thickening.target.scheme]
    (hF : F.IsQuasicoherentOnSite) :
    Function.Bijective (crisBaseChangeAlong F k) :=
  bijective_crisBaseChangeAlong F k ((isQuasicoherentOnSite_iff F).1 hF).1
    ((isQuasicoherentOnSite_iff F).1 hF).2

/-- **Every section of a crystal over the source of `k` is a finite sum `∑ tᵢ · k^* sᵢ`** of
sections of `𝒪_{X/S}` over the source times restrictions of sections over the target, under the
hypotheses of `...SmallSite.bijective_crisBaseChangeAlong`. -/
theorem exists_sum_eq_crisBaseChangeAlong
    [IsAffine A₀.obj.thickening.target.scheme] [IsAffine A₁.obj.thickening.target.scheme]
    (hF : IsLocallyQuasiCoherent F) (hcrys : IsSheafCrystal F) (y : F.val.obj (op A₁)) :
    ∃ (n : ℕ) (t : Fin n → crysSheafRing S A₁.obj) (s : Fin n → F.val.obj (op A₀)),
      y = ∑ i, t i • crysSiteRestrict F k (s i) := by
  obtain ⟨z, rfl⟩ := (bijective_crisBaseChangeAlong F k hF hcrys).2 y
  have hz : z ∈ Submodule.span (crysSheafRing S A₀.obj)
      {w : ringAlong k.hom ⊗[crysSheafRing S A₀.obj] F.val.obj (op A₀) |
        ∃ a b, a ⊗ₜ[crysSheafRing S A₀.obj] b = w} := by
    rw [TensorProduct.span_tmul_eq_top]
    exact Submodule.mem_top
  obtain ⟨n, c, w, hw⟩ := Submodule.mem_span_set'.mp hz
  choose a b hab using fun j ↦ (w j).2
  refine ⟨n, fun j ↦ siteRingAlong k.hom (c j • a j), b, ?_⟩
  rw [← hw, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← hab j, TensorProduct.smul_tmul', crisBaseChangeAlong_tmul]

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
