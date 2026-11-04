module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineBaseChangeSmall
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineSubsite
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineComparisonAlong
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentOfCrystal
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local

/-!
# The affine base-change criterion for quasi-coherence on `Cris(X/S)`

Let `ℱ` be a sheaf of `𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)` of a global
crystalline situation.  A morphism `k : A ⟶ B` of `Cris(X/S)` gives the base change of sections

`𝒪(A) ⊗_{𝒪(B)} ℱ(B) ⟶ ℱ(A)`,  `r ⊗ x ↦ r · k^* x`.

When `ℱ` is quasi-coherent and `A`, `B` are affine objects (both schemes of each affine) this
map is bijective.  This file proves the **converse**: if it is bijective along every morphism
between affine objects, then `ℱ` is quasi-coherent.  So quasi-coherence on `Cris(X/S)` is
exactly the bijectivity of the base change of sections between affine objects.

The two halves of [Stacks, Tag 07IT] (2) are obtained separately.

* **Local quasi-coherence.**  For an affine open `U` of the ambient scheme `T` of an object and
  `a ∈ Γ(U, 𝒪_T)`, the base change along the restriction morphism from the restriction to
  `D(a)` to the restriction to `U` says that `Γ(D(a), ℱ_T)` is the base change of `Γ(U, ℱ_T)`
  to `Γ(D(a), 𝒪_T) = Γ(U, 𝒪_T)_a`, that is, its localisation at `a`; and a module on a scheme
  whose sections over the basic opens of the affine opens are such localisations is
  quasi-coherent.
* **The crystal condition.**  It is Zariski-local on the ambient scheme of the source, so it
  reduces to a morphism between affine objects.  There both sides of the comparison map are
  quasi-coherent on an affine scheme, the pullback of a quasi-coherent module being
  quasi-coherent, so the comparison map is an isomorphism as soon as it is bijective on global
  sections; and on global sections it is the base change of sections, read through the affine
  base-change comparison `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.crysBaseChange` — the base change of
  sections along a morphism of `Cris(X/S)`.  The action of `𝒪(B)` on `𝒪(A)` depends on `k`, so
  `𝒪(A)` is read at the synonym `Crystalline.GlobalCrystallineSituation.ringAlong`.

## Main results

* `...SmallSite.isLocallyQuasiCoherent_of_bijective_crysBaseChange` and
  `...SmallSite.isSheafCrystal_of_bijective_crysBaseChange` — the two halves.
* `...SmallSite.isQuasicoherentOnSite_of_bijective_crysBaseChange` — **the criterion.**
* `...SmallSite.bijective_crysBaseChange_of_isQuasicoherentOnSite` — the converse, and
  `...SmallSite.isQuasicoherentOnSite_iff_bijective_crysBaseChange` — the equivalence.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct ChangeOfRings

universe u

noncomputable section

/-! ### Tensor products along a ring isomorphism -/

namespace Stacks.TensorProduct

open _root_.TensorProduct

variable {R₁ R₂ P₁ P₂ M₁ M₂ : Type*} [CommRing R₁] [CommRing R₂]
  [AddCommGroup P₁] [Module R₁ P₁] [AddCommGroup P₂] [Module R₂ P₂]
  [AddCommGroup M₁] [Module R₁ M₁] [AddCommGroup M₂] [Module R₂ M₂]
  (σ : R₁ ≃+* R₂) (ρ : P₁ ≃+ P₂) (τ : M₁ ≃+ M₂)
  (hρ : ∀ (r : R₁) (p : P₁), ρ (r • p) = σ r • ρ p)
  (hτ : ∀ (r : R₁) (m : M₁), τ (r • m) = σ r • τ m)

/-- The bilinear datum of `Stacks.TensorProduct.transport`. -/
def transportAux : P₁ →+ M₁ →+ P₂ ⊗[R₂] M₂ :=
  AddMonoidHom.mk' (fun p ↦ AddMonoidHom.mk' (fun m ↦ ρ p ⊗ₜ τ m) fun m m' ↦ by
      rw [map_add, TensorProduct.tmul_add])
    fun p p' ↦ AddMonoidHom.ext fun m ↦ by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, TensorProduct.add_tmul]

include hρ hτ in
/-- **The tensor product carried along a ring isomorphism and two semilinear additive maps**:
`p ⊗ m ↦ ρ p ⊗ τ m`. -/
def transport : P₁ ⊗[R₁] M₁ →+ P₂ ⊗[R₂] M₂ :=
  TensorProduct.liftAddHom (transportAux ρ τ) fun r p m ↦ by
    show ρ (r • p) ⊗ₜ τ m = ρ p ⊗ₜ τ (r • m)
    rw [hρ, hτ, TensorProduct.smul_tmul]

/-- `Stacks.TensorProduct.transport` on a pure tensor. -/
@[simp]
theorem transport_tmul (p : P₁) (m : M₁) :
    transport σ ρ τ hρ hτ (p ⊗ₜ m) = ρ p ⊗ₜ τ m := rfl

/-- The semilinearity of the inverse of a semilinear additive equivalence. -/
theorem symm_smul_of_smul {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R₁ N₁] [AddCommGroup N₂]
    [Module R₂ N₂] (e : N₁ ≃+ N₂) (he : ∀ (r : R₁) (n : N₁), e (r • n) = σ r • e n)
    (s : R₂) (n : N₂) : e.symm (s • n) = σ.symm s • e.symm n := by
  refine e.injective ?_
  rw [he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/-- **The tensor product carried along a ring isomorphism and two semilinear additive
equivalences**, as an additive equivalence. -/
def transportEquiv : P₁ ⊗[R₁] M₁ ≃+ P₂ ⊗[R₂] M₂ where
  toFun := transport σ ρ τ hρ hτ
  invFun := transport σ.symm ρ.symm τ.symm (symm_smul_of_smul σ ρ hρ)
    (symm_smul_of_smul σ τ hτ)
  map_add' := map_add _
  left_inv z := by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul p m => rw [transport_tmul, transport_tmul, AddEquiv.symm_apply_apply,
        AddEquiv.symm_apply_apply]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  right_inv w := by
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul p m => rw [transport_tmul, transport_tmul, AddEquiv.apply_symm_apply,
        AddEquiv.apply_symm_apply]
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-- `Stacks.TensorProduct.transportEquiv` on a pure tensor. -/
@[simp]
theorem transportEquiv_tmul (p : P₁) (m : M₁) :
    transportEquiv σ ρ τ hρ hτ (p ⊗ₜ m) = ρ p ⊗ₜ τ m := rfl

end Stacks.TensorProduct

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The comparison map over the restricted structure sheaves, from its ambient reading -/

section Abstract

variable {A A' : Thickening S} (g : A' ⟶ A) (NA : SheafOfModules.{u} A.ringRestrictionSheaf)
  (NA' : SheafOfModules.{u} A'.ringRestrictionSheaf)
  (fmap : NA ⟶ (SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g)).obj NA')

/-- **The comparison map over the restricted structure sheaves is an isomorphism as soon as the
comparison map along the morphism of ambient schemes is.**  The converse of
`Crystalline.GlobalCrystallineSituation.isIso_affineComparisonAbstract`: the two differ by the
pullback of the counit of a restriction of scalars along an isomorphism and by the comparison of
two left adjoints of one functor, both isomorphisms. -/
theorem isIso_comparisonAbstract_of_isIso_affineComparisonAbstract
    (hc : IsIso (affineComparisonAbstract g NA NA' fmap)) :
    IsIso (comparisonAbstract g NA NA' fmap) := by
  have hε : IsIso ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (Thickening.ringRestrictionSheafStructureIso A)).counit.app NA) :=
    Stacks.SheafOfModules.isIso_restrictScalarsAdjunctionOfIso_counit_app _ _
  have hPε : IsIso ((SheafOfModules.pullback.{u}
        (Thickening.ringRestrictionSheafFMap g)).map
      ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
        (Thickening.ringRestrictionSheafStructureIso A)).counit.app NA)) :=
    Functor.map_isIso _ _
  have hU : IsIso ((Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g)
      (ambientPullbackAdjunctionAlong g)).hom.app (Thickening.ambientOf A NA)) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) _
  have h : (Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g)
          (ambientPullbackAdjunctionAlong g)).hom.app (Thickening.ambientOf A NA) ≫
        affineComparisonAbstract g NA NA' fmap =
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).map
          ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app NA) ≫
        comparisonAbstract g NA NA' fmap :=
    (Adjunction.leftAdjointUniq_hom_app_homEquiv_symm (crysPullbackAdjunctionAlong g)
        (ambientPullbackAdjunctionAlong g) _).trans
      (crysPullbackAdjunctionAlong_homEquiv_symm_fmap g NA NA' fmap)
  have hcomp : IsIso ((SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).map
          ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app NA) ≫
        comparisonAbstract g NA NA' fmap) := h ▸ IsIso.comp_isIso' hU hc
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hPε hcomp

/-- **The comparison map along the morphism of ambient schemes is an isomorphism as soon as its
ambient reading is.**  The two agree on sections. -/
theorem isIso_affineComparisonAbstract_of_isIso_ambientComparisonAbstract
    (hc : IsIso (ambientComparisonAbstract g NA NA' fmap)) :
    IsIso (affineComparisonAbstract g NA NA' fmap) := by
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app _ fun W ↦ ?_
  have hb := ConcreteCategory.bijective_of_isIso
    ((ambientComparisonAbstract g NA NA' fmap).app W.unop)
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  have hfun : (fun y ↦ (affineComparisonAbstract g NA NA' fmap).val.app W y) =
      fun y ↦ (ambientComparisonAbstract g NA NA' fmap).app W.unop y :=
    funext fun y ↦ (ambientComparisonAbstract_val_app g NA NA' fmap W y).symm
  exact (congrArg Function.Bijective hfun).mpr hb

end Abstract

namespace SmallSite

open CohomologyRestriction

variable (F : SheafOfModules.{u} (structureSheaf S))

/-! ### The base change of sections along a morphism of `Cris(X/S)` -/

/-- **The sections of `ℱ` over the source of a morphism `k` of `Cris(X/S)` as a module over the
synonym `Crystalline.GlobalCrystallineSituation.ringAlong` of the sections of `𝒪_{X/S}` there**:
the action of those sections, unchanged. -/
instance moduleRingAlongSections {A B : CrystallineThickening S} (k : A ⟶ B) :
    Module (ringAlong k.hom) (F.val.obj (op A)) :=
  inferInstanceAs (Module (crysSheafRing S A.obj) (F.val.obj (op A)))

/-- The bilinear datum of `Crystalline.GlobalCrystallineSituation.SmallSite.crysBaseChange`. -/
def crysBaseChangeAux {A B : CrystallineThickening S} (k : A ⟶ B) :
    ringAlong k.hom →+ (F.val.obj (op B) →+ F.val.obj (op A)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk' (fun s ↦ siteRingAlong k.hom t • crysRestrict F k s)
      fun s s' ↦ by rw [map_add, smul_add])
    fun t t' ↦ AddMonoidHom.ext fun s ↦ by
      show siteRingAlong k.hom (t + t') • crysRestrict F k s =
        siteRingAlong k.hom t • crysRestrict F k s + siteRingAlong k.hom t' • crysRestrict F k s
      rw [siteRingAlong_add, add_smul]

/-- `Crystalline.GlobalCrystallineSituation.SmallSite.crysBaseChange` as an additive map. -/
def crysBaseChangeAddHom {A B : CrystallineThickening S} (k : A ⟶ B) :
    ringAlong k.hom ⊗[crysSheafRing S B.obj] F.val.obj (op B) →+ F.val.obj (op A) :=
  TensorProduct.liftAddHom (crysBaseChangeAux F k) fun b t s ↦ by
    show siteRingAlong k.hom (b • t) • crysRestrict F k s =
      siteRingAlong k.hom t • crysRestrict F k (b • s)
    rw [siteRingAlong_smul, show crysRestrict F k (b • s) =
      crysSheafRingMap k.hom b • crysRestrict F k s from crysSiteRestrict_smul F k b s,
      smul_smul, mul_comm]

/-- `Crystalline.GlobalCrystallineSituation.SmallSite.crysBaseChangeAddHom` on a pure tensor. -/
theorem crysBaseChangeAddHom_tmul {A B : CrystallineThickening S} (k : A ⟶ B)
    (t : ringAlong k.hom) (s : F.val.obj (op B)) :
    crysBaseChangeAddHom F k (t ⊗ₜ s) = siteRingAlong k.hom t • crysRestrict F k s := rfl

/-- **The base change of the sections of a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` along a
morphism `k : A ⟶ B` of the site**:

`𝒪(A) ⊗_{𝒪(B)} ℱ(B) ⟶ ℱ(A)`,  `r ⊗ x ↦ r · k^* x`,

linear over the sections `𝒪(A)` of `𝒪_{X/S}` over `A`.  The scalar action of `𝒪(B)` on `𝒪(A)`
is that of the restriction map of `𝒪_{X/S}` along `k`, so it is carried by the synonym
`Crystalline.GlobalCrystallineSituation.ringAlong`. -/
def crysBaseChange {A B : CrystallineThickening S} (k : A ⟶ B) :
    ringAlong k.hom ⊗[crysSheafRing S B.obj] F.val.obj (op B) →ₗ[ringAlong k.hom]
      F.val.obj (op A) where
  toFun := crysBaseChangeAddHom F k
  map_add' := map_add _
  map_smul' c z := by
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul t s =>
        rw [TensorProduct.smul_tmul', crysBaseChangeAddHom_tmul, crysBaseChangeAddHom_tmul,
          RingHom.id_apply]
        exact mul_smul (siteRingAlong k.hom c) (siteRingAlong k.hom t) (crysRestrict F k s)
    | add z z' hz hz' => rw [smul_add, map_add, map_add, hz, hz', smul_add]

/-- **The base change of sections on a pure tensor**: `r ⊗ x ↦ r · k^* x`. -/
@[simp]
theorem crysBaseChange_tmul {A B : CrystallineThickening S} (k : A ⟶ B)
    (t : ringAlong k.hom) (s : F.val.obj (op B)) :
    crysBaseChange F k (t ⊗ₜ s) = siteRingAlong k.hom t • crysRestrict F k s := rfl

/-! ### The base change of sections and the base change of ambient sections -/

/-- **The restriction of sections to the whole of the ambient scheme is semilinear**: the
scalars of `𝒪_{X/S}` over the object act on the ambient sections as the sections of the
structure sheaf of the ambient scheme they are. -/
theorem crysSectionTop_smul_of_affine (C : CrystallineThickening S) (b : crysSheafRing S C.obj)
    (y : F.val.obj (op C)) :
    crysSectionTop F C (b • y) = ambientRingSection C.obj b • crysSectionTop F C y :=
  crysSiteRestrict_smul F (C.restrictOpenHom (⊤ : C.obj.thickening.target.scheme.Opens)) b y

variable {A B : CrystallineThickening S} (k : A ⟶ B)

/-- **The two tensor products of the base change along `k` agree**:

`𝒪(A) ⊗_{𝒪(B)} ℱ(B) ≅ 𝒪(A) ⊗_{Γ(T, 𝒪_T)} Γ(T, ℱ_T)`,  `t ⊗ s ↦ t ⊗ s|_T`,

the first being the source of `...SmallSite.crysBaseChange` and the second the source of the
base change of ambient sections
`Crystalline.GlobalCrystallineSituation.ambientBaseChangeTensorFun`. The two rings are the same
ring, acting on `𝒪(A)` through the two ring homomorphisms of
`Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap`, which agree pointwise. -/
def crysCrossEquiv :
    ringAlong k.hom ⊗[crysSheafRing S B.obj] F.val.obj (op B) ≃+
      ringAlong k.hom ⊗[Γ(B.obj.thickening.target.scheme, ⊤)]
        Γ(ambientSchemeOf B.obj (moduleRestrictionSheaf F B), ⊤) :=
  Stacks.TensorProduct.transportEquiv
    (RingEquiv.refl _ : crysSheafRing S B.obj ≃+* Γ(B.obj.thickening.target.scheme, ⊤))
    (AddEquiv.refl (ringAlong k.hom))
    (AddEquiv.ofBijective (crysSectionTopHom F B) (bijective_crysSectionTop F B))
    (fun b t ↦ (ambientRingSection_smul_eq_smul k.hom b t).symm)
    (fun b s ↦ crysSectionTop_smul_of_affine F B b s)

/-- `Crystalline.GlobalCrystallineSituation.SmallSite.crysCrossEquiv` on a pure tensor. -/
theorem crysCrossEquiv_tmul (t : ringAlong k.hom) (s : F.val.obj (op B)) :
    crysCrossEquiv F k (t ⊗ₜ s) = t ⊗ₜ crysSectionTop F B s := rfl

section Affine

variable [IsAffine A.obj.thickening.target.scheme] [IsAffine B.obj.thickening.target.scheme]
  [(ambientSchemeOf B.obj (moduleRestrictionSheaf F B)).IsQuasicoherent]

/-- `...SmallSite.crysCrossEquiv`, with its target named at the extension of scalars of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, whose carrier it is. -/
def crysCrossModule :
    ringAlong k.hom ⊗[crysSheafRing S B.obj] F.val.obj (op B) →+
      ((ModuleCat.extendScalars
          (k.hom.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient k.hom)).hom).obj
        (ModuleCat.of Γ(B.obj.thickening.target.scheme, ⊤)
          Γ(ambientSchemeOf B.obj (moduleRestrictionSheaf F B), ⊤)) : Type u) :=
  (crysCrossEquiv F k).toAddMonoidHom

/-- **The affine chain of the base change of sections along `k`**: the change of spelling, the
affine base-change comparison of [Stacks, Tag 01I9], and the comparison map of
[Stacks, Tag 07IQ] on global sections. -/
def crysAmbientChain :
    ringAlong k.hom ⊗[crysSheafRing S B.obj] F.val.obj (op B) →+
      Γ(ambientSchemeOf A.obj (moduleRestrictionSheaf F A), ⊤) :=
  (ambientComparisonAbstractTop k.hom (moduleRestrictionSheaf F B)
      (moduleRestrictionSheaf F A) (moduleFMapSheaf F k)).comp
    ((affineBaseChangeTopHomAbstract k.hom (moduleRestrictionSheaf F B)).comp
      (crysCrossModule F k))

/-- The change of spelling, on a pure tensor, in the spelling of the extension of scalars. -/
theorem crysCrossModule_tmul (t : ringAlong k.hom) (s : F.val.obj (op B)) :
    crysCrossModule F k (t ⊗ₜ s) =
      ambientRingSection A.obj (siteRingAlong k.hom t) ⊗ₜ[
        Γ(B.obj.thickening.target.scheme, ⊤),
        (k.hom.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient k.hom)).hom]
        crysSectionTop F B s :=
  crysCrossEquiv_tmul F k t s

/-- **The affine chain on a pure tensor**: `t ⊗ s ↦ t · (f-map of s|_T)`. -/
theorem crysAmbientChain_tmul (t : ringAlong k.hom) (s : F.val.obj (op B)) :
    crysAmbientChain F k (t ⊗ₜ s) =
      ambientRingSection A.obj (siteRingAlong k.hom t) •
        fmapTopSection k.hom (moduleRestrictionSheaf F B) (moduleRestrictionSheaf F A)
          (moduleFMapSheaf F k) (crysSectionTop F B s) := by
  have hcross : crysAmbientChain F k (t ⊗ₜ s) =
      ambientComparisonAbstractTop k.hom (moduleRestrictionSheaf F B)
        (moduleRestrictionSheaf F A) (moduleFMapSheaf F k)
        ((affineBaseChangeTopIsoAbstract k.hom (moduleRestrictionSheaf F B)).hom
          (ambientRingSection A.obj (siteRingAlong k.hom t) ⊗ₜ[
            Γ(B.obj.thickening.target.scheme, (⊤ : B.obj.thickening.target.scheme.Opens)),
            (k.hom.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient k.hom)).hom]
            crysSectionTop F B s)) :=
    congrArg (fun w ↦ ambientComparisonAbstractTop k.hom (moduleRestrictionSheaf F B)
        (moduleRestrictionSheaf F A) (moduleFMapSheaf F k)
        ((affineBaseChangeTopIsoAbstract k.hom (moduleRestrictionSheaf F B)).hom w))
      (crysCrossModule_tmul F k t s)
  have hcomp := congrArg (fun y ↦ ambientComparisonAbstractTop k.hom
      (moduleRestrictionSheaf F B) (moduleRestrictionSheaf F A) (moduleFMapSheaf F k) y)
    (affineBaseChangeTopIsoAbstract_hom_tmul k.hom (moduleRestrictionSheaf F B)
      (ambientRingSection A.obj (siteRingAlong k.hom t)) (crysSectionTop F B s))
  exact (hcross.trans hcomp).trans
    (ambientComparisonAbstractTop_smul_ambientPullbackSectionTopModuleAbstract k.hom
      (moduleRestrictionSheaf F B) (moduleRestrictionSheaf F A) (moduleFMapSheaf F k)
      (ambientRingSection A.obj (siteRingAlong k.hom t)) (crysSectionTop F B s))

/-- **The affine chain is the base change of sections followed by the restriction to the whole
of the ambient scheme.** -/
theorem crysAmbientChain_apply
    (z : ringAlong k.hom ⊗[crysSheafRing S B.obj] F.val.obj (op B)) :
    crysAmbientChain F k z = crysSectionTopHom F A (crysBaseChange F k z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul t s =>
      rw [crysAmbientChain_tmul, crysBaseChange_tmul, crysSectionTopHom_apply,
        crysSectionTop_smul_of_affine, fmapTopSection_crysSectionTop]
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']

/-- **The comparison map on global sections is bijective exactly when the base change of sections
is.**  The two differ by the change of spelling, the affine base-change comparison of
[Stacks, Tag 01I9] and the restriction to the whole of the ambient scheme, all bijective. -/
theorem bijective_ambientComparisonAbstractTop_iff :
    Function.Bijective (ambientComparisonAbstractTop k.hom (moduleRestrictionSheaf F B)
        (moduleRestrictionSheaf F A) (moduleFMapSheaf F k)) ↔
      Function.Bijective (crysBaseChange F k) := by
  have hinner : Function.Bijective
      ((affineBaseChangeTopHomAbstract k.hom (moduleRestrictionSheaf F B)) ∘
        (crysCrossModule F k)) :=
    (bijective_affineBaseChangeTopHomAbstract k.hom (moduleRestrictionSheaf F B)).comp
      (crysCrossEquiv F k).bijective
  have h₁ : (crysAmbientChain F k : _ → _) =
      (ambientComparisonAbstractTop k.hom (moduleRestrictionSheaf F B)
        (moduleRestrictionSheaf F A) (moduleFMapSheaf F k)) ∘
      ((affineBaseChangeTopHomAbstract k.hom (moduleRestrictionSheaf F B)) ∘
        (crysCrossModule F k)) := by
    rw [crysAmbientChain, AddMonoidHom.coe_comp, AddMonoidHom.coe_comp]
  have h₂ : (crysAmbientChain F k : _ → _) = crysSectionTopHom F A ∘ crysBaseChange F k :=
    funext fun z ↦ crysAmbientChain_apply F k z
  rw [← Function.Bijective.of_comp_iff _ hinner, ← h₁, h₂]
  exact Function.Bijective.of_comp_iff' (bijective_crysSectionTop F A) _

end Affine

/-- **The crystal condition at a morphism between objects with affine ambient schemes, from the
bijectivity of the base change of sections**, both restrictions `ℱ_T` being quasi-coherent.  On
the affine ambient scheme of the source both sides of the comparison map are quasi-coherent, the
pullback of a quasi-coherent module being quasi-coherent, so the comparison map is an
isomorphism as soon as it is on global sections; and on global sections it is the base change of
sections, read through the affine base-change comparison of [Stacks, Tag 01I9]. -/
theorem isIso_moduleComparisonSheaf_of_bijective_crysBaseChange
    [IsAffine A.obj.thickening.target.scheme] [IsAffine B.obj.thickening.target.scheme]
    (hA : (crysAmbientSchemeModules F A).IsQuasicoherent)
    (hB : (crysAmbientSchemeModules F B).IsQuasicoherent)
    (h : Function.Bijective (crysBaseChange F k)) :
    IsIso (moduleComparisonSheaf F k) := by
  have : (ambientSchemeOf B.obj (moduleRestrictionSheaf F B)).IsQuasicoherent := hB
  have : (ambientSchemeOf A.obj (moduleRestrictionSheaf F A)).IsQuasicoherent := hA
  have := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
    k.hom.targetHom.hom (ambientSchemeOf B.obj (moduleRestrictionSheaf F B))
  have hamb : IsIso (ambientComparisonAbstract k.hom (moduleRestrictionSheaf F B)
      (moduleRestrictionSheaf F A) (moduleFMapSheaf F k)) :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top _
      ((ConcreteCategory.isIso_iff_bijective _).2
        ((bijective_ambientComparisonAbstractTop_iff F k).2 h))
  rw [← comparisonAbstract_moduleFMapSheaf]
  exact isIso_comparisonAbstract_of_isIso_affineComparisonAbstract _ _ _ _
    (isIso_affineComparisonAbstract_of_isIso_ambientComparisonAbstract _ _ _ _ hamb)

/-- The restriction of an object to an affine open of its ambient scheme is an affine object. -/
private theorem isAffineObject_restrictOpen (C : CrystallineThickening S)
    {W : C.obj.thickening.target.scheme.Opens} (hW : IsAffineOpen W) :
    IsAffineObject S (C.restrictOpen W) :=
  have : IsAffine (C.restrictOpen W).obj.thickening.target.scheme := hW
  isAffineObject_of_isAffine S _

/-! ### Local quasi-coherence from the base change of sections -/

section LocallyQuasiCoherent

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange Stacks.AlgebraicGeometry.TorsionQuasicoherent

variable (A : CrystallineThickening S) {U : A.obj.thickening.target.scheme.Opens}

/-- **The sections of `𝒪_{X/S}` over the restriction of an object to an open `W` of its ambient
scheme are the sections of the structure sheaf of that scheme over `W`**, as a ring
isomorphism. -/
def crysSectionsRingEquiv (W : A.obj.thickening.target.scheme.Opens) :
    crysSheafRing S (A.restrictOpen W).obj ≃+* Γ(A.obj.thickening.target.scheme, W) :=
  (CrystallineThickening.sectionsIso A W).ringCatIsoToRingEquiv

/-- The sections of `ℱ_T` over an open `W` are acted on by the sections of the structure sheaf
of `T` through the identification of
`Crystalline.GlobalCrystallineSituation.SmallSite.crysSectionsRingEquiv`. -/
theorem smul_crysAmbientSchemeModules (W : A.obj.thickening.target.scheme.Opens)
    (r : Γ(A.obj.thickening.target.scheme, W)) (x : Γ(crysAmbientSchemeModules F A, W)) :
    r • x = (show F.val.obj (op (A.restrictOpen W)) from
      ((crysSectionsRingEquiv A W).symm r • (show F.val.obj (op (A.restrictOpen W)) from x))) :=
  rfl

/-- **The restriction of the structure sheaf of `𝒪_{X/S}` between two nested opens of an ambient
scheme is the restriction of the structure sheaf of that scheme**, read through
`Crystalline.GlobalCrystallineSituation.SmallSite.crysSectionsRingEquiv`. -/
theorem crysSectionsRingEquiv_restrictOpenLE {D : A.obj.thickening.target.scheme.Opens}
    (hDU : D ≤ U) (b : crysSheafRing S (A.restrictOpen U).obj) :
    crysSectionsRingEquiv A D
        (crysSheafRingMap (CrystallineThickening.restrictOpenLE A hDU).hom b) =
      A.obj.thickening.target.scheme.presheaf.map (homOfLE hDU).op
        (crysSectionsRingEquiv A U b) :=
  congrArg (fun φ ↦ RingCat.Hom.hom φ b) (CrystallineThickening.sectionsIso_restrictOpenLE A hDU)

/-- **The sections of `ℱ_T` over an open `D` are the base change of its sections over a larger
open `U`**, along the restriction map of the structure sheaf of `T`, as soon as the base change of
sections along the restriction morphism between the corresponding objects of `Cris(X/S)` is
bijective. -/
theorem isBaseChange_restrictₗ_of_bijective {D : A.obj.thickening.target.scheme.Opens}
    (hDU : D ≤ U)
    (h : Function.Bijective (crysBaseChange F (CrystallineThickening.restrictOpenLE A hDU))) :
    letI := algebraOfLE A.obj.thickening.target.scheme hDU
    letI := moduleOfLE (crysAmbientSchemeModules F A) hDU
    haveI := isScalarTowerOfLE (crysAmbientSchemeModules F A) hDU
    IsBaseChange Γ(A.obj.thickening.target.scheme, D)
      (restrictₗ (crysAmbientSchemeModules F A) hDU) := by
  let := algebraOfLE A.obj.thickening.target.scheme hDU
  let := moduleOfLE (crysAmbientSchemeModules F A) hDU
  have := isScalarTowerOfLE (crysAmbientSchemeModules F A) hDU
  let k := CrystallineThickening.restrictOpenLE A hDU
  let σ := crysSectionsRingEquiv A U
  let ρ : ringAlong k.hom ≃+ Γ(A.obj.thickening.target.scheme, D) :=
    (crysSectionsRingEquiv A D).toAddEquiv
  let τ : F.val.obj (op (A.restrictOpen U)) ≃+ Γ(crysAmbientSchemeModules F A, U) :=
    AddEquiv.refl _
  have hρ : ∀ (b : crysSheafRing S (A.restrictOpen U).obj) (t : ringAlong k.hom),
      ρ (b • t) = σ b • ρ t := fun b t ↦ by
    show crysSectionsRingEquiv A D (crysSheafRingMap k.hom b * siteRingAlong k.hom t) =
      A.obj.thickening.target.scheme.presheaf.map (homOfLE hDU).op (σ b) *
        crysSectionsRingEquiv A D t
    rw [map_mul, crysSectionsRingEquiv_restrictOpenLE]
    rfl
  have hτ : ∀ (b : crysSheafRing S (A.restrictOpen U).obj)
      (m : F.val.obj (op (A.restrictOpen U))), τ (b • m) = σ b • τ m := fun b m ↦ by
    show b • m = (crysSectionsRingEquiv A U).symm (σ b) • m
    rw [RingEquiv.symm_apply_apply]
  let Ψ := Stacks.TensorProduct.transportEquiv σ ρ τ hρ hτ
  let L := (restrictₗ (crysAmbientSchemeModules F A) hDU).liftBaseChange
    Γ(A.obj.thickening.target.scheme, D)
  have hsq : ∀ z, L (Ψ z) = crysBaseChange F k z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        rw [map_zero, map_zero, map_zero]
        rfl
    | tmul t m =>
        rw [Stacks.TensorProduct.transportEquiv_tmul, LinearMap.liftBaseChange_tmul,
          crysBaseChange_tmul, smul_crysAmbientSchemeModules]
        exact congrArg (· • crysRestrict F k m)
          ((crysSectionsRingEquiv A D).symm_apply_apply (siteRingAlong k.hom t))
    | add z z' hz hz' =>
        rw [map_add, map_add, map_add, hz, hz']
        rfl
  have hbij : Function.Bijective L := by
    have hfun : (crysBaseChange F k : _ → _) ∘ Ψ.symm = L := funext fun w ↦ by
      rw [Function.comp_apply, ← hsq, AddEquiv.apply_symm_apply]
    rw [← hfun]
    exact h.comp Ψ.symm.bijective
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective L hbij) fun x ↦ ?_
  rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul]

variable {A}

/-- **The sections of `ℱ_T` over a basic open of an affine open are the localisation of its
sections over the affine open**, as soon as the base change of sections along the restriction
morphism between the two corresponding objects of `Cris(X/S)` is bijective. -/
theorem isLocalizedModule_restrictₗ_of_bijective (hU : IsAffineOpen U)
    (a : Γ(A.obj.thickening.target.scheme, U))
    (h : Function.Bijective (crysBaseChange F (CrystallineThickening.restrictOpenLE A
      (A.obj.thickening.target.scheme.basicOpen_le a)))) :
    letI := moduleOfLE (crysAmbientSchemeModules F A)
      (A.obj.thickening.target.scheme.basicOpen_le a)
    IsLocalizedModule.Away a (restrictₗ (crysAmbientSchemeModules F A)
      (A.obj.thickening.target.scheme.basicOpen_le a)) := by
  let := moduleOfLE (crysAmbientSchemeModules F A)
    (A.obj.thickening.target.scheme.basicOpen_le a)
  let := hU.isLocalization_basicOpen a
  let := isScalarTowerOfLE (crysAmbientSchemeModules F A)
    (A.obj.thickening.target.scheme.basicOpen_le a)
  exact (isLocalizedModule_iff_isBaseChange (Submonoid.powers a)
    Γ(A.obj.thickening.target.scheme, A.obj.thickening.target.scheme.basicOpen a)
    (restrictₗ (crysAmbientSchemeModules F A)
      (A.obj.thickening.target.scheme.basicOpen_le a))).2
    (isBaseChange_restrictₗ_of_bijective F A _ h)

variable (A) in
/-- **The restriction `ℱ_T` to the ambient scheme of every object is quasi-coherent** as soon as
the base change of sections along every morphism between affine objects of `Cris(X/S)` is
bijective: its sections over the basic opens of an affine open are then localisations of its
sections over that open. -/
theorem isQuasicoherent_crysAmbientSchemeModules_of_bijective
    (h : ∀ {A B : CrystallineThickening S} (k : A ⟶ B), IsAffineObject S A →
      IsAffineObject S B → Function.Bijective (crysBaseChange F k)) :
    (crysAmbientSchemeModules F A).IsQuasicoherent := by
  refine isQuasicoherent_of_isLocalizedModule_restrictₗ (crysAmbientSchemeModules F A)
    fun U hU a ↦ isLocalizedModule_restrictₗ_of_bijective F hU a
      (h _ (isAffineObject_restrictOpen A (hU.basicOpen a)) (isAffineObject_restrictOpen A hU))

/-- **Local quasi-coherence from the base change of sections**: a sheaf of `𝒪_{X/S}`-modules on
`Cris(X/S)` whose base change of sections along every morphism between affine objects is
bijective is locally quasi-coherent. -/
theorem isLocallyQuasiCoherent_of_bijective_crysBaseChange
    (h : ∀ {A B : CrystallineThickening S} (k : A ⟶ B), IsAffineObject S A →
      IsAffineObject S B → Function.Bijective (crysBaseChange F k)) :
    IsLocallyQuasiCoherent F := by
  intro A
  refine ⟨(moduleRestrictionSheaf F A).isSheaf, ?_⟩
  have : (ambientModuleRestriction F A).IsQuasicoherent :=
    isQuasicoherent_crysAmbientSchemeModules_of_bijective F A h
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (@asIso _ _ _ _ ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (Thickening.ringRestrictionSheafStructureIso A.obj)).counit.app
        (moduleRestrictionSheaf F A))
      (Stacks.SheafOfModules.isIso_restrictScalarsAdjunctionOfIso_counit_app
        (Thickening.ringRestrictionSheafStructureIso A.obj) (moduleRestrictionSheaf F A)))
    (Thickening.isQuasicoherentOnSite_ofAmbient A.obj _
      (SheafOfModules.isQuasicoherentOnSite_of_isQuasicoherent (ambientModuleRestriction F A)))

end LocallyQuasiCoherent

/-! ### The criterion -/

/-- **The crystal condition from the base change of sections**: a sheaf of `𝒪_{X/S}`-modules on
`Cris(X/S)` whose base change of sections along every morphism between affine objects is
bijective is a crystal in `𝒪_{X/S}`-modules.  The crystal condition at a morphism is Zariski-local
on the ambient scheme of its source, so it reduces to the morphisms between restrictions to affine
opens, where it is
`...SmallSite.isIso_moduleComparisonSheaf_of_bijective_crysBaseChange`. -/
theorem isSheafCrystal_of_bijective_crysBaseChange
    (h : ∀ {A B : CrystallineThickening S} (k : A ⟶ B), IsAffineObject S A →
      IsAffineObject S B → Function.Bijective (crysBaseChange F k)) :
    IsSheafCrystal F := by
  have hlqc := isLocallyQuasiCoherent_of_bijective_crysBaseChange F h
  intro A B k
  have hV : ∀ y : B.obj.thickening.target.scheme, ∃ V : B.obj.thickening.target.scheme.Opens,
      IsAffineOpen V ∧ y ∈ V := fun y ↦ by
    obtain ⟨V, hVa, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top y)
    exact ⟨V, hVa, hyV⟩
  choose V hVa hyV using hV
  have hW : ∀ x : A.obj.thickening.target.scheme, ∃ W : A.obj.thickening.target.scheme.Opens,
      IsAffineOpen W ∧ x ∈ W ∧ W ≤ k.hom.targetHom.hom ⁻¹ᵁ V (k.hom.targetHom.hom.base x) :=
    fun x ↦ exists_isAffineOpen_mem_and_subset (hyV (k.hom.targetHom.hom.base x))
  choose W hWa hxW hWV using hW
  choose p hp using fun x ↦ CrystallineThickening.exists_comp_restrictOpenHom_eq_of_le k
    (V (k.hom.targetHom.hom.base x)) (W x) (hWV x)
  refine CohomologyRestriction.isIso_moduleComparisonSheaf_of_isOpenCover F k W
    (eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxW x⟩) fun x Z₀ ↦ ?_
  have : IsAffine (A.restrictOpen (W x)).obj.thickening.target.scheme := hWa x
  have : IsAffine
      (B.restrictOpen (V (k.hom.targetHom.hom.base x))).obj.thickening.target.scheme := hVa _
  refine CohomologyRestriction.bijective_fmapComp_pushforward_of_comm F (hp x).symm Z₀ ?_ ?_ ?_
  · exact (CohomologyRestriction.isIso_moduleComparisonSheaf_iff_bijective_fmapComp F _).1
      (CohomologyRestriction.isIso_moduleComparisonSheaf_restrictOpenHom F A _) Z₀
  · exact (CohomologyRestriction.isIso_moduleComparisonSheaf_iff_bijective_fmapComp F _).1
      (isIso_moduleComparisonSheaf_of_bijective_crysBaseChange F (p x)
        (isQuasicoherent_ambientModuleRestriction hlqc _)
        (isQuasicoherent_ambientModuleRestriction hlqc _)
        (h (p x) (isAffineObject_restrictOpen A (hWa x))
          (isAffineObject_restrictOpen B (hVa _)))) Z₀
  · exact (CohomologyRestriction.isIso_moduleComparisonSheaf_iff_bijective_fmapComp F _).1
      (CohomologyRestriction.isIso_moduleComparisonSheaf_restrictOpenHom F B _) _

/-- **A sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` whose base change of sections along every
morphism between affine objects is bijective is quasi-coherent.**  It is locally quasi-coherent
and a crystal, by
`...SmallSite.isLocallyQuasiCoherent_of_bijective_crysBaseChange` and
`...SmallSite.isSheafCrystal_of_bijective_crysBaseChange`,
and such a sheaf is quasi-coherent by [Stacks, Tag 07IT]. -/
theorem isQuasicoherentOnSite_of_bijective_crysBaseChange
    (h : ∀ {A B : CrystallineThickening S} (k : A ⟶ B), IsAffineObject S A →
      IsAffineObject S B → Function.Bijective (crysBaseChange F k)) :
    F.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isLocallyQuasiCoherent
    (isLocallyQuasiCoherent_of_bijective_crysBaseChange F h)
    (isSheafCrystal_of_bijective_crysBaseChange F h)

/-- **The base change of sections of a quasi-coherent sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)`
along a morphism between affine objects is bijective.**  The sheaf is a locally quasi-coherent
crystal by [Stacks, Tag 07IT], so the comparison map is bijective on global sections, and that map
is the base change of sections read through bijections. -/
theorem bijective_crysBaseChange_of_isQuasicoherentOnSite (hF : F.IsQuasicoherentOnSite)
    {A B : CrystallineThickening S} (k : A ⟶ B) (hA : IsAffineObject S A)
    (hB : IsAffineObject S B) : Function.Bijective (crysBaseChange F k) := by
  have := hA.2
  have := hB.2
  have : (ambientSchemeOf B.obj (moduleRestrictionSheaf F B)).IsQuasicoherent :=
    isQuasicoherent_ambientModuleRestriction
      (isLocallyQuasiCoherent_of_isQuasicoherentOnSite F hF) B
  exact (bijective_ambientComparisonAbstractTop_iff F k).1
    (bijective_ambientComparisonAbstractTop k.hom _ _ _
      (isSheafCrystal_of_isQuasicoherentOnSite F hF A B k))

/-- **A sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` is quasi-coherent exactly when its base change
of sections along every morphism between affine objects is bijective.** -/
theorem isQuasicoherentOnSite_iff_bijective_crysBaseChange :
    F.IsQuasicoherentOnSite ↔
      ∀ {A B : CrystallineThickening S} (k : A ⟶ B), IsAffineObject S A →
        IsAffineObject S B → Function.Bijective (crysBaseChange F k) :=
  ⟨fun hF _ _ k hA hB ↦ bijective_crysBaseChange_of_isQuasicoherentOnSite F hF k hA hB,
    isQuasicoherentOnSite_of_bijective_crysBaseChange F⟩

end SmallSite

end Crystalline.GlobalCrystallineSituation

end

end
