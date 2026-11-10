module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CrystalValues
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentOfCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineBaseChangeCriterion

/-!
# The affine base-change criterion for quasi-coherence on `CRIS(X/S)`

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the big crystalline site `CRIS(X/S)` of a global
crystalline situation.  A morphism `g : (U', T', δ') ⟶ (U, T, δ)` gives the base change of
sections `Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} F(U, T, δ) ⟶ F(U', T', δ')`, `t ⊗ s ↦ t · g^* s`
(`Crystalline.GlobalCrystallineSituation.extensionSectionsMapAlong`).  When `F` is quasi-coherent
and the two ambient schemes are affine it is bijective
(`...bijective_extensionSectionsMapAlong_of_isQuasicoherentOnSite`).
This file proves the **converse**: if it is bijective along every morphism between objects with
affine ambient schemes, then `F` is quasi-coherent.  This is the big-site counterpart of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineBaseChangeCriterion.lean`, and the two
halves of [Stacks, Tag 07IT] (2) are obtained the same way.

* **Local quasi-coherence.**  For an affine open `U` of the ambient scheme `T` of an object and
  `a ∈ Γ(U, 𝒪_T)`, the base change along the restriction morphism from the restriction to `D(a)`
  to the restriction to `U` says that `Γ(D(a), F_T)` is the localisation of `Γ(U, F_T)` at `a`,
  and a module on a scheme with this property is quasi-coherent.
* **The crystal condition.**  It is Zariski-local on the ambient scheme of the source, so it
  reduces to a morphism between objects with affine ambient schemes.  There the base change of
  sections is the comparison map `g^* F_T ⟶ F_{T'}` on global sections read through the affine
  base-change comparison (`Crystalline.GlobalCrystallineSituation.affineExtensionHomAlong`), both
  sides of the comparison map are quasi-coherent on an affine scheme, and so the comparison map
  is an isomorphism.

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation`.

* `isIso_moduleComparisonSheaf_of_bijective_extensionSectionsMapAlong` — the crystal condition at
  a morphism between objects with affine ambient schemes.
* `isLocallyQuasiCoherent_of_bijective_extensionSectionsMapAlong` and
  `isSheafCrystal_of_bijective_extensionSectionsMapAlong` — the two halves.
* `isQuasicoherentOnSite_of_bijective_extensionSectionsMapAlong` — **the criterion**, and
  `isQuasicoherentOnSite_iff_bijective_extensionSectionsMapAlong`.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} (M : SheafOfModules.{u} (crystallineStructureSheaf S))

/-! ### The crystal condition at a morphism between objects with affine ambient schemes -/

section Crystal

variable {A A' : Thickening S} (g : A' ⟶ A)

section Affine

variable [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
  [(ambientSchemeModules M A).IsQuasicoherent]

/-- **The tail of the affine chain is bijective as soon as the base change of sections is**: the
other two factors of the chain are bijective. -/
theorem bijective_affineChainTailAlong_of_bijective
    (h : Function.Bijective (extensionSectionsMapAlong M g)) :
    Function.Bijective (affineChainTailAlong M g) := by
  rw [extensionSectionsMapAlong_eq_affineExtensionHomAlong M g] at h
  exact (Function.Bijective.of_comp_iff _ ((bijective_affineBaseChangeTopHomAlong M g).comp
    (bijective_affineCrossModuleAlong M g))).1 h

/-- **The comparison map on global sections is bijective as soon as the base change of sections
is.** -/
theorem bijective_ambientComparisonAlongTop_of_bijective
    (h : Function.Bijective (extensionSectionsMapAlong M g)) :
    Function.Bijective (ambientComparisonAlongTop M g) :=
  (Function.Bijective.of_comp_iff' ((restrictOpenTopEquiv M A').symm.bijective.comp
    (bijective_siteModuleSectionHom M A')) _).1 (bijective_affineChainTailAlong_of_bijective M g h)

/-- **The comparison map `g^* F_T ⟶ F_{T'}` along the morphism of ambient schemes is an
isomorphism as soon as the base change of sections is bijective**, both `F_T` and `F_{T'}` being
quasi-coherent: both sides are quasi-coherent modules on the affine scheme `T'`, so a morphism
between them is an isomorphism once it is bijective on global sections. -/
theorem isIso_ambientComparisonAlong_of_bijective [(ambientSchemeModules M A').IsQuasicoherent]
    (h : Function.Bijective (extensionSectionsMapAlong M g)) :
    IsIso (ambientComparisonAlong M g) := by
  have := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
    g.targetHom.hom (ambientSchemeModules M A)
  exact Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top _
    ((ConcreteCategory.isIso_iff_bijective _).2
      (bijective_ambientComparisonAlongTop_of_bijective M g h))

end Affine

/-- **The comparison map over the restricted structure sheaves is an isomorphism as soon as its
ambient reading is.**  The two agree on sections. -/
theorem isIso_affineComparisonAlong_of_isIso_ambientComparisonAlong
    (h : IsIso (ambientComparisonAlong M g)) : IsIso (affineComparisonAlong M g) := by
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app _ fun W ↦ ?_
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  have hfun : (fun y ↦ (affineComparisonAlong M g).val.app W y) =
      fun y ↦ (ambientComparisonAlong M g).app W.unop y :=
    funext fun y ↦ (ambientComparisonAlong_val_app M g W y).symm
  exact (congrArg Function.Bijective hfun).mpr
    (ConcreteCategory.bijective_of_isIso ((ambientComparisonAlong M g).app W.unop))

/-- **The comparison map `c_g` of [Stacks, Tag 07IQ] is an isomorphism as soon as its reading
along the morphism of ambient schemes is.**  The converse of
`Crystalline.GlobalCrystallineSituation.isIso_affineComparisonAlong`: the two differ by the
pullback of the counit of a restriction of scalars along an isomorphism and by the comparison of
two left adjoints of one functor, both isomorphisms. -/
theorem isIso_moduleComparisonSheaf_of_isIso_affineComparisonAlong
    (h : IsIso (affineComparisonAlong M g)) : IsIso (Thickening.moduleComparisonSheaf M g) := by
  have hPε : IsIso ((SheafOfModules.pullback.{u}
        (Thickening.ringRestrictionSheafFMap g)).map
      ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
        (Thickening.ringRestrictionSheafStructureIso A)).counit.app
        (Thickening.moduleRestrictionSheaf M A))) :=
    have := Stacks.SheafOfModules.isIso_restrictScalarsAdjunctionOfIso_counit_app
      (Thickening.ringRestrictionSheafStructureIso A) (Thickening.moduleRestrictionSheaf M A)
    Functor.map_isIso _ _
  have hU : IsIso ((Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g)
      (ambientPullbackAdjunctionAlong g)).hom.app
      (Thickening.ambientModuleRestriction M A)) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) _
  have hh : (Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g)
          (ambientPullbackAdjunctionAlong g)).hom.app
        (Thickening.ambientModuleRestriction M A) ≫ affineComparisonAlong M g =
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).map
          ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app
            (Thickening.moduleRestrictionSheaf M A)) ≫
        Thickening.moduleComparisonSheaf M g :=
    (Adjunction.leftAdjointUniq_hom_app_homEquiv_symm (crysPullbackAdjunctionAlong g)
        (ambientPullbackAdjunctionAlong g) _).trans
      (crysPullbackAdjunctionAlong_homEquiv_symm_moduleFMapSheaf M g)
  have hcomp := IsIso.comp_isIso' hU h
  rw [hh] at hcomp
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hPε hcomp

/-- **The crystal condition at a morphism between objects with affine ambient schemes, from the
bijectivity of the base change of sections**, both restrictions `F_T` and `F_{T'}` being
quasi-coherent. -/
theorem isIso_moduleComparisonSheaf_of_bijective_extensionSectionsMapAlong
    [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
    (hA : (ambientSchemeModules M A).IsQuasicoherent)
    (hA' : (ambientSchemeModules M A').IsQuasicoherent)
    (h : Function.Bijective (extensionSectionsMapAlong M g)) :
    IsIso (Thickening.moduleComparisonSheaf M g) :=
  isIso_moduleComparisonSheaf_of_isIso_affineComparisonAlong M g
    (isIso_affineComparisonAlong_of_isIso_ambientComparisonAlong M g
      (isIso_ambientComparisonAlong_of_bijective M g h))

end Crystal

/-! ### Local quasi-coherence from the base change of sections -/

section LocallyQuasiCoherent

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange Stacks.AlgebraicGeometry.TorsionQuasicoherent

variable (A : Thickening S) {U : A.thickening.target.scheme.Opens}

/-- **The sections of `𝒪_{X/S}` over the restriction of an object to an open `W` of its ambient
scheme are the sections of the structure sheaf of that scheme over `W`**, as a ring
isomorphism. -/
def restrictOpenSectionsRingEquiv (W : A.thickening.target.scheme.Opens) :
    crysSheafRing S (A.restrictOpen W) ≃+* Γ(A.thickening.target.scheme, W) :=
  (((sheafToPresheaf _ _).mapIso (Thickening.ringRestrictionSheafStructureIso A)).app
    (op W)).ringCatIsoToRingEquiv

/-- The sections of `F_T` over an open `W` are acted on by the sections of the structure sheaf of
`T` through `restrictOpenSectionsRingEquiv`. -/
theorem smul_ambientSchemeModules (W : A.thickening.target.scheme.Opens)
    (r : Γ(A.thickening.target.scheme, W)) (x : Γ(ambientSchemeModules M A, W)) :
    r • x = (show M.val.obj (op (A.restrictOpen W)) from
      ((restrictOpenSectionsRingEquiv A W).symm r •
        (show M.val.obj (op (A.restrictOpen W)) from x))) :=
  rfl

/-- **The restriction of `𝒪_{X/S}` between two nested opens of an ambient scheme is the
restriction of the structure sheaf of that scheme**, read through
`restrictOpenSectionsRingEquiv`. -/
theorem restrictOpenSectionsRingEquiv_restrictOpenLE {D : A.thickening.target.scheme.Opens}
    (hDU : D ≤ U) (b : crysSheafRing S (A.restrictOpen U)) :
    restrictOpenSectionsRingEquiv A D (crysSheafRingMap (A.restrictOpenLE hDU) b) =
      A.thickening.target.scheme.presheaf.map (homOfLE hDU).op
        (restrictOpenSectionsRingEquiv A U b) :=
  congrArg (fun φ ↦ RingCat.Hom.hom φ b)
    ((Thickening.ringRestrictionSheafStructureIso A).hom.hom.naturality (homOfLE hDU).op)

/-- **The sections of `F_T` over an open `D` are the base change of its sections over a larger
open `U`**, along the restriction map of the structure sheaf of `T`, as soon as the base change of
sections along the restriction morphism between the corresponding objects of `CRIS(X/S)` is
bijective. -/
theorem isBaseChange_ambientRestrictₗ_of_bijective {D : A.thickening.target.scheme.Opens}
    (hDU : D ≤ U)
    (h : Function.Bijective (extensionSectionsMapAlong M (A.restrictOpenLE hDU))) :
    letI := algebraOfLE A.thickening.target.scheme hDU
    letI := moduleOfLE (ambientSchemeModules M A) hDU
    haveI := isScalarTowerOfLE (ambientSchemeModules M A) hDU
    IsBaseChange Γ(A.thickening.target.scheme, D)
      (restrictₗ (ambientSchemeModules M A) hDU) := by
  let := algebraOfLE A.thickening.target.scheme hDU
  let := moduleOfLE (ambientSchemeModules M A) hDU
  have := isScalarTowerOfLE (ambientSchemeModules M A) hDU
  let k := A.restrictOpenLE hDU
  let σ := restrictOpenSectionsRingEquiv A U
  let ρ : ringAlong k ≃+ Γ(A.thickening.target.scheme, D) :=
    (restrictOpenSectionsRingEquiv A D).toAddEquiv
  let τ : M.val.obj (op (A.restrictOpen U)) ≃+ Γ(ambientSchemeModules M A, U) :=
    AddEquiv.refl _
  have hρ : ∀ (b : crysSheafRing S (A.restrictOpen U)) (t : ringAlong k),
      ρ (b • t) = σ b • ρ t := fun b t ↦ by
    change restrictOpenSectionsRingEquiv A D (crysSheafRingMap k b * siteRingAlong k t) =
      A.thickening.target.scheme.presheaf.map (homOfLE hDU).op (σ b) *
        restrictOpenSectionsRingEquiv A D t
    rw [map_mul, restrictOpenSectionsRingEquiv_restrictOpenLE]
    rfl
  have hτ : ∀ (b : crysSheafRing S (A.restrictOpen U))
      (m : M.val.obj (op (A.restrictOpen U))), τ (b • m) = σ b • τ m := fun b m ↦ by
    change b • m = (restrictOpenSectionsRingEquiv A U).symm (σ b) • m
    rw [RingEquiv.symm_apply_apply]
  let Ψ := Stacks.TensorProduct.transportEquiv σ ρ τ hρ hτ
  let L := (restrictₗ (ambientSchemeModules M A) hDU).liftBaseChange
    Γ(A.thickening.target.scheme, D)
  have hsq : ∀ z, L (Ψ z) = extensionSectionsMapAlong M k z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul t m =>
        rw [Stacks.TensorProduct.transportEquiv_tmul, LinearMap.liftBaseChange_tmul,
          extensionSectionsMapAlong_tmul, smul_ambientSchemeModules]
        exact congrArg (· • moduleSiteRestrict M k m)
          ((restrictOpenSectionsRingEquiv A D).symm_apply_apply (siteRingAlong k t))
    | add z z' hz hz' =>
        rw [map_add, map_add, map_add, hz, hz']
        rfl
  have hbij : Function.Bijective L := by
    have hfun : (extensionSectionsMapAlong M k : _ → _) ∘ Ψ.symm = L := funext fun w ↦ by
      rw [Function.comp_apply, ← hsq, AddEquiv.apply_symm_apply]
    rw [← hfun]
    exact h.comp Ψ.symm.bijective
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective L hbij) fun x ↦ ?_
  rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul]

variable {A}

/-- **The sections of `F_T` over a basic open of an affine open are the localisation of its
sections over the affine open**, as soon as the base change of sections along the restriction
morphism between the two corresponding objects of `CRIS(X/S)` is bijective. -/
theorem isLocalizedModule_ambientRestrictₗ_of_bijective (hU : IsAffineOpen U)
    (a : Γ(A.thickening.target.scheme, U))
    (h : Function.Bijective (extensionSectionsMapAlong M
      (A.restrictOpenLE (A.thickening.target.scheme.basicOpen_le a)))) :
    letI := moduleOfLE (ambientSchemeModules M A) (A.thickening.target.scheme.basicOpen_le a)
    IsLocalizedModule.Away a (restrictₗ (ambientSchemeModules M A)
      (A.thickening.target.scheme.basicOpen_le a)) := by
  let := moduleOfLE (ambientSchemeModules M A) (A.thickening.target.scheme.basicOpen_le a)
  have := hU.isLocalization_basicOpen a
  have := isScalarTowerOfLE (ambientSchemeModules M A)
    (A.thickening.target.scheme.basicOpen_le a)
  exact (isLocalizedModule_iff_isBaseChange (Submonoid.powers a)
    Γ(A.thickening.target.scheme, A.thickening.target.scheme.basicOpen a)
    (restrictₗ (ambientSchemeModules M A) (A.thickening.target.scheme.basicOpen_le a))).2
    (isBaseChange_ambientRestrictₗ_of_bijective M A _ h)

variable (A) in
/-- **The restriction `F_T` to the ambient scheme of every object is quasi-coherent** as soon as
the base change of sections along every morphism between objects with affine ambient schemes is
bijective: its sections over the basic opens of an affine open are then localisations of its
sections over that open. -/
theorem isQuasicoherent_ambientSchemeModules_of_bijective
    (h : ∀ {A A' : Thickening S} (g : A' ⟶ A), IsAffine A'.thickening.target.scheme →
      IsAffine A.thickening.target.scheme → Function.Bijective (extensionSectionsMapAlong M g)) :
    (ambientSchemeModules M A).IsQuasicoherent :=
  isQuasicoherent_of_isLocalizedModule_restrictₗ (ambientSchemeModules M A)
    fun _ hU a ↦ isLocalizedModule_ambientRestrictₗ_of_bijective M hU a (h _ (hU.basicOpen a) hU)

/-- **Local quasi-coherence from the base change of sections**: a sheaf of `𝒪_{X/S}`-modules on
`CRIS(X/S)` whose base change of sections along every morphism between objects with affine
ambient schemes is bijective is locally quasi-coherent. -/
theorem isLocallyQuasiCoherent_of_bijective_extensionSectionsMapAlong
    (h : ∀ {A A' : Thickening S} (g : A' ⟶ A), IsAffine A'.thickening.target.scheme →
      IsAffine A.thickening.target.scheme → Function.Bijective (extensionSectionsMapAlong M g)) :
    IsLocallyQuasiCoherent M := by
  intro A
  refine ⟨(Thickening.moduleRestrictionSheaf M A).isSheaf, ?_⟩
  have : (Thickening.ambientModuleRestriction M A).IsQuasicoherent :=
    isQuasicoherent_ambientSchemeModules_of_bijective M A h
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (@asIso _ _ _ _ ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (Thickening.ringRestrictionSheafStructureIso A)).counit.app
        (Thickening.moduleRestrictionSheaf M A))
      (Stacks.SheafOfModules.isIso_restrictScalarsAdjunctionOfIso_counit_app
        (Thickening.ringRestrictionSheafStructureIso A) (Thickening.moduleRestrictionSheaf M A)))
    (Thickening.isQuasicoherentOnSite_ofAmbient A _
      (SheafOfModules.isQuasicoherentOnSite_of_isQuasicoherent
        (Thickening.ambientModuleRestriction M A)))

end LocallyQuasiCoherent

/-! ### The criterion -/

/-- **The crystal condition from the base change of sections**: a sheaf of `𝒪_{X/S}`-modules on
`CRIS(X/S)` whose base change of sections along every morphism between objects with affine
ambient schemes is bijective is a crystal in `𝒪_{X/S}`-modules.  The crystal condition at a
morphism is Zariski-local on the ambient scheme of its source, so it reduces to the morphisms
between restrictions to affine opens, where it is
`isIso_moduleComparisonSheaf_of_bijective_extensionSectionsMapAlong`. -/
theorem isSheafCrystal_of_bijective_extensionSectionsMapAlong
    (h : ∀ {A A' : Thickening S} (g : A' ⟶ A), IsAffine A'.thickening.target.scheme →
      IsAffine A.thickening.target.scheme → Function.Bijective (extensionSectionsMapAlong M g)) :
    IsSheafCrystal M := by
  have hlqc := isLocallyQuasiCoherent_of_bijective_extensionSectionsMapAlong M h
  intro A B k
  have hV : ∀ y : B.thickening.target.scheme, ∃ V : B.thickening.target.scheme.Opens,
      IsAffineOpen V ∧ y ∈ V := fun y ↦
    (exists_isAffineOpen_mem_and_subset (Opens.mem_top y)).imp fun _ h ↦ ⟨h.1, h.2.1⟩
  choose V hVa hyV using hV
  have hW : ∀ x : A.thickening.target.scheme, ∃ W : A.thickening.target.scheme.Opens,
      IsAffineOpen W ∧ x ∈ W ∧ W ≤ k.targetHom.hom ⁻¹ᵁ V (k.targetHom.hom.base x) :=
    fun x ↦ exists_isAffineOpen_mem_and_subset (hyV (k.targetHom.hom.base x))
  choose W hWa hxW hWV using hW
  have hp := fun x ↦ Thickening.exists_comp_restrictOpenHom_eq (V (k.targetHom.hom.base x))
    (A.restrictOpenHom (W x) ≫ k) fun y ↦ hWV x y.2
  choose p hp using hp
  refine Thickening.isIso_moduleComparisonSheaf_of_isOpenCover M k W
    (eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxW x⟩) fun x Z₀ ↦ ?_
  have : IsAffine (A.restrictOpen (W x)).thickening.target.scheme := hWa x
  have : IsAffine (B.restrictOpen (V (k.targetHom.hom.base x))).thickening.target.scheme :=
    hVa _
  refine Thickening.bijective_fmapComp_pushforward_of_comm M (hp x).symm Z₀ ?_ ?_ ?_
  · exact (Thickening.isIso_moduleComparisonSheaf_iff_bijective_fmapComp M _).1
      (Thickening.isIso_moduleComparisonSheaf_of_isCartesian M _
        (A.isCartesian_restrictOpenHom _)) Z₀
  · exact (Thickening.isIso_moduleComparisonSheaf_iff_bijective_fmapComp M _).1
      (isIso_moduleComparisonSheaf_of_bijective_extensionSectionsMapAlong M (p x)
        (isQuasicoherent_ambientModuleRestriction hlqc _)
        (isQuasicoherent_ambientModuleRestriction hlqc _)
        (h (p x) inferInstance inferInstance)) Z₀
  · exact (Thickening.isIso_moduleComparisonSheaf_iff_bijective_fmapComp M _).1
      (Thickening.isIso_moduleComparisonSheaf_of_isCartesian M _
        (B.isCartesian_restrictOpenHom _)) _

/-- **A sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` whose base change of sections along every
morphism between objects with affine ambient schemes is bijective is quasi-coherent.**  It is
locally quasi-coherent and a crystal, and such a sheaf is quasi-coherent by
[Stacks, Tag 07IT]. -/
theorem isQuasicoherentOnSite_of_bijective_extensionSectionsMapAlong
    (h : ∀ {A A' : Thickening S} (g : A' ⟶ A), IsAffine A'.thickening.target.scheme →
      IsAffine A.thickening.target.scheme → Function.Bijective (extensionSectionsMapAlong M g)) :
    M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isLocallyQuasiCoherent
    (isLocallyQuasiCoherent_of_bijective_extensionSectionsMapAlong M h)
    (isSheafCrystal_of_bijective_extensionSectionsMapAlong M h)

/-- **A sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` is quasi-coherent exactly when its base change
of sections along every morphism between objects with affine ambient schemes is bijective.** -/
theorem isQuasicoherentOnSite_iff_bijective_extensionSectionsMapAlong :
    M.IsQuasicoherentOnSite ↔
      ∀ {A A' : Thickening S} (g : A' ⟶ A), IsAffine A'.thickening.target.scheme →
        IsAffine A.thickening.target.scheme →
          Function.Bijective (extensionSectionsMapAlong M g) :=
  ⟨fun hM _ _ g _ _ ↦ bijective_extensionSectionsMapAlong_of_isQuasicoherentOnSite M g hM,
    isQuasicoherentOnSite_of_bijective_extensionSectionsMapAlong M⟩

end Crystalline.GlobalCrystallineSituation

end
