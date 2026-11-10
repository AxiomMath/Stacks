module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.NagataConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.HigherDirectImageExtendScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.RestrictionOfScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ExtensionByZeroCurveCohomology

/-!
# Changing the coefficient ring of a torsion constructible sheaf

Let `Λ` be a Noetherian ring and `F` a constructible sheaf of `Λ`-modules on the small étale site
of a quasi-compact quasi-separated scheme `X` which is torsion. Then `F` is annihilated by a
positive integer `N`
(`Stacks.EtaleCohomology.exists_nsmul_id_eq_zero_of_isBigSiteConstructibleEtaleModule`), so `F`
is the restriction of scalars of a constructible sheaf of `Λ/NΛ`-modules (coextension of scalars,
and Stacks 0GKB for the constructibility), and `Rf_!` commutes with restriction of scalars. This is
the first step of the proof of Stacks 0GKZ: "Say `F` is annihilated by `n > 0`. Then we can replace
`Λ` by `Λ/nΛ` without changing `Rf_! F`."

The statements are made in the standard model of the derived category
(`HasDerivedCategory.standard`), in which `Rf_!` and
`Stacks.EtaleCohomology.LowerShriekConstructibilityInput` are stated.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_of_restrictScalars`: the converse of
  `Stacks.EtaleCohomology.isConstructibleEtaleModule_restrictScalars` along a surjection.
* `Stacks.EtaleCohomology.etaleModuleRestrictCoextendScalarsIso`: a sheaf annihilated by the
  kernel of `Λ ⟶ Λ'` is the restriction of scalars of its coextension of scalars.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_quotient`:
  Stacks 0GL0 for torsion sheaves over a Noetherian ring from the case of a torsion ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

/-! ### Restriction of scalars along a surjection -/

section Surjective

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (hρ : Function.Surjective ρ)

include hρ in
/-- Restriction of scalars along a surjective ring homomorphism is full: a `Λ`-linear map between
`Λ'`-modules is `Λ'`-linear, every element of `Λ'` being the image of an element of `Λ`. -/
theorem moduleCat_restrictScalars_full_of_surjective :
    (ModuleCat.restrictScalars.{u + 1} ρ).Full where
  map_surjective {M N} f := by
    refine ⟨ModuleCat.ofHom
      { toFun := f.hom
        map_add' := f.hom.map_add
        map_smul' := fun s x => ?_ }, rfl⟩
    obtain ⟨a, rfl⟩ := hρ s
    exact f.hom.map_smul a x

include hρ in
/-- The counit `Hom_Λ(Λ', M) ⟶ M`, `g ↦ g 1`, of `res_ρ ⊣ coextension of scalars` is invertible
at a `Λ`-module annihilated by the kernel of a surjection `ρ`. -/
theorem isIso_restrictCoextendScalarsAdj_counit_app (M : ModuleCat.{u + 1} Λ)
    (hM : ∀ a ∈ RingHom.ker ρ, ∀ x : M, a • x = 0) :
    IsIso ((ModuleCat.restrictCoextendScalarsAdj.{u + 1} ρ).counit.app M) := by
  have key : ∀ a b : Λ, ρ a = ρ b → ∀ x : M, a • x = b • x := fun a b h x => by
    rw [← sub_eq_zero, ← sub_smul]
    exact hM _ (by rw [RingHom.mem_ker, map_sub, h, sub_self]) x
  have e1 : ∀ s : Λ', ρ (Function.surjInv hρ s) = s := Function.surjInv_eq hρ
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun g g' h => ?_, fun x => ?_⟩
  · refine ModuleCat.CoextendScalars.ext (LinearMap.ext fun s => ?_)
    obtain ⟨a, rfl⟩ := hρ s
    have hg : ∀ g : (ModuleCat.coextendScalars.{0, 0, u + 1} ρ).obj M,
        ModuleCat.CoextendScalars.equiv ρ M g (ρ a) =
          a • ModuleCat.CoextendScalars.equiv ρ M g (1 : Λ') := fun g => by
      rw [← (ModuleCat.CoextendScalars.equiv ρ M g).map_smul a (1 : Λ')]
      congr 1
      exact (mul_one (ρ a)).symm
    exact (hg g).trans ((congrArg (a • ·) h).trans (hg g').symm)
  · let φ : (ModuleCat.restrictScalars.{0} ρ).obj (ModuleCat.of Λ' Λ') →ₗ[Λ] M :=
      { toFun := fun s => Function.surjInv hρ s • x
        map_add' := fun (s t : Λ') => by
          rw [← add_smul]
          exact key _ _ (by rw [map_add, e1, e1]; exact e1 _) x
        map_smul' := fun (a : Λ) (s : Λ') => by
          rw [RingHom.id_apply, smul_smul]
          exact key _ _ (by rw [map_mul, e1]; exact e1 _) x }
    refine ⟨(ModuleCat.CoextendScalars.equiv ρ M).symm φ, ?_⟩
    change Function.surjInv hρ 1 • x = x
    rw [key _ 1 (by rw [e1, map_one]), one_smul]

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

include hρ in
/-- **A sheaf of `Λ'`-modules is constructible once its restriction of scalars along a surjection
`Λ ⟶ Λ'` of Noetherian rings is.** Restriction of scalars is fully faithful, so the counit of
extension of scalars `Λ' ⊗_Λ res G ⟶ G` is invertible, and extension of scalars preserves
constructibility (Stacks 0GKB). This is the converse of
`Stacks.EtaleCohomology.isConstructibleEtaleModule_restrictScalars`. -/
theorem isConstructibleEtaleModule_of_restrictScalars [IsNoetherianRing Λ] [IsNoetherianRing Λ']
    (B : BigEtaleSite.{u}) (X : B.Scheme) (G : EtaleModules.{u, 0} Λ' X.obj)
    (hG : IsBigSiteConstructibleEtaleModule B X Λ ((etaleModuleRestrictScalars ρ X.obj).obj G)) :
    IsBigSiteConstructibleEtaleModule B X Λ' G := by
  have := moduleCat_restrictScalars_full_of_surjective.{u} ρ hρ
  have h := isConstructibleEtaleModule_etaleModuleExtendScalars B X ρ _ hG
  exact IsBigSiteConstructibleEtaleModule.of_iso B Λ'
    (asIso ((etaleModuleExtendScalarsAdj ρ X.obj).counit.app G)) h

include hρ in
/-- **A sheaf of `Λ`-modules whose sections are annihilated by the kernel of a surjection
`ρ : Λ ⟶ Λ'` is the restriction of scalars of its coextension of scalars**: the counit
`res_ρ (Hom_Λ(Λ', F)) ⟶ F`, `g ↦ g 1`, is invertible, sectionwise. -/
def etaleModuleRestrictCoextendScalarsIso {X : Scheme.{u}} (F : EtaleModules.{u, 0} Λ X)
    (hF : ∀ (V : X.Etaleᵒᵖ), ∀ a ∈ RingHom.ker ρ, ∀ x : F.obj.obj V, a • x = 0) :
    (etaleModuleRestrictScalars ρ X).obj ((etaleModuleCoextendScalars ρ X).obj F) ≅ F :=
  have : ∀ V : X.Etaleᵒᵖ,
      IsIso ((ModuleCat.restrictCoextendScalarsAdj.{u + 1} ρ).counit.app (F.obj.obj V)) :=
    fun V => isIso_restrictCoextendScalarsAdj_counit_app ρ hρ _ (hF V)
  (fullyFaithfulSheafToPresheaf X.smallEtaleTopology _).preimageIso
    (NatIso.ofComponents
      (fun V => @asIso _ _ _ _ ((ModuleCat.restrictCoextendScalarsAdj.{u + 1} ρ).counit.app
        (F.obj.obj V)) (this V))
      (fun g => (ModuleCat.restrictCoextendScalarsAdj.{u + 1} ρ).counit.naturality (F.obj.map g)))

end Surjective

/-! ### Torsion sheaves and integers -/

section Torsion

variable (Λ : Type) [CommRing Λ]

/-- The sections of `n • 𝟙 F` act by `n`. -/
theorem etaleModules_map_nsmul_id_apply {X : Scheme.{u}} (F : EtaleModules.{u, 0} Λ X) (n : ℕ)
    (V : X.Etaleᵒᵖ) (y : F.obj.obj V) :
    ((sheafToPresheaf X.smallEtaleTopology _ ⋙ (evaluation _ _).obj V).map (n • 𝟙 F)).hom y =
      n • y := by
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

/-- A torsion sheaf of `Λ`-modules is, as an abelian sheaf, torsion prime to `1`. -/
theorem isPrimeToCharacteristicTorsion_one_of_isTorsionEtaleModule {X : Scheme.{u}}
    (F : EtaleModules.{u, 0} Λ X) (ht : IsTorsionEtaleModule Λ X F) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology 1
      ((etaleModuleForgetAb.{u, 0} Λ X).obj F) := by
  intro U x
  obtain ⟨R, hR, h⟩ := ht U x
  exact ⟨R, hR, fun V f hf => by
    obtain ⟨n, hn, hx⟩ := h V f hf
    exact ⟨n, hn, Nat.coprime_one_right n, hx⟩⟩

end Torsion

/-! ### `Rf_!` and restriction of scalars -/

section LowerShriek

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

/-- **`Rf_!` commutes with restriction of scalars on sheaves**: for a sheaf `G` of `Λ'`-modules
placed in degree `0`, `H^p(Rf_!(res G)) ≅ res H^p(Rf_! G)`. Both sides are `R^p f̄_*(j_! -)`, and
extension by zero and the higher direct images commute with restriction of scalars. -/
theorem nonempty_homology_derivedLowerShriek_restrictScalars_iso {Λ Λ' : Type} [CommRing Λ]
    [CommRing Λ'] (ρ : Λ →+* Λ') {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (G : EtaleModules.{u, 0} Λ' X) (p : ℕ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleRestrictScalars ρ X).obj G))) ≅
      (etaleModuleRestrictScalars ρ Y).obj ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        ((derivedLowerShriek.{u, 0} f j Λ').obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            G)))) :=
  ⟨(nonempty_rightDerived_iso_homology_derivedLowerShriek_singleFunctor f j Λ _ p).some.symm ≪≫
    ((etaleModuleDirectImage.{u, 0} Λ j.toBase).rightDerived p).mapIso
      ((etaleModuleExtensionByZeroRestrictScalars ρ j.immersion).app G) ≪≫
    ((etaleModuleRightDerivedDirectImageRestrictScalarsNatIso ρ j.toBase p).app
      ((etaleModuleExtensionByZero.{u, 0} Λ' j.immersion).obj G)).symm ≪≫
    (etaleModuleRestrictScalars ρ Y).mapIso
      (nonempty_rightDerived_iso_homology_derivedLowerShriek_singleFunctor f j Λ' G p).some⟩

/-- **Stacks 0GL0 for torsion sheaves over a Noetherian ring, from the case of a torsion ring.**
Let `f : X ⟶ Y` be a morphism of schemes of `B` with `X` quasi-compact and quasi-separated and `j`
a compactification of
`f`. Suppose that for every Noetherian ring `Λ'` with `m = 0` in `Λ'` for some `m > 0`, every
cohomology sheaf of `Rf_! G` is constructible for every constructible sheaf `G` of `Λ'`-modules.
Then for every Noetherian ring `Λ` and every constructible torsion sheaf `F` of `Λ`-modules, every
cohomology sheaf of `Rf_! F` is constructible: `F` is annihilated by some `N > 0`, hence is the
restriction of scalars of a constructible sheaf of `Λ/NΛ`-modules, and `Rf_!` commutes with
restriction of scalars. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_quotient (B : BigEtaleSite.{u})
    {X Y : B.Scheme} [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (f : X.obj ⟶ Y.obj)
    (j : CompactificationOf (Over.mk f))
    (h : ∀ (Λ' : Type) [CommRing Λ'] [IsNoetherianRing Λ'] (m : ℕ), 0 < m → (m : Λ') = 0 →
      ∀ G : EtaleModules.{u, 0} Λ' X.obj, IsBigSiteConstructibleEtaleModule B X Λ' G → ∀ p : ℕ,
        IsBigSiteConstructibleEtaleModule B Y Λ'
          ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
            ((derivedLowerShriek.{u, 0} f j Λ').obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
                G))))
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (F : EtaleModules.{u, 0} Λ X.obj)
    (hF : IsBigSiteConstructibleEtaleModule B X Λ F) (ht : IsTorsionEtaleModule Λ X.obj F) (n : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ n).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          F))) := by
  refine isConstructibleEtaleModule_homology_derivedLowerShriek_of_forall_sheaf B f j Λ
    (fun G hG hGt p => ?_) _ (fun q => ⟨isConstructibleEtaleModule_homology_singleFunctor hF q,
      ?_⟩) n
  · obtain ⟨N, hN, -, hNG⟩ :=
      exists_nsmul_id_eq_zero_of_isBigSiteConstructibleEtaleModule B X Λ 1 G hG
        (isPrimeToCharacteristicTorsion_one_of_isTorsionEtaleModule Λ G hGt)
    let I : Ideal Λ := Ideal.span {(N : Λ)}
    let ρ : Λ →+* Λ ⧸ I := Ideal.Quotient.mk I
    have hρ : Function.Surjective ρ := Ideal.Quotient.mk_surjective
    have hNΛ' : ((N : ℕ) : Λ ⧸ I) = 0 := by
      rw [← map_natCast ρ, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    have hker : ∀ (V : X.obj.Etaleᵒᵖ), ∀ a ∈ RingHom.ker ρ, ∀ x : G.obj.obj V, a • x = 0 := by
      intro V a ha x
      rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      have hx : N • x = 0 := by
        rw [← etaleModules_map_nsmul_id_apply Λ G N V x, hNG, Functor.map_zero]
        rfl
      rw [mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, hx, smul_zero]
    let G' := (etaleModuleCoextendScalars ρ X.obj).obj G
    let ε : (etaleModuleRestrictScalars ρ X.obj).obj G' ≅ G :=
      etaleModuleRestrictCoextendScalarsIso ρ hρ G hker
    have hG' : IsBigSiteConstructibleEtaleModule B X (Λ ⧸ I) G' :=
      isConstructibleEtaleModule_of_restrictScalars ρ hρ B X G'
        (IsBigSiteConstructibleEtaleModule.of_iso B Λ ε.symm hG)
    have h' := isConstructibleEtaleModule_restrictScalars B Y ρ hρ _ (h (Λ ⧸ I) N hN hNΛ' G' hG' p)
    obtain ⟨e⟩ := nonempty_homology_derivedLowerShriek_restrictScalars_iso ρ f j G' p
    exact IsBigSiteConstructibleEtaleModule.of_iso B Λ (e.symm ≪≫
      (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).mapIso
        ((derivedLowerShriek.{u, 0} f j Λ).mapIso
          ((DerivedCategory.Plus.singleFunctor _ 0).mapIso ε))) h'
  · rcases lt_trichotomy q 0 with hq | rfl | hq
    · exact isTorsionEtaleModule_of_isZero Λ X.obj
        (DerivedCategory.Plus.isZero_homology_of_isGE _ 0 q hq)
    · exact IsTorsionEtaleModule.of_iso Λ X.obj
        ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app F).symm ht
    · exact isTorsionEtaleModule_of_isZero Λ X.obj
        (DerivedCategory.Plus.isZero_homology_of_isLE _ 0 q hq)

end LowerShriek

end Stacks.EtaleCohomology

end
