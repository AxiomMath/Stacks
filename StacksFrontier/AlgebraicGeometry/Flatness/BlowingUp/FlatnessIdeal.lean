module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Flat.Nilpotent
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks

/-!
# Shrinking a flatness ideal

Let `A` be a commutative ring, `I ⊆ A` an ideal and `U ⊆ Spec A` a quasi-compact open. For an
`A`-module `M` which is flat modulo `I` and flat on `U`, flatness modulo `I` already holds
modulo the smaller ideal

`I₂ = Ker (I → Γ(U, (I/I²)~))`,

the kernel of the canonical map from `I` to the sections over `U` of the quasi-coherent sheaf
attached to the conormal module `I/I²`. This is the shrinking step used to pass from a
first-order flatness hypothesis to a genuinely smaller one.

The proof is the source's. By the local criterion for a square-zero ideal it suffices to show
that `M ⊗_A I/I₂ → IM/I₂M` is injective; that map is injective over `U` by hypothesis, and
`M ⊗_A I/I₂` injects into its sections over `U` because `M/IM` is a filtered colimit of finite
free `A/I`-modules and `I/I₂` injects into its sections over `U` by the very definition of
`I₂`. Quasi-compactness of `U` turns "sections over `U`" into a finite product of localizations
at the elements of a finite family of basic opens covering `U`.

## Main definitions

* `AlgebraicGeometry.smallerFlatnessIdeal`: the ideal `I₂ = Ker (I → Γ(U, (I/I²)~))` of `A`.

## Main results

* `AlgebraicGeometry.flat_quotient_smallerFlatnessIdeal`: flatness of `M/IM` over `A/I`
  together with flatness of `M` on `U` gives flatness of `M/I₂M` over `A/I₂`.

## Implementation notes

The source states the lemma for a local ring `A`; locality is never used, and the statement is
recorded here for an arbitrary commutative ring. Flatness of `M` on `U` is flatness of the
restriction to `U` of the quasi-coherent sheaf `M~`, in the sense of
`AlgebraicGeometry.SheafOfModules.IsFlat`. The module `I/I²` is Mathlib's `Ideal.Cotangent`.

## References

* [Stacks Project, Tag 0ATC](https://stacks.math.columbia.edu/tag/0ATC)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The ideal `I₂ = Ker (I → Γ(U, (I/I²)~))` of `A`, for an ideal `I` of `A` and an open
`U ⊆ Spec A`: the image in `A` of the kernel of the composite of `I → I/I²` with the map
taking a global conormal class to its sections over `U`. -/
@[stacks 0ATC "the ideal I₂"]
def smallerFlatnessIdeal {A : Type u} [CommRing A]
    (I : Ideal A) (U : (Spec (.of A)).Opens) : Ideal A :=
  (LinearMap.ker
    ((tilde.toOpen (ModuleCat.of A I.Cotangent) U).hom.comp I.toCotangent)).map I.subtype

/-- The map `I → Γ(U, (I/I²)~)` whose kernel defines `smallerFlatnessIdeal`. -/
private def cotangentSectionMap {A : Type u} [CommRing A]
    (I : Ideal A) (U : (Spec (.of A)).Opens) :=
  (tilde.toOpen (ModuleCat.of A I.Cotangent) U).hom.comp I.toCotangent

/-- The ideal `I₂` contains `I²`, so `I/I₂` is a square-zero ideal of `A/I₂`. -/
private lemma smallerFlatnessIdeal_sq_le {A : Type u} [CommRing A]
    (I : Ideal A) (U : (Spec (.of A)).Opens) : I ^ 2 ≤ smallerFlatnessIdeal I U := by
  rw [← I.map_toCotangent_ker]
  exact Submodule.map_mono (LinearMap.ker_le_ker_comp _ _)

/-- Pulling `I₂` back along `I → A` recovers the kernel it was defined as the image of. -/
private lemma cotangentSectionMap_ker_comap {A : Type u} [CommRing A]
    (I : Ideal A) (U : (Spec (.of A)).Opens) :
    Submodule.comap I.subtype (smallerFlatnessIdeal I U : Submodule A A) =
      LinearMap.ker (cotangentSectionMap I U) :=
  Submodule.comap_map_eq_of_injective I.subtype_injective _

/-- If `M` localizes flatly at `S` then an element of `M ⊗ P` killed by an injective map out of
`P` is already killed by the localization map `P → S⁻¹P`. -/
private lemma tensor_localization_eq_zero
    {A M P Q : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (S : Submonoid A) (g : P →ₗ[A] Q) (hg : Function.Injective g)
    (hflat : Module.Flat A (LocalizedModule S M))
    (z : M ⊗[A] P) (hz : g.lTensor M z = 0) :
    (LocalizedModule.mkLinearMap S P).lTensor M z = 0 := by
  let m := LocalizedModule.mkLinearMap S M
  let p := LocalizedModule.mkLinearMap S P
  have hm : (AlgebraTensorModule.rTensor A P m) z = 0 := by
    apply (Module.Flat.lTensor_preserves_injective_linearMap (M := LocalizedModule S M) g hg)
    rw [map_zero]
    have he : (g.lTensor (LocalizedModule S M)).comp (AlgebraTensorModule.rTensor A P m) =
        (AlgebraTensorModule.rTensor A Q m).comp (g.lTensor M) := by
      ext x y
      rfl
    rw [← LinearMap.comp_apply, he, LinearMap.comp_apply, hz, map_zero]
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff S (AlgebraTensorModule.rTensor A P m)).mp hm
  have hc : (AlgebraTensorModule.rTensor A M p) ((TensorProduct.comm A M P) z) = 0 := by
    refine (IsLocalizedModule.eq_zero_iff S (AlgebraTensorModule.rTensor A M p)).mpr ⟨s, ?_⟩
    change (s : A) • z = 0 at hs
    change (s : A) • (TensorProduct.comm A M P) z = 0
    rw [← map_smul, hs, map_zero]
  apply (TensorProduct.comm A M (LocalizedModule S P)).injective
  rw [map_zero]
  have he : (TensorProduct.comm A M (LocalizedModule S P)).toLinearMap.comp (p.lTensor M) =
      (AlgebraTensorModule.rTensor A M p).comp (TensorProduct.comm A M P).toLinearMap := by
    ext x y
    rfl
  exact (LinearMap.congr_fun he z).trans hc

/-- An ideal `I` with `I • ⊤ = ⊥` on a module kills each of its elements. -/
private lemma smul_eq_zero_of_smul_top_eq_bot
    {A P : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    {I : Ideal A} (hP : I • (⊤ : Submodule A P) = ⊥) {a : A} (ha : a ∈ I) (x : P) :
    a • x = 0 := by
  have := Submodule.smul_mem_smul ha (Submodule.mem_top : x ∈ (⊤ : Submodule A P))
  rwa [hP, Submodule.mem_bot] at this

/-- An ideal killing a module kills each of its localizations. -/
private lemma localized_smul_top_eq_bot
    {A P : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    (I : Ideal A) (hP : I • (⊤ : Submodule A P) = ⊥) (S : Submonoid A) :
    I • (⊤ : Submodule A (LocalizedModule S P)) = ⊥ := by
  refine le_antisymm (Submodule.smul_le.mpr fun a ha x _ => ?_) bot_le
  induction x using LocalizedModule.induction_on with | h x s =>
    simp [LocalizedModule.mk, OreLocalization.smul_oreDiv,
      smul_eq_zero_of_smul_top_eq_bot hP ha x]

/-- Tensoring with `M` preserves injectivity of a map out of an `I`-killed module `P`, provided
`M/IM` is flat over `A/I` and `P` embeds into a finite product of localizations of itself at
submonoids over which `M` is flat. -/
private lemma lTensor_injective_of_finite_localizations
    {A M P Q : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (I : Ideal A) (hquot : Module.Flat (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M)))
    (hP : I • (⊤ : Submodule A P) = ⊥)
    {ι : Type*} [Finite ι] (S : ι → Submonoid A)
    (hsep : Function.Injective (LinearMap.pi fun i => LocalizedModule.mkLinearMap (S i) P))
    (hflat : ∀ i, Module.Flat A (LocalizedModule (S i) M))
    (g : P →ₗ[A] Q) (hg : Function.Injective g) : Function.Injective (g.lTensor M) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let L := fun i => LocalizedModule (S i) P
  let f : P →ₗ[A] ∀ i, L i := LinearMap.pi fun i => LocalizedModule.mkLinearMap (S i) P
  have hL : I • (⊤ : Submodule A (∀ i, L i)) = ⊥ := by
    refine le_antisymm (Submodule.smul_le.mpr fun a ha x _ => ?_) bot_le
    rw [Submodule.mem_bot]
    exact funext fun i =>
      smul_eq_zero_of_smul_top_eq_bot (localized_smul_top_eq_bot I hP (S i)) ha (x i)
  have hf : Function.Injective (f.lTensor M) := factB_Jkilled' I hquot hP hL f hsep
  rw [injective_iff_map_eq_zero]
  intro z hz
  apply hf
  rw [map_zero]
  apply (TensorProduct.piRight A A M L).injective
  rw [map_zero]
  ext i
  have he : (LinearMap.proj i).comp
      ((TensorProduct.piRight A A M L).toLinearMap.comp (f.lTensor M)) =
      (LocalizedModule.mkLinearMap (S i) P).lTensor M := by
    ext m p
    rfl
  exact (LinearMap.congr_fun he z).trans
    (tensor_localization_eq_zero (S i) g hg (hflat i) z hz)

/-- Membership in `I₂` is the pointwise vanishing over `U` of the conormal class. -/
private lemma mem_smallerFlatnessIdeal_iff {A : Type u} [CommRing A]
    (I : Ideal A) (U : (Spec (.of A)).Opens) (a : I) :
    (a : A) ∈ smallerFlatnessIdeal I U ↔
      ∀ (p : PrimeSpectrum A) (_hp : p ∈ U),
        LocalizedModule.mkLinearMap p.asIdeal.primeCompl I.Cotangent (I.toCotangent a) = 0 := by
  change a ∈ Submodule.comap I.subtype (smallerFlatnessIdeal I U) ↔ _
  rw [cotangentSectionMap_ker_comap]
  change (StructureSheaf.toOpenₗ A I.Cotangent U) (I.toCotangent a) = 0 ↔ _
  exact ⟨fun h p hp => congrArg (fun s => s.val ⟨p, hp⟩) h,
    fun h => Subtype.ext (funext fun p => h p.val p.property)⟩

/-- The ideal `I/I₂` of `A/I₂` injects into the product of its localizations at a finite family
of elements whose basic opens cover `U`. -/
private lemma quotient_ideal_localizations_injective {A : Type u} [CommRing A]
    (I : Ideal A) (U : (Spec (.of A)).Opens)
    (s : Finset A) (hs : ∀ p ∈ U, ∃ f ∈ s, p ∈ PrimeSpectrum.basicOpen f) :
    let K := smallerFlatnessIdeal I U
    let J := Ideal.map (Ideal.Quotient.mk K) I
    Function.Injective (LinearMap.pi fun f : s =>
      LocalizedModule.mkLinearMap (Submonoid.powers (f : A)) J) := by
  classical
  intro K J
  rw [injective_iff_map_eq_zero]
  intro j hj
  obtain ⟨a, ha, haj⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk K)
    Ideal.Quotient.mk_surjective).mp j.property
  have haK : a ∈ K := by
    refine (mem_smallerFlatnessIdeal_iff I U ⟨a, ha⟩).mpr fun p hp => ?_
    obtain ⟨f, hf, hpf⟩ := hs p hp
    have hjf : LocalizedModule.mkLinearMap (Submonoid.powers f) J j = 0 := congrFun hj ⟨f, hf⟩
    obtain ⟨r, hr⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) J)).mp hjf
    have hra : (r : A) * a ∈ K := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hh := congrArg (fun j : J => (j : A ⧸ K)) hr
      change (r : A) • (j : A ⧸ K) = 0 at hh
      rwa [← haj] at hh
    have hrp : (r : A) ∈ p.asIdeal.primeCompl := Submonoid.powers_le.mpr hpf r.property
    apply IsLocalizedModule.smul_injective
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl I.Cotangent) ⟨r, hrp⟩
    change (r : A) • _ = (r : A) • (0 : LocalizedModule p.asIdeal.primeCompl I.Cotangent)
    simpa only [map_smul, smul_zero] using
      (mem_smallerFlatnessIdeal_iff I U ((r : A) • (⟨a, ha⟩ : I))).mp hra p hp
  exact Subtype.ext (haj.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr haK))

/-- A quasi-compact open of an affine scheme is covered by finitely many basic opens. -/
private lemma finite_basicOpen_cover {A : Type u} [CommRing A]
    (U : (Spec (.of A)).Opens) (hU : IsCompact U.1) :
    ∃ s : Finset A, (∀ p : PrimeSpectrum A, p ∈ U ↔ ∃ f ∈ s, p ∈ PrimeSpectrum.basicOpen f) := by
  classical
  obtain ⟨s, hs⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hU, U.isOpen⟩
  refine ⟨s, fun p => ?_⟩
  change p ∈ U.1 ↔ _
  rw [← hs]
  change p ∉ PrimeSpectrum.zeroLocus (s : Set A) ↔ _
  simp [PrimeSpectrum.mem_zeroLocus, Set.not_subset, PrimeSpectrum.mem_basicOpen]

/-- A flat sheaf of modules on a scheme is flat as a module over the structure sheaf of the
underlying ringed space. -/
private lemma oxModuleFlat_of_isFlat {X : Scheme.{u}} (F : X.Modules)
    (hF : SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F) :
    OXModule.Flat (show OXModule X.toLocallyRingedSpace.toRingedSpace from F) := by
  change ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj
    F).PreservesMonomorphisms
  let _ : Limits.PreservesLimitsOfShape Limits.WalkingCospan
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj F) :=
    hF.1.preservesFiniteLimits Limits.WalkingCospan
  infer_instance

/-- A flat sheaf of modules has flat stalks. -/
private lemma flat_stalk_of_isFlat {X : Scheme.{u}} (F : X.Modules)
    (hF : SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F)
    (x : X.toPresheafedSpace) :
    Module.Flat (X.toLocallyRingedSpace.toRingedSpace.presheaf.stalk x)
      (OXModule.stalk (show OXModule X.toLocallyRingedSpace.toRingedSpace from F) x) :=
  (OXModule.flat_iff_flat_stalk _).mp (oxModuleFlat_of_isFlat F hF) x

/-- Along an open immersion, a flat sheaf of modules on the source is flat over the target:
the stalk maps are isomorphisms. -/
private lemma isFlatOver_of_isFlat_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (F : X.Modules)
    (hF : SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F) :
    IsFlatOver f.toLRSHom.toShHom F := by
  intro x
  have hFx := flat_stalk_of_isFlat F hF x
  let φ := (f.stalkMap x).hom
  let _ := φ.toAlgebra
  have hφ : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (f.stalkMap x))
  let _ : Module (Y.presheaf.stalk (f x)) (OXModule.stalk F x) :=
    Module.compHom _ φ
  have : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) (OXModule.stalk F x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.Flat.trans (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) (OXModule.stalk F x)

/-- If `M~` restricted to `U` is flat over `Spec A`, then its sections over a basic open
contained in `U` form a flat `A`-module. -/
private lemma flat_basicOpen_sections {A : Type u} [CommRing A]
    (M : ModuleCat (.of A : CommRingCat)) (U : (Spec (.of A)).Opens)
    (hF : IsFlatOver U.ι.toLRSHom.toShHom ((tilde M).restrict U.ι))
    (f : A) (hf : PrimeSpectrum.basicOpen f ≤ U) :
    Module.Flat A
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op (PrimeSpectrum.basicOpen f))) := by
  let F := (tilde M).restrict U.ι
  let W := U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f
  have hW : IsAffineOpen W :=
    (IsAffineOpen.Spec_basicOpen (R := .of A) f).preimage_of_isOpenImmersion U.ι
      (by
        convert hf using 1
        simp only [Scheme.Opens.opensRange_ι]
        rfl)
  have hWtop : W ≤ U.ι ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens) := by simp
  have hsections := ((isFlatOver_tfae U.ι F).out 1 2 (by rfl) (by rfl)).mp hF
  have H := hsections W hW ⊤ (isAffineOpen_top (Spec (.of A))) hWtop
  let V := U.ι ''ᵁ W
  have hV : V = PrimeSpectrum.basicOpen f := by
    have h := U.ι.image_preimage_eq_opensRange_inf (PrimeSpectrum.basicOpen f)
    rw [Scheme.Opens.opensRange_ι] at h
    exact h.trans (inf_eq_right.mpr hf)
  let _ : Module Γ(Spec (.of A), ⊤) Γ(F, W) := Module.compHom _ (U.ι.appLE ⊤ W hWtop).hom
  let _ : Module.Flat Γ(Spec (.of A), ⊤) Γ(F, W) := H
  let φ := (Scheme.ΓSpecIso (.of A)).inv.hom
  let _ := φ.toAlgebra
  let _ : Module A Γ(F, W) := Module.compHom _ φ
  have : Module.Flat A Γ(Spec (.of A), ⊤) :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv)
  have : IsScalarTower A Γ(Spec (.of A), ⊤) Γ(F, W) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat A Γ(F, W) := Module.Flat.trans A Γ(Spec (.of A), ⊤) Γ(F, W)
  let e : Γ(F, W) ≃ₗ[A] ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op V)) :=
    { __ := AddEquiv.refl _
      map_smul' a m := by
        change ((tilde M).smul ((U.ι.appIso W).inv ((U.ι.appLE ⊤ W hWtop) (φ a)))).asHom.hom m =
          ((tilde M).smul ((Spec (.of A)).presheaf.map
            (homOfLE (show V ≤ ⊤ from le_top)).op (φ a))).asHom.hom m
        rw [Scheme.Hom.appLE_appIso_inv_apply] }
  have := Module.Flat.of_linearEquiv e.symm
  let eV := (modulesSpecToSheaf.obj (tilde M)).presheaf.mapIso (eqToIso hV).op
  exact Module.Flat.of_linearEquiv eV.toLinearEquiv

/-- The sections of `M~` over a basic open `D(f)` are the localization of `M` at `f`. -/
private lemma isLocalizedModule_toOpen (R : CommRingCat.{u}) (M : ModuleCat R) (f : R) :
    IsLocalizedModule (Submonoid.powers f) (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom :=
  inferInstance

/-- **Stacks Project, Tag 0ATC.** Let `I` be an ideal of a commutative ring `A` and let
`U ⊆ Spec A` be a quasi-compact open. If `M/IM` is flat over `A/I` and `M~` is flat on `U`,
then `M/I₂M` is flat over `A/I₂`, where `I₂ = Ker (I → Γ(U, (I/I²)~))`.

The source assumes `A` local; locality is not used. -/
@[stacks 0ATC "flatness modulo I₂"]
theorem flat_quotient_smallerFlatnessIdeal
    {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M]
    (I : Ideal A) (U : (Spec (.of A)).Opens)
    (hU : IsCompact U.1)
    (hquot : Module.Flat (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M)))
    (hflat : SheafOfModules.IsFlat.{u, u, u, u} (O := (U : Scheme).sheaf)
      (show (U : Scheme).Modules from
        (tilde (ModuleCat.of A M)).restrict U.ι)) :
    Module.Flat (A ⧸ smallerFlatnessIdeal I U)
      (M ⧸ smallerFlatnessIdeal I U • (⊤ : Submodule A M)) := by
  classical
  let K := smallerFlatnessIdeal I U
  let J : Ideal (A ⧸ K) := Ideal.map (Ideal.Quotient.mk K) I
  have hJ : J ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact smallerFlatnessIdeal_sq_le I U
  obtain ⟨s, hs⟩ := finite_basicOpen_cover U hU
  have hFo : IsFlatOver U.ι.toLRSHom.toShHom ((tilde (ModuleCat.of A M)).restrict U.ι) :=
    isFlatOver_of_isFlat_of_isOpenImmersion U.ι _ hflat
  have hloc (f : s) : Module.Flat A (LocalizedModule (Submonoid.powers (f : A)) M) := by
    have := flat_basicOpen_sections (ModuleCat.of A M) U hFo f
      fun p hp => (hs p).mpr ⟨f, f.property, hp⟩
    let _ : IsLocalizedModule.Away (R := (.of A : CommRingCat)) (f : A)
        (tilde.toOpen (R := .of A) (ModuleCat.of A M) (PrimeSpectrum.basicOpen (f : A))).hom :=
      isLocalizedModule_toOpen (.of A) (ModuleCat.of A M) (f : A)
    exact Module.Flat.of_linearEquiv (IsLocalizedModule.iso (Submonoid.powers (f : A))
      (tilde.toOpen (R := .of A) (ModuleCat.of A M) (PrimeSpectrum.basicOpen (f : A))).hom)
  have hcore : Function.Injective (LinearMap.rTensor M (J.subtype.restrictScalars A)) := by
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    exact lTensor_injective_of_finite_localizations I hquot
      (killed_of_sq_bot I J (fun a ha => Ideal.mem_map_of_mem _ ha) hJ)
      (fun f : s => Submonoid.powers (f : A))
      (quotient_ideal_localizations_injective I U s fun p hp => (hs p).mp hp) hloc
      (J.subtype.restrictScalars A) J.subtype_injective
  exact flat_of_sq_zero_local_criterion J hJ
    (flat_quotient_map_quotient I K hquot)
    (injective_lift_lsmul_of_rTensor_injective K J hcore)

end AlgebraicGeometry

end
