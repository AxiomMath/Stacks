module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Ideal sheaves on an affine scheme

On `Spec R`, the kernel of the map `M^~ ⟶ N^~` induced by a surjection of `R`-modules
`M ⟶ N` is the sheaf associated to the kernel of that surjection. For an ideal `I` of `R`
this says that the kernel of `𝒪_{Spec R} ⟶ (R ⧸ I)^~` is `I^~`, and — identifying
`(R ⧸ I)^~` with the pushforward of `𝒪_{Spec (R ⧸ I)}` — that the kernel sheaf of the
closed immersion `Spec (R ⧸ I) ⟶ Spec R` is `I^~`.

This is the affine content of Stacks 01IN.

## Main definitions

* `kerShortComplex` is the short complex `p ⟶ M ⟶ N` attached to a map `g : M ⟶ N` of
  `R`-modules together with a submodule `p` which is the kernel of `g`.
* `quotRing`, `quotHom`, `pushforwardQuotUnit` and `quotUnitHom` name the closed immersion
  `Spec (R ⧸ I) ⟶ Spec R` and its structure-sheaf map.

## Main results

* `mono_tilde_map` : the `~` construction takes an injective map of modules to a
  monomorphism of sheaves of modules.
* `exists_tilde_iso_kernel` : for a surjection `g : M ⟶ N` of `R`-modules whose kernel is a
  given submodule `p`, the sheaf `p^~` is the kernel of `g^~`, compatibly with the inclusion
  `p ⟶ M`.
* `exists_tilde_iso_kernel_mkQ` : the ideal-theoretic case, `I^~` is the kernel of
  `R^~ ⟶ (R ⧸ I)^~`.
* `exists_tilde_iso_kernel_quotUnitHom` : the geometric form, `I^~` is the kernel of the
  structure-sheaf map `𝒪_{Spec R} ⟶ i_* 𝒪_{Spec (R ⧸ I)}`, compatibly with the two
  inclusions into `𝒪_{Spec R}`.

## References

* [Stacks Project, Tag 01IN](https://stacks.math.columbia.edu/tag/01IN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.ClosedImmersion.IdealSheafAffine

variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}

/-- Over a basic open `D(r)`, the map on sections induced by `u^~` is injective as soon as `u`
is. -/
theorem injective_tilde_map_app_basicOpen (u : M ⟶ N) (hu : Function.Injective u.hom) (r : R) :
    Function.Injective
      ((modulesSpecToSheaf.map (tilde.map u)).hom.app (op (PrimeSpectrum.basicOpen r))).hom := by
  refine IsLocalizedModule.injective_of_map_zero (.powers r)
    (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom (fun m hm => ?_)
  have h := congr($(tilde.toOpen_map_app u (PrimeSpectrum.basicOpen r)).hom m)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h hm
  rw [h] at hm
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (.powers r)
    (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom).mp hm
  refine (IsLocalizedModule.eq_zero_iff (.powers r)
    (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom).mpr ⟨s, hu ?_⟩
  rw [Submonoid.smul_def] at hs ⊢
  rw [map_smul, map_zero]
  exact hs

/-- The map on sections over an arbitrary open induced by `u^~` is injective as soon as `u`
is. -/
theorem injective_tilde_map_app (u : M ⟶ N) (hu : Function.Injective u.hom)
    (V : (Spec R).Opens) :
    Function.Injective ((modulesSpecToSheaf.map (tilde.map u)).hom.app (op V)).hom := by
  have key : ∀ s, ((modulesSpecToSheaf.map (tilde.map u)).hom.app (op V)).hom s = 0 → s = 0 := by
    intro s hs
    refine TopCat.Presheaf.IsSheaf.section_ext
      (F := (modulesSpecToSheaf.obj (tilde M)).obj) (modulesSpecToSheaf.obj (tilde M)).2
      (U := op V) (t := 0) (fun x hxV => ?_)
    obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrV⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxV V.2
    refine ⟨_, hrV, hxr, injective_tilde_map_app_basicOpen u hu r ?_⟩
    simp only [map_zero]
    exact (congr($((modulesSpecToSheaf.map (tilde.map u)).hom.naturality
      (homOfLE hrV).op).hom s)).trans
      (by rw [ModuleCat.hom_comp]; simp only [LinearMap.coe_comp,
        Function.comp_apply, hs, map_zero]; rfl)
  exact fun a b hab ↦ sub_eq_zero.mp (key (a - b) (by rw [map_sub, hab, sub_self]))

/-- The `~` construction takes an injective map of `R`-modules to a monomorphism of
`𝒪_{Spec R}`-modules. -/
theorem mono_tilde_map (u : M ⟶ N) (hu : Function.Injective u.hom) : Mono (tilde.map u) := by
  have (V : (Opens ↥(Spec R))ᵒᵖ) :
      Mono (((sheafToPresheaf (Opens.grothendieckTopology ↥(Spec R)) (ModuleCat R)).map
        (modulesSpecToSheaf.map (tilde.map u))).app V) := by
    rw [ModuleCat.mono_iff_injective]
    exact injective_tilde_map_app u hu V.unop
  exact Functor.mono_of_mono_map modulesSpecToSheaf
    (Functor.mono_of_mono_map (sheafToPresheaf _ _) (NatTrans.mono_of_mono_app _))

/-- The `~` construction takes the inclusion of a submodule to a monomorphism. -/
private theorem mono_tilde_map_subtype (p : Submodule R M) :
    Mono (tilde.map (ModuleCat.ofHom p.subtype)) :=
  mono_tilde_map (M := ModuleCat.of R p) _ Subtype.val_injective

/-- A limit kernel fork `X ⟶ Y ⟶ Z` identifies `X` with `kernel g`, compatibly with `f`. -/
private theorem exists_iso_kernel_of_isLimit {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel g] (w : f ≫ g = 0)
    (h : IsLimit (KernelFork.ofι f w)) :
    ∃ e : X ≅ kernel g, e.hom ≫ kernel.ι g = f :=
  ⟨IsLimit.conePointUniqueUpToIso h (limit.isLimit _),
    IsLimit.conePointUniqueUpToIso_hom_comp h (limit.isLimit _) WalkingParallelPair.zero⟩

variable (g : M ⟶ N) {p : Submodule R M} (hp : LinearMap.ker g.hom = p)

/-- The short complex `p ⟶ M ⟶ N` attached to a map `g : M ⟶ N` of `R`-modules and a
submodule `p` which is the kernel of `g`. -/
def kerShortComplex : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom p.subtype) g
    (by ext x; exact (LinearMap.mem_ker (f := g.hom)).1 (hp ▸ x.2))

include hp in
/-- The short complex `p ⟶ M ⟶ N` is exact at `M`. -/
theorem exact_kerShortComplex : (kerShortComplex g hp).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact ⟨⟨x, hp ▸ (LinearMap.mem_ker (f := g.hom)).2 hx⟩, rfl⟩

include hp in
/-- For a surjection `g : M ⟶ N` of `R`-modules with kernel the submodule `p`, the sheaf
`p^~` on `Spec R` is the kernel of `g^~`, compatibly with the inclusion of `p` into `M`. -/
theorem exists_tilde_iso_kernel (hg : Function.Surjective g.hom) :
    ∃ e : tilde (ModuleCat.of R p) ≅ kernel (tilde.map g),
      e.hom ≫ kernel.ι (tilde.map g) = tilde.map (ModuleCat.ofHom p.subtype) := by
  have hsub : Mono (ModuleCat.ofHom p.subtype) :=
    (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have hsur : Epi g := (ModuleCat.epi_iff_surjective _).mpr hg
  have hmono : Mono (kerShortComplex g hp).f := hsub
  have hepi : Epi (kerShortComplex g hp).g := hsur
  have hmono' : Mono ((kerShortComplex g hp).map (tilde.functor R)).f :=
    mono_tilde_map_subtype p
  have hker : IsLimit (KernelFork.ofι ((kerShortComplex g hp).map (tilde.functor R)).f
      ((kerShortComplex g hp).map (tilde.functor R)).zero) :=
    ((exact_kerShortComplex g hp).map_of_epi_of_preservesCokernel _ hepi inferInstance).fIsKernel
  exact exists_iso_kernel_of_isLimit _ _ _ hker

/-- **The module-level affine case of Stacks 01IN.** For an ideal `I` of `R`, the sheaf `I^~`
on `Spec R` is the kernel of the map `R^~ ⟶ (R ⧸ I)^~` induced by the quotient map,
compatibly with the inclusion of `I` into `R`. -/
theorem exists_tilde_iso_kernel_mkQ (I : Ideal R) :
    ∃ e : tilde (ModuleCat.of R I) ≅ kernel (tilde.map (ModuleCat.ofHom I.mkQ)),
      e.hom ≫ kernel.ι (tilde.map (ModuleCat.ofHom I.mkQ)) =
        tilde.map (ModuleCat.ofHom I.subtype) :=
  exists_tilde_iso_kernel (ModuleCat.ofHom I.mkQ) (Submodule.ker_mkQ I)
    (Submodule.mkQ_surjective I)

section Pushforward

variable (I : Ideal R)

/-- The quotient of `R` by an ideal, as an object of `CommRingCat`. -/
abbrev quotRing : CommRingCat.{u} := CommRingCat.of (R ⧸ I)

/-- The quotient map `R ⟶ R ⧸ I`, as a morphism of `CommRingCat`. -/
abbrev quotHom : R ⟶ quotRing I := CommRingCat.ofHom (Ideal.Quotient.mk I)

/-- The pushforward of the structure sheaf of `Spec (R ⧸ I)` along the closed immersion
`Spec (R ⧸ I) ⟶ Spec R`, as an `𝒪_{Spec R}`-module. -/
abbrev pushforwardQuotUnit : (Spec R).Modules :=
  (Scheme.Modules.pushforward (Spec.map (quotHom I))).obj
    (SheafOfModules.unit (Spec (quotRing I)).ringCatSheaf)

/-- The structure-sheaf map `𝒪_{Spec R} ⟶ i_* 𝒪_{Spec (R ⧸ I)}` of the closed immersion
`i : Spec (R ⧸ I) ⟶ Spec R`, as a morphism of `𝒪_{Spec R}`-modules. -/
abbrev quotUnitHom :
    SheafOfModules.unit (Spec R).ringCatSheaf ⟶ pushforwardQuotUnit I :=
  SheafOfModules.unitToPushforwardObjUnit (Spec.map (quotHom I)).toRingCatSheafHom

/-- Taking global sections of `𝒪_{Spec R}`-modules turns a composition into the composition
of the maps on global sections. -/
theorem moduleSpecΓFunctor_map_comp_apply {A B C : (Spec R).Modules} (a : A ⟶ B) (b : B ⟶ C)
    (y : moduleSpecΓFunctor.obj A) :
    (moduleSpecΓFunctor.map (a ≫ b)).hom y =
      (moduleSpecΓFunctor.map b).hom ((moduleSpecΓFunctor.map a).hom y) :=
  rfl

/-- On global sections, the structure-sheaf map of `Spec (R ⧸ I) ⟶ Spec R` is the quotient
map `R ⟶ R ⧸ I`, read through the canonical identifications of `R` with `Γ(Spec R, ⊤)` and of
`R ⧸ I` with `Γ(Spec (R ⧸ I), ⊤)`. -/
theorem moduleSpecΓFunctor_map_quotUnitHom_toOpen (x : R) :
    (moduleSpecΓFunctor.map (tildeSelf.hom ≫ quotUnitHom I)).hom
        ((tilde.toOpen (ModuleCat.of R R) ⊤).hom x) =
      (Scheme.ΓSpecIso (quotRing I)).inv (Ideal.Quotient.mk I x) := by
  have h := congr($(Scheme.ΓSpecIso_inv_naturality (quotHom I)) x)
  simp only [CommRingCat.comp_apply] at h
  exact h.symm

/-- The inclusion `I^~ ⟶ 𝒪_{Spec R}` is killed by the structure-sheaf map of
`Spec (R ⧸ I) ⟶ Spec R`. -/
theorem tilde_subtype_comp_quotUnitHom :
    tilde.map (ModuleCat.ofHom I.subtype) ≫ tildeSelf.hom ≫ quotUnitHom I = 0 := by
  refine (tilde.adjunction.homEquiv (ModuleCat.of R I) (pushforwardQuotUnit I)).injective ?_
  change tilde.adjunction.unit.app _ ≫ moduleSpecΓFunctor.map _ =
    tilde.adjunction.unit.app _ ≫ moduleSpecΓFunctor.map _
  ext y
  have h1 := congr($(tilde.toOpen_map_app (ModuleCat.ofHom I.subtype) ⊤).hom y)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1
  change (moduleSpecΓFunctor.map (tildeSelf.hom ≫ quotUnitHom I)).hom
      ((moduleSpecΓFunctor.map (tilde.map (ModuleCat.ofHom I.subtype))).hom
        ((tilde.toOpen (ModuleCat.of R I) ⊤).hom y)) = 0
  refine Eq.trans (congrArg (moduleSpecΓFunctor.map
    (tildeSelf.hom ≫ quotUnitHom I)).hom h1) ?_
  refine (moduleSpecΓFunctor_map_quotUnitHom_toOpen I y.1).trans ?_
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr y.2, map_zero]
  rfl

/-- The quotient map `R ⟶ R ⧸ I` is an epimorphism of `R`-modules. -/
private theorem epi_ofHom_mkQ : Epi (ModuleCat.ofHom I.mkQ) :=
  (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective I)

/-- Applying `~` to the short complex `I ⟶ R ⟶ R ⧸ I` leaves it exact. -/
theorem exact_map_kerShortComplex_mkQ :
    ((kerShortComplex (ModuleCat.ofHom I.mkQ) (Submodule.ker_mkQ I)).map
      (tilde.functor R)).Exact := by
  have hepi : Epi (kerShortComplex (ModuleCat.ofHom I.mkQ) (Submodule.ker_mkQ I)).g :=
    epi_ofHom_mkQ I
  exact (exact_kerShortComplex _ _).map_of_epi_of_preservesCokernel _ hepi inferInstance

/-- Sections of `(R ⧸ I)^~` over `⊤` are exhausted by the images of the elements of `R`. -/
theorem surjective_toOpen_mk :
    Function.Surjective
      (fun x : R => (tilde.toOpen (ModuleCat.of R (R ⧸ I)) ⊤).hom (Ideal.Quotient.mk I x)) := by
  intro z
  obtain ⟨w, hw⟩ :=
    (ConcreteCategory.bijective_of_isIso (tilde.toOpen (ModuleCat.of R (R ⧸ I)) ⊤)).2 z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
  exact ⟨x, hw⟩

/-- **The geometric affine case of Stacks 01IN.** For the closed immersion
`i : Spec (R ⧸ I) ⟶ Spec R`, the kernel of the structure-sheaf map
`𝒪_{Spec R} ⟶ i_* 𝒪_{Spec (R ⧸ I)}` is the sheaf `I^~` associated to the ideal `I`, compatibly
with the two inclusions into `𝒪_{Spec R}`. -/
theorem exists_tilde_iso_kernel_quotUnitHom :
    ∃ e : tilde (ModuleCat.of R I) ≅ kernel (quotUnitHom I),
      e.hom ≫ kernel.ι (quotUnitHom I) =
        tilde.map (ModuleCat.ofHom I.subtype) ≫ tildeSelf.hom := by
  have hS := exact_map_kerShortComplex_mkQ I
  have : Epi ((kerShortComplex (ModuleCat.ofHom I.mkQ)
      (Submodule.ker_mkQ I)).map (tilde.functor R)).g :=
    have := epi_ofHom_mkQ I
    inferInstanceAs (Epi ((tilde.functor R).map (ModuleCat.ofHom I.mkQ)))
  obtain ⟨m, hm⟩ := hS.desc' (tildeSelf.hom ≫ quotUnitHom I) (tilde_subtype_comp_quotUnitHom I)
  have hΓ : ∀ x : R, (moduleSpecΓFunctor.map m).hom
      ((tilde.toOpen (ModuleCat.of R (R ⧸ I)) ⊤).hom (Ideal.Quotient.mk I x)) =
      (Scheme.ΓSpecIso (quotRing I)).inv (Ideal.Quotient.mk I x) := by
    intro x
    have h1 := congr($(tilde.toOpen_map_app (ModuleCat.ofHom I.mkQ) ⊤).hom x)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1
    have h2 := congr($(moduleSpecΓFunctor.congr_map hm).hom
      ((tilde.toOpen (ModuleCat.of R R) ⊤).hom x))
    refine Eq.trans (congrArg (moduleSpecΓFunctor.map m).hom h1.symm) ?_
    exact ((moduleSpecΓFunctor_map_comp_apply
      (tilde.map (ModuleCat.ofHom I.mkQ)) m _).symm.trans h2).trans
      (moduleSpecΓFunctor_map_quotUnitHom_toOpen I x)
  have hbij : Function.Bijective (moduleSpecΓFunctor.map m).hom := by
    constructor
    · intro z z' hzz
      obtain ⟨x, rfl⟩ := surjective_toOpen_mk I z
      obtain ⟨x', rfl⟩ := surjective_toOpen_mk I z'
      rw [hΓ, hΓ] at hzz
      exact congrArg (tilde.toOpen (ModuleCat.of R (R ⧸ I)) ⊤).hom
        ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (quotRing I)).inv).1 hzz)
    · intro z
      obtain ⟨w, hw⟩ :=
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (quotRing I)).inv).2 z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
      exact ⟨_, (hΓ x).trans hw⟩
  have hiso : IsIso (modulesSpecToSheaf.map m) := by
    refine isLocalizing_of_isIso_app_top ?_ (isLocalizing_tilde _) ?_
    · rw [ConcreteCategory.isIso_iff_bijective]
      exact hbij
    · exact isLocalizing_pushforward_of_isLocalizing (quotHom I)
        ((isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance)
  have hmiso : IsIso m := isIso_of_reflects_iso m modulesSpecToSheaf
  have hw : (tilde.map (ModuleCat.ofHom I.subtype) ≫ tildeSelf.hom) ≫ quotUnitHom I = 0 :=
    (Category.assoc _ _ _).trans (tilde_subtype_comp_quotUnitHom I)
  have := mono_tilde_map_subtype (M := ModuleCat.of R R) I
  have : Mono ((kerShortComplex (ModuleCat.ofHom I.mkQ)
      (Submodule.ker_mkQ I)).map (tilde.functor R)).f :=
    this
  have : Mono (tildeSelf (R := R)).hom :=
    inferInstanceAs (Mono (𝟙 (tilde (ModuleCat.of R R))))
  have : Mono (tilde.map (ModuleCat.ofHom I.subtype) ≫ tildeSelf.hom) := mono_comp _ _
  have hlimit : IsLimit (KernelFork.ofι
      (tilde.map (ModuleCat.ofHom I.subtype) ≫ tildeSelf.hom) hw) := by
    refine KernelFork.IsLimit.ofι' _ hw (fun {A} k hk => ?_)
    have key : (k ≫ tildeSelf.inv) ≫ tildeSelf.hom ≫ quotUnitHom I = 0 :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => k ≫ z) (Iso.inv_hom_id_assoc tildeSelf (quotUnitHom I))).trans hk)
    have hk' : (k ≫ tildeSelf.inv) ≫ ((kerShortComplex (ModuleCat.ofHom I.mkQ)
        (Submodule.ker_mkQ I)).map (tilde.functor R)).g = 0 := by
      refine (cancel_mono m).mp ?_
      exact (Category.assoc _ _ _).trans
        (((congrArg (fun z => (k ≫ tildeSelf.inv) ≫ z) hm).trans key).trans zero_comp.symm)
    refine ⟨hS.lift (k ≫ tildeSelf.inv) hk', ?_⟩
    have hl : hS.lift (k ≫ tildeSelf.inv) hk' ≫
        ((kerShortComplex (ModuleCat.ofHom I.mkQ) (Submodule.ker_mkQ I)).map
          (tilde.functor R)).f = k ≫ tildeSelf.inv := hS.lift_f _ _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ tildeSelf.hom) hl).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => k ≫ z) tildeSelf.inv_hom_id).trans (Category.comp_id k))))
  exact exists_iso_kernel_of_isLimit _ _ _ hlimit

end Pushforward

end Stacks.ClosedImmersion.IdealSheafAffine

end
