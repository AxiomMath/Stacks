module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange

/-!
# The scheme-theoretic support of a finite type quasi-coherent module

Let `F` be a quasi-coherent module of finite type on a scheme `X`. The annihilators of its
modules of sections over the affine opens of `X` are compatible with localization, so they are
the components of an ideal sheaf on `X`. The closed subscheme it cuts out is the
*scheme-theoretic support* of `F`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport`: the ideal sheaf whose component at
  an affine open `U` is the annihilator of the `Γ(X, U)`-module `Γ(F, U)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport_ideal`: the component of that ideal
  sheaf at an affine open is the annihilator of the module of sections, so that on
  `Spec A ⊆ X` with `F|_{Spec A} = M~` the scheme-theoretic support is `Spec (A / Ann_A M)`.
* `AlgebraicGeometry.Scheme.Modules.map_annihilator_sections_basicOpen`: the annihilator of the
  sections over an affine open extends, along restriction to a principal open, to the
  annihilator of the sections there.

## Implementation notes

Compatibility with localization is flat base change for annihilators of finite modules:
`Γ(F, D(f))` is the localization of `Γ(F, U)` away from `f`, hence its base change along the
flat map `Γ(X, U) → Γ(X, D(f))`, and the annihilator of a finite module extends to the
annihilator of its flat base change. Finiteness of `Γ(F, U)` is where the finite type
hypothesis on `F` is used, and it is also what makes the statement false in general: without
it the annihilator of the sections need not localize.

## References

* [Stacks Project, Tag 05JU](https://stacks.math.columbia.edu/tag/05JU)
* [Stacks Project, Tag 07T8](https://stacks.math.columbia.edu/tag/07T8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The annihilator of a finite module extends, along a localization map, to the annihilator of
any localization of the module. -/
theorem map_annihilator_of_isLocalizedModule {R A M N : Type*} [CommRing R] [CommRing A]
    (S : Submonoid R) [Algebra R A] [IsLocalization S A]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (g : M →ₗ[R] N) [IsLocalizedModule S g] :
    (Module.annihilator R M).map (algebraMap R A) = Module.annihilator A N := by
  have : Module.Flat R A := IsLocalization.flat A S
  rw [ann_extension_eq_ann_baseChange_module]
  exact (IsLocalizedModule.isBaseChange S A g).equiv.annihilator_eq

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

/-- **The annihilator of the sections of a finite type quasi-coherent module localizes.** The
extension of `Ann_{Γ(X, U)} Γ(F, U)` along restriction to a principal open `D(f)` of an affine
open `U` is `Ann_{Γ(X, D(f))} Γ(F, D(f))`. -/
theorem map_annihilator_sections_basicOpen (U : X.affineOpens) (f : Γ(X, U.1)) :
    (Module.annihilator Γ(X, U.1) Γ(F, U.1)).map
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      Module.annihilator Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) := by
  have hfin : Module.Finite Γ(X, U.1) Γ(F, U.1) := moduleFinite_sections_on_affine F U.1 U.2
  have hring : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  let := moduleOfLE F (X.basicOpen_le f)
  have htower : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hmod : IsLocalizedModule.Away f (restrictₗ F (X.basicOpen_le f)) :=
    isLocalizedModule_restrictₗ F U.2 f rfl (X.basicOpen_le f)
  exact map_annihilator_of_isLocalizedModule (Submonoid.powers f)
    (restrictₗ F (X.basicOpen_le f))

/-- **The scheme-theoretic support of a finite type quasi-coherent module**, as an ideal sheaf:
its component at an affine open `U` is the annihilator of the `Γ(X, U)`-module `Γ(F, U)`. The
closed subscheme it cuts out is the smallest one from which `F` is a direct image. -/
@[stacks 05JU "the closed subscheme", stacks 05JV "the scheme-theoretic support"]
def schemeTheoreticSupport : X.IdealSheafData where
  ideal U := Module.annihilator Γ(X, U.1) Γ(F, U.1)
  map_ideal_basicOpen U f := map_annihilator_sections_basicOpen F U f

/-- On an affine open `U = Spec A` the scheme-theoretic support of `F` is cut out by the
annihilator of the `A`-module `Γ(F, U)`; equivalently, if `F|_U` is `M~` then the
scheme-theoretic support meets `U` in `Spec (A / Ann_A M)`. -/
@[stacks 05JU "part (1): affine annihilator formula"]
theorem schemeTheoreticSupport_ideal (U : X.affineOpens) :
    (schemeTheoreticSupport F).ideal U = Module.annihilator Γ(X, U.1) Γ(F, U.1) :=
  rfl

/-! ### `F` is a direct image from its scheme-theoretic support -/

/-- A function on an affine open that vanishes on the scheme-theoretic support of `F`
annihilates the sections of `F` there. -/
private theorem mem_annihilator_of_subschemeι_app_eq_zero (V : X.affineOpens) (a : Γ(X, V.1))
    (ha : ((schemeTheoreticSupport F).subschemeι.app V.1).hom a = 0) :
    a ∈ Module.annihilator Γ(X, V.1) Γ(F, V.1) := by
  rw [← schemeTheoreticSupport_ideal F V, ← (schemeTheoreticSupport F).ker_subschemeι_app V]
  exact RingHom.mem_ker.mpr ha

/-- A function on an open set of `X` that vanishes on the scheme-theoretic support of `F`
annihilates every section of `F` over that open set. -/
theorem smul_eq_zero_of_subschemeι_app_eq_zero (U : X.Opens) (a : Γ(X, U))
    (ha : ((schemeTheoreticSupport F).subschemeι.app U).hom a = 0) (m : Γ(F, U)) :
    a • m = 0 := by
  let i := (schemeTheoreticSupport F).subschemeι
  refine TopCat.Presheaf.IsSheaf.section_ext (U := op U) F.isSheaf fun x hx ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  refine ⟨V, hVU, hxV, ?_⟩
  have hpre : i ⁻¹ᵁ V ≤ i ⁻¹ᵁ U := fun z hz ↦ hVU hz
  have hzero : i.appLE V (i ⁻¹ᵁ V) le_rfl (X.presheaf.map (homOfLE hVU).op a) = 0 := by
    have h₁ : i.appLE U (i ⁻¹ᵁ U) le_rfl a = 0 := by simpa [Scheme.Hom.appLE] using ha
    have h₂ : i.appLE U (i ⁻¹ᵁ V) hpre a = 0 := by
      have h := congrArg (fun φ ↦ φ.hom a)
        (i.appLE_map (U := U) (V := i ⁻¹ᵁ U) le_rfl (homOfLE hpre).op)
      rw [CommRingCat.hom_comp, RingHom.comp_apply, h₁] at h
      simpa [Scheme.Hom.appLE] using h.symm
    have h₃ := congrArg (fun φ ↦ φ.hom a)
      (i.map_appLE (U := V) (U' := U) (V := i ⁻¹ᵁ V) le_rfl (homOfLE hVU).op)
    simpa [Scheme.Hom.appLE] using h₃.trans h₂
  have hmem : X.presheaf.map (homOfLE hVU).op a ∈ Module.annihilator Γ(X, V) Γ(F, V) :=
    mem_annihilator_of_subschemeι_app_eq_zero F ⟨V, hV⟩ _
      (by simpa [Scheme.Hom.appLE] using hzero)
  rw [map_zero]
  exact (F.map_smul (homOfLE hVU) a m).trans (Module.mem_annihilator.mp hmem _)

/-- The unit of the pullback-pushforward adjunction along the closed immersion of the
scheme-theoretic support of `F` is an isomorphism at `F`. -/
instance isIso_unit_app_schemeTheoreticSupport :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (schemeTheoreticSupport F).subschemeι).unit.app F) :=
  Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero _ F
    (smul_eq_zero_of_subschemeι_app_eq_zero F)

/-- **The direct image of the restriction of `F` to its scheme-theoretic support is `F`.** This
is the inverse of the unit of the pullback-pushforward adjunction, which is an isomorphism
because the ideal of the scheme-theoretic support annihilates `F`. -/
def pushforwardPullbackSchemeTheoreticSupportIso :
    (Scheme.Modules.pushforward (schemeTheoreticSupport F).subschemeι).obj
        ((Scheme.Modules.pullback (schemeTheoreticSupport F).subschemeι).obj F) ≅ F :=
  (asIso ((Scheme.Modules.pullbackPushforwardAdjunction
    (schemeTheoreticSupport F).subschemeι).unit.app F)).symm

/-- Any module on the scheme-theoretic support of `F` whose direct image is `F` is isomorphic
to the pullback of `F`. -/
def isoPullback_of_pushforwardIso (G : (schemeTheoreticSupport F).subscheme.Modules)
    (e : (Scheme.Modules.pushforward (schemeTheoreticSupport F).subschemeι).obj G ≅ F) :
    G ≅ (Scheme.Modules.pullback (schemeTheoreticSupport F).subschemeι).obj F :=
  (Stacks.ClosedImmersion.fullyFaithfulPushforward _).preimageIso
    (e ≪≫ (pushforwardPullbackSchemeTheoreticSupportIso F).symm)

/-- The pullback of `F` to its scheme-theoretic support is of finite type. -/
instance isFiniteType_pullback_schemeTheoreticSupport :
    ((Scheme.Modules.pullback (schemeTheoreticSupport F).subschemeι).obj F).IsFiniteType :=
  SheafOfModules.pullback_isFiniteType
    (schemeTheoreticSupport F).subschemeι.toLRSHom.toShHom F

/-- A quasi-coherent module of finite type is the direct image of a quasi-coherent module of
finite type on its scheme-theoretic support. -/
@[stacks 05JU "existence of the descended module"]
theorem exists_module_on_schemeTheoreticSupport :
    ∃ G : (schemeTheoreticSupport F).subscheme.Modules,
      G.IsQuasicoherent ∧ G.IsFiniteType ∧
        Nonempty ((Scheme.Modules.pushforward
          (schemeTheoreticSupport F).subschemeι).obj G ≅ F) :=
  ⟨(Scheme.Modules.pullback (schemeTheoreticSupport F).subschemeι).obj F, inferInstance,
    inferInstance, ⟨pushforwardPullbackSchemeTheoreticSupportIso F⟩⟩

/-- Every closed subscheme of `X` from which `F` is a direct image contains the
scheme-theoretic support of `F`; equivalently, its ideal sheaf is contained in the ideal sheaf
of the scheme-theoretic support. -/
@[stacks 05JU "minimality"]
theorem schemeTheoreticSupport_isSmallest (J : X.IdealSheafData)
    (G : J.subscheme.Modules)
    (e : (Scheme.Modules.pushforward J.subschemeι).obj G ≅ F) :
    J ≤ schemeTheoreticSupport F := by
  have hkill :=
    (Stacks.ClosedImmersion.pushforward_essImage_iff J.subschemeι F).mp ⟨G, ⟨e⟩⟩
  refine Scheme.IdealSheafData.le_def.mpr fun U a ha ↦ ?_
  rw [schemeTheoreticSupport_ideal F U]
  refine Module.mem_annihilator.mpr fun m ↦ hkill U.1 a ?_ m
  exact RingHom.mem_ker.mp (by rwa [J.ker_subschemeι_app U])

/-- A descent of `F` to its scheme-theoretic support is unique up to a unique isomorphism
compatible with the chosen identifications of the direct images with `F`. -/
@[stacks 05JU "part (2): uniqueness"]
theorem module_on_schemeTheoreticSupport_unique
    (G H : (schemeTheoreticSupport F).subscheme.Modules)
    (eG : (Scheme.Modules.pushforward (schemeTheoreticSupport F).subschemeι).obj G ≅ F)
    (eH : (Scheme.Modules.pushforward (schemeTheoreticSupport F).subschemeι).obj H ≅ F) :
    ∃! φ : G ≅ H,
      (Scheme.Modules.pushforward (schemeTheoreticSupport F).subschemeι).map φ.hom ≫
        eH.hom = eG.hom := by
  have hff := Stacks.ClosedImmersion.fullyFaithfulPushforward
    (schemeTheoreticSupport F).subschemeι
  refine ⟨hff.preimageIso (eG ≪≫ eH.symm), by simp, fun ψ hψ ↦ ?_⟩
  refine Iso.ext (hff.map_injective ?_)
  rw [← cancel_mono eH.hom, hψ]
  simp

/-- Every descent of `F` to its scheme-theoretic support is of finite type. -/
@[stacks 05JU "part (3): finite type"]
theorem module_on_schemeTheoreticSupport_isFiniteType
    (G : (schemeTheoreticSupport F).subscheme.Modules)
    (e : (Scheme.Modules.pushforward (schemeTheoreticSupport F).subschemeι).obj G ≅ F) :
    G.IsFiniteType :=
  isFiniteType_of_scheme_iso (isoPullback_of_pushforwardIso F G e).symm

/-- Every descent of `F` to its scheme-theoretic support is quasi-coherent. -/
theorem module_on_schemeTheoreticSupport_isQuasicoherent
    (G : (schemeTheoreticSupport F).subscheme.Modules)
    (e : (Scheme.Modules.pushforward (schemeTheoreticSupport F).subschemeι).obj G ≅ F) :
    G.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (schemeTheoreticSupport F).subscheme.ringCatSheaf).prop_of_iso
    (isoPullback_of_pushforwardIso F G e).symm inferInstance

/-! ### The scheme-theoretic support carries the support -/

/-- On an affine open, the zero locus of the annihilator of the sections of `F` is the support
of the module of sections. -/
lemma mem_zeroLocus_annihilator_iff (U : X.affineOpens) {x : X} (hxU : x ∈ U.1) :
    x ∈ X.zeroLocus (U := U.1) (Module.annihilator Γ(X, U.1) Γ(F, U.1)) ↔
      U.2.primeIdealOf ⟨x, hxU⟩ ∈ Module.support Γ(X, U.1) Γ(F, U.1) := by
  have hfin : Module.Finite Γ(X, U.1) Γ(F, U.1) := moduleFinite_sections_on_affine F U.1 U.2
  have hpoint : U.2.fromSpec (U.2.primeIdealOf ⟨x, hxU⟩) = x :=
    U.2.fromSpec_primeIdealOf ⟨x, hxU⟩
  set p := U.2.primeIdealOf ⟨x, hxU⟩
  have hbasic (s : Γ(X, U.1)) : x ∈ X.basicOpen s ↔ p ∈ PrimeSpectrum.basicOpen s := by
    rw [← hpoint, ← U.2.fromSpec_preimage_basicOpen s]
    rfl
  rw [Scheme.mem_zeroLocus_iff, Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus]
  simp only [SetLike.mem_coe, Set.subset_def]
  refine ⟨fun h s hs ↦ ?_, fun h s hs hx ↦ ?_⟩
  · by_contra hsp
    exact h s hs ((hbasic s).2 ((PrimeSpectrum.mem_basicOpen s _).2 hsp))
  · exact (PrimeSpectrum.mem_basicOpen s _).1 ((hbasic s).1 hx) (h s hs)

/-- The support of `F` is the closed set underlying its scheme-theoretic support. -/
@[stacks 05JU "part (4): support on the ambient scheme"]
theorem supp_eq_support_schemeTheoreticSupport :
    SheafOfModules.supp F = ((schemeTheoreticSupport F).support : Set X) := by
  ext x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hsupp : x ∈ (schemeTheoreticSupport F).support ↔
      x ∈ X.zeroLocus (U := U) (Module.annihilator Γ(X, U) Γ(F, U)) :=
    Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU
  exact (Scheme.Modules.mem_support_sections_iff_mem_supp F ⟨U, hU⟩ x hxU).symm.trans
    ((mem_zeroLocus_annihilator_iff F ⟨U, hU⟩ hxU).symm.trans hsupp.symm)

/-- A descent of `F` to its scheme-theoretic support has support the whole closed subscheme. -/
@[stacks 05JU "part (4): support on the closed subscheme"]
theorem module_on_schemeTheoreticSupport_support
    (G : (schemeTheoreticSupport F).subscheme.Modules)
    (e : (Scheme.Modules.pushforward (schemeTheoreticSupport F).subschemeι).obj G ≅ F) :
    SheafOfModules.supp G = Set.univ := by
  let i := (schemeTheoreticSupport F).subschemeι
  refine Set.eq_univ_of_forall fun z ↦ ?_
  refine (SheafOfModules.mem_supp_iff_nontrivial_stalk
    (show SheafOfModules (schemeTheoreticSupport F).subscheme.ringCatSheaf from G) z).mpr ?_
  have hx : i.base z ∈ SheafOfModules.supp F := by
    rw [supp_eq_support_schemeTheoreticSupport F]
    have hrange : i.base z ∈ Set.range (schemeTheoreticSupport F).subschemeι := ⟨z, rfl⟩
    rwa [(schemeTheoreticSupport F).range_subschemeι] at hrange
  have hF : Nontrivial
      ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} (i.base z)).obj F) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk F (i.base z)).mp hx
  have hpush : Nontrivial ((i.base _*
      (Scheme.Modules.toPresheaf (schemeTheoreticSupport F).subscheme).obj G).stalk (i.base z)) :=
    (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} (i.base z)).mapIso e.symm).hom)).1.nontrivial
  have hα : IsIso (((Scheme.Modules.toPresheaf (schemeTheoreticSupport F).subscheme).obj
      G).stalkPushforward Ab i.base z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Ab
      i.isClosedEmbedding.isInducing _ z
  exact (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf (schemeTheoreticSupport F).subscheme).obj G).stalkPushforward
      Ab i.base z)).1.nontrivial

end AlgebraicGeometry.Scheme.Modules

end
