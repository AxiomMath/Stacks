module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.AlgebraicGeometry.Blowup.AlmostExactness
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.Immersions
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoretic
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# An invertible direct image supported finitely over the base

Let `f : X ⟶ Y` be a separated morphism of finite type and let `F` be a quasi-coherent
`𝒪_X`-module of finite type. When the scheme-theoretic support of `F` is finite over `Y` and the
direct image `f_* F` is invertible, `f` admits a section `s` and `F` is the direct image of
`f_* F` along `s`. Conversely, over a reduced base, a module supported on the image of a given
section `s` with invertible direct image is the direct image of `f_* F` along that very `s`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_section_iso_pushforward_of_invertible_pushforward`:
  the existence of the section.
* `AlgebraicGeometry.Scheme.Modules.iso_pushforward_section_of_invertible_pushforward`: the
  identification with the direct image along a prescribed section, over a reduced base.

## Implementation notes

The scheme-theoretic support of `F` is the closed subscheme cut out by
`AlgebraicGeometry.Scheme.Modules.annihilatorIdeal`, and the support of `F` being finite over
`Y` is finiteness of the composite of its closed immersion with `f`. The first section proves
the parts of [Stacks, Tag 05JU] used here at `annihilatorIdeal`;
`AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport` is the same ideal sheaf presented
directly rather than through `Scheme.IdealSheafData.ofIdeals`.

## References

* [Stacks Project, Tag 0FZP](https://stacks.math.columbia.edu/tag/0FZP)
* [Stacks Project, Tag 0FZQ](https://stacks.math.columbia.edu/tag/0FZQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-! ### The scheme-theoretic support

Everything in this section is [Stacks, Tag 05JU] read at
`AlgebraicGeometry.Scheme.Modules.annihilatorIdeal` rather than at the tagged
`AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport`, which is the same ideal sheaf
presented differently.
-/

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

/-- The annihilators of the sections of a finite type quasi-coherent module, assembled into an
ideal sheaf. -/
private def annihilatorSheaf : X.IdealSheafData where
  ideal U := Module.annihilator Γ(X, U.1) Γ(F, U.1)
  map_ideal_basicOpen U f := map_annihilator_sections_basicOpen F U f

/-- For a finite type quasi-coherent module the annihilator ideal sheaf has the annihilators of
the modules of sections as its components. -/
private theorem annihilatorIdeal_eq_annihilatorSheaf :
    Scheme.Modules.annihilatorIdeal F = annihilatorSheaf F :=
  Scheme.IdealSheafData.ofIdeals_ideal (annihilatorSheaf F)

/-- The component of the annihilator ideal sheaf at an affine open is the annihilator of the
module of sections there. -/
private theorem annihilatorIdeal_ideal (U : X.affineOpens) :
    (Scheme.Modules.annihilatorIdeal F).ideal U =
      Module.annihilator Γ(X, U.1) Γ(F, U.1) := by
  rw [annihilatorIdeal_eq_annihilatorSheaf]
  rfl

/-- A function on an affine open that vanishes on the scheme-theoretic support of `F`
annihilates the sections of `F` there. -/
private theorem mem_annihilator_of_subschemeι_app_eq_zero (V : X.affineOpens) (a : Γ(X, V.1))
    (ha : ((Scheme.Modules.annihilatorIdeal F).subschemeι.app V.1).hom a = 0) :
    a ∈ Module.annihilator Γ(X, V.1) Γ(F, V.1) := by
  rw [← annihilatorIdeal_ideal F V,
    ← (Scheme.Modules.annihilatorIdeal F).ker_subschemeι_app V]
  exact RingHom.mem_ker.mpr ha

/-- A function on an open set of `X` that vanishes on the scheme-theoretic support of `F`
annihilates every section of `F` over that open set. -/
private theorem smul_eq_zero_of_annihilatorIdeal_subschemeι_app_eq_zero
    (U : X.Opens) (a : Γ(X, U))
    (ha : ((Scheme.Modules.annihilatorIdeal F).subschemeι.app U).hom a = 0) (m : Γ(F, U)) :
    a • m = 0 := by
  let i := (Scheme.Modules.annihilatorIdeal F).subschemeι
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
  have hsmul : F.presheaf.map (homOfLE hVU).op (a • m) =
      X.presheaf.map (homOfLE hVU).op a • F.presheaf.map (homOfLE hVU).op m :=
    F.map_smul (homOfLE hVU) a m
  rw [map_zero]
  exact hsmul.trans (Module.mem_annihilator.mp hmem _)

private instance isIso_unit_app_annihilatorIdeal :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (Scheme.Modules.annihilatorIdeal F).subschemeι).unit.app F) :=
  Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero _ F
    (smul_eq_zero_of_annihilatorIdeal_subschemeι_app_eq_zero F)

/-- The direct image of the restriction of `F` to its scheme-theoretic support is `F`. -/
private def pushforwardPullbackAnnihilatorIso :
    (Scheme.Modules.pushforward (Scheme.Modules.annihilatorIdeal F).subschemeι).obj
        ((Scheme.Modules.pullback (Scheme.Modules.annihilatorIdeal F).subschemeι).obj F) ≅ F :=
  (asIso ((Scheme.Modules.pullbackPushforwardAdjunction
    (Scheme.Modules.annihilatorIdeal F).subschemeι).unit.app F)).symm

/-- Any module on the scheme-theoretic support of `F` whose direct image is `F` is isomorphic to
the pullback of `F`. -/
private def isoPullback_of_pushforwardIso_annihilatorIdeal
    (G : (Scheme.Modules.annihilatorIdeal F).subscheme.Modules)
    (e : (Scheme.Modules.pushforward
      (Scheme.Modules.annihilatorIdeal F).subschemeι).obj G ≅ F) :
    G ≅ (Scheme.Modules.pullback (Scheme.Modules.annihilatorIdeal F).subschemeι).obj F :=
  (Stacks.ClosedImmersion.fullyFaithfulPushforward _).preimageIso
    (e ≪≫ (pushforwardPullbackAnnihilatorIso F).symm)

private instance isFiniteType_pullback_annihilatorIdeal :
    ((Scheme.Modules.pullback
      (Scheme.Modules.annihilatorIdeal F).subschemeι).obj F).IsFiniteType :=
  SheafOfModules.pullback_isFiniteType
    (Scheme.Modules.annihilatorIdeal F).subschemeι.toLRSHom.toShHom F

/-- A quasi-coherent module of finite type is the direct image of a quasi-coherent module of
finite type on its scheme-theoretic support. -/
private theorem exists_module_on_annihilatorIdeal :
    ∃ G : (Scheme.Modules.annihilatorIdeal F).subscheme.Modules,
      G.IsQuasicoherent ∧ G.IsFiniteType ∧
        Nonempty ((Scheme.Modules.pushforward
          (Scheme.Modules.annihilatorIdeal F).subschemeι).obj G ≅ F) :=
  ⟨(Scheme.Modules.pullback (Scheme.Modules.annihilatorIdeal F).subschemeι).obj F,
    inferInstance, inferInstance, ⟨pushforwardPullbackAnnihilatorIso F⟩⟩

/-- **A quasi-coherent module of finite type is the direct image of a quasi-coherent module of
finite type on its scheme-theoretic support** (part of [Stacks, Tag 05JU]). -/
alias exists_isQuasicoherent_isFiniteType_pushforward_annihilatorIdeal :=
  exists_module_on_annihilatorIdeal

/-- Every closed subscheme of `X` from which `F` is a direct image contains the
scheme-theoretic support of `F`. -/
private theorem annihilatorIdeal_isSmallest (J : X.IdealSheafData)
    (G : J.subscheme.Modules)
    (e : (Scheme.Modules.pushforward J.subschemeι).obj G ≅ F) :
    J ≤ Scheme.Modules.annihilatorIdeal F := by
  have hkill :=
    (Stacks.ClosedImmersion.pushforward_essImage_iff J.subschemeι F).mp ⟨G, ⟨e⟩⟩
  refine Scheme.IdealSheafData.le_def.mpr fun U a ha ↦ ?_
  rw [annihilatorIdeal_ideal F U]
  refine Module.mem_annihilator.mpr fun m ↦ hkill U.1 a ?_ m
  exact RingHom.mem_ker.mp (by rw [J.ker_subschemeι_app U]; exact ha)

/-- Every descent of `F` to its scheme-theoretic support is of finite type. -/
private theorem module_on_annihilatorIdeal_isFiniteType
    (G : (Scheme.Modules.annihilatorIdeal F).subscheme.Modules)
    (e : (Scheme.Modules.pushforward
      (Scheme.Modules.annihilatorIdeal F).subschemeι).obj G ≅ F) :
    G.IsFiniteType :=
  isFiniteType_of_scheme_iso (isoPullback_of_pushforwardIso_annihilatorIdeal F G e).symm


/-- The support of `F` is the closed set underlying its scheme-theoretic support. -/
private theorem supp_eq_support_annihilatorIdeal :
    SheafOfModules.supp F = ((Scheme.Modules.annihilatorIdeal F).support : Set X) := by
  ext x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hsec := Scheme.Modules.mem_support_sections_iff_mem_supp F ⟨U, hU⟩ x hxU
  have hloc := mem_zeroLocus_annihilator_iff F ⟨U, hU⟩ hxU
  have hsupp : x ∈ (Scheme.Modules.annihilatorIdeal F).support ↔
      x ∈ X.zeroLocus (U := U) (Module.annihilator Γ(X, U) Γ(F, U)) := by
    rw [← annihilatorIdeal_ideal F ⟨U, hU⟩]
    exact Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU
  exact hsec.symm.trans (hloc.symm.trans hsupp.symm)

/-! ### Sections of an invertible module over an affine open -/

/-- An invertible module on a scheme is finite locally free of rank one, in the form of Tag
01C6 (3). -/
private theorem sheafRank_one_of_isInvertible (Y : Scheme.{u}) (L : Y.Modules)
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property L) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
  (Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one Y L).mp
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr h)

/-- A module which is finite locally free of some rank is quasi-coherent. -/
private theorem isQuasicoherent_of_sheafRank {Y : Scheme.{u}} (L : Y.Modules) (r : ℕ)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L r) :
    L.IsQuasicoherent := by
  obtain ⟨q, hfree, -⟩ := h.exists_isFiniteLocallyFreeOfRankData
  let : q.IsLocallyFreeData := hfree
  exact q.quasiCoherentData.isQuasicoherent

/-- The module of sections of a quasi-coherent module of rank one over an affine open is an
invertible module over the functions on that open. -/
private theorem invertible_sections_of_rank_one {Y : Scheme.{u}} (L : Y.Modules)
    [L.IsQuasicoherent] (h : L.IsFiniteLocallyFreeOfRank 1) (U : Y.affineOpens) :
    Module.Invertible Γ(Y, U.1) Γ(L, U.1) := by
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  refine Stacks.PicardUFD.invertible_of_isFiniteLocallyFreeOfRank_one
    ((_root_.tilde_isFiniteLocallyFreeOfRank_iff Γ(Y, U.1) Γ(L, U.1) 1).mp ?_)
  exact IsFiniteLocallyFreeOfRank.of_iso
    (Stacks.Modules.tildeIsoRestrictFromSpec L U.2).symm
    (IsFiniteLocallyFreeOfRank.restrict U.2.fromSpec h)

/-! ### An invertible direct image supported finitely over the base -/

/-- The underlying map of a section `s` of `f` is a right inverse of the underlying map of `f`. -/
private theorem base_section_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (y : Y) : f.base (s.base y) = y := by
  simpa [Scheme.Hom.comp_base] using congrArg (fun q : Y ⟶ Y => q.base y) hs

/-- A section of a separated morphism is a closed immersion. -/
private theorem isClosedImmersion_of_section {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    [IsSeparated f] (hs : s ≫ f = 𝟙 Y) : IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ f) := by
    rw [hs]
    infer_instance
  exact IsClosedImmersion.of_comp (f := s) (g := f)

/-- An invertible module is finite locally free of rank one and quasi-coherent. -/
private theorem isFiniteLocallyFreeOfRank_one_and_isQuasicoherent (Y : Scheme.{u})
    (L : Y.Modules)
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property L) :
    L.IsFiniteLocallyFreeOfRank 1 ∧ L.IsQuasicoherent :=
  have hsheaf := sheafRank_one_of_isInvertible Y L h
  ⟨isFiniteLocallyFreeOfRank_of_sheafOfModules L 1 hsheaf,
    isQuasicoherent_of_sheafRank L 1 hsheaf⟩

/-- An affine morphism which is bijective on the functions of every affine open of the target is
an isomorphism. -/
private theorem isIso_of_affineOpen_app_bijective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f]
    (h : ∀ U : Y.Opens, IsAffineOpen U → Function.Bijective (f.app U).hom) : IsIso f := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro y
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : IsIso (f.app U) := (ConcreteCategory.isIso_iff_bijective _).mpr (h U hU)
  exact ⟨U, hyU, (isIso_morphismRestrict_iff_isIso_app (f := f) hU).2 this⟩

/-- If a module `F` on `X` is the direct image of a module on a scheme `Z` mapping
isomorphically to `Y` over `f`, then `f` has a section `s` and `F` is the direct image of
`f_* F` along `s`. -/
private theorem exists_section_iso_of_isIso_map
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (k : Z ⟶ X)
    (F : X.Modules) (G : Z.Modules)
    (e : (Scheme.Modules.pushforward k).obj G ≅ F)
    (h : IsIso (k ≫ f)) :
    ∃ s : Y ⟶ X, s ≫ f = 𝟙 Y ∧
      Nonempty (F ≅ (Scheme.Modules.pushforward s).obj
        ((Scheme.Modules.pushforward f).obj F)) := by
  let g := k ≫ f
  let : IsIso g := h
  let s : Y ⟶ X := inv g ≫ k
  have hs : s ≫ f = 𝟙 Y := by simp [s, g]
  let eL : (Scheme.Modules.pushforward g).obj G ≅ (Scheme.Modules.pushforward f).obj F :=
    ((Scheme.Modules.pushforwardComp k f).app G).symm ≪≫
      (Scheme.Modules.pushforward f).mapIso e
  let eZG : (Scheme.Modules.pushforward (inv g)).obj ((Scheme.Modules.pushforward f).obj F) ≅ G :=
    (Scheme.Modules.pushforward (inv g)).mapIso eL.symm ≪≫
      (Scheme.Modules.pushforwardComp g (inv g)).app G ≪≫
      (Scheme.Modules.pushforwardCongr (by simp : g ≫ inv g = 𝟙 _)).app G ≪≫
      (Scheme.Modules.pushforwardId _).app G
  exact ⟨s, hs, ⟨e.symm ≪≫ (Scheme.Modules.pushforward k).mapIso eZG.symm ≪≫
    (Scheme.Modules.pushforwardComp (inv g) k).app ((Scheme.Modules.pushforward f).obj F)⟩⟩

/-- An algebra map is bijective when the algebra acts faithfully on a module which is invertible
over the base ring. -/
private theorem algebraMap_bijective_of_faithful_invertible
    {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [SMulCommClass B A M] [Module.Invertible A M] [FaithfulSMul B M] :
    Function.Bijective (algebraMap A B) := by
  constructor
  · refine fun a₁ a₂ h ↦ (Module.Invertible.toModuleEnd_bijective A M).1 (LinearMap.ext fun m ↦ ?_)
    change a₁ • m = a₂ • m
    simpa only [IsScalarTower.algebraMap_smul] using congrArg (fun b : B => b • m) h
  · intro b
    obtain ⟨a, ha⟩ := (Module.Invertible.toModuleEnd_bijective A M).2
      (Module.toModuleEnd A (S := B) M b)
    have hact : ∀ m : M, b • m = (algebraMap A B a) • m := by
      intro m
      have hm := congrArg (fun φ : Module.End A M => φ m) ha
      change a • m = b • m at hm
      simpa only [IsScalarTower.algebraMap_smul] using hm.symm
    exact ⟨a, (FaithfulSMul.eq_of_smul_eq_smul hact).symm⟩

/-- A descent of `F` to its scheme-theoretic support has vanishing annihilator ideal sheaf: its
own scheme-theoretic support is a closed subscheme of `X` from which `F` is a direct image, so
minimality forces it to be everything. -/
private theorem annihilatorIdeal_on_support_eq_bot
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (G : (Scheme.Modules.annihilatorIdeal F).subscheme.Modules) [G.IsQuasicoherent]
    (e : (Scheme.Modules.pushforward
      (Scheme.Modules.annihilatorIdeal F).subschemeι).obj G ≅ F) :
    Scheme.Modules.annihilatorIdeal G = ⊥ := by
  let I := Scheme.Modules.annihilatorIdeal F
  let : G.IsFiniteType := module_on_annihilatorIdeal_isFiniteType F G e
  let K := Scheme.Modules.annihilatorIdeal G
  let k := K.subschemeι
  let j : K.subscheme ⟶ X := k ≫ I.subschemeι
  let J := j.ker
  obtain ⟨G', hG'qc, _, ⟨e'⟩⟩ := exists_module_on_annihilatorIdeal G
  let : G'.IsQuasicoherent := hG'qc
  let eJ : K.subscheme ≅ J.subscheme := asIso j.toImage
  let GJ : J.subscheme.Modules := (Scheme.Modules.pushforward eJ.hom).obj G'
  let : GJ.IsQuasicoherent := inferInstance
  have hfac : eJ.hom ≫ J.subschemeι = j := j.toImage_imageι
  let eJpush : (Scheme.Modules.pushforward J.subschemeι).obj GJ ≅
      (Scheme.Modules.pushforward j).obj G' :=
    (Scheme.Modules.pushforwardComp eJ.hom J.subschemeι).app G' ≪≫
      (Scheme.Modules.pushforwardCongr hfac).app G'
  let eF : (Scheme.Modules.pushforward J.subschemeι).obj GJ ≅ F :=
    eJpush ≪≫ ((Scheme.Modules.pushforwardComp k I.subschemeι).app G').symm ≪≫
      (Scheme.Modules.pushforward I.subschemeι).mapIso e' ≪≫ e
  have hsmall : J ≤ I := annihilatorIdeal_isSmallest F J GJ eF
  have hlarge : I ≤ J := by
    rw [← I.ker_subschemeι]
    exact Scheme.Hom.le_ker_comp k I.subschemeι
  have hker : j.ker = I.subschemeι.ker := (le_antisymm hsmall hlarge).trans I.ker_subschemeι.symm
  have hkIso : IsIso k :=
    IsClosedImmersion.isIso_of_ker_eq j I.subschemeι k (by rfl) hker
  rw [show Scheme.Modules.annihilatorIdeal G = K from rfl, ← K.ker_subschemeι]
  exact Scheme.Hom.ker_eq_bot_of_isIso k

/-- Let `f : X ⟶ Y` be a separated morphism of finite type and let `F` be a quasi-coherent
`𝒪_X`-module of finite type whose scheme-theoretic support is finite over `Y`. If the direct
image `f_* F` is invertible, then `f` admits a section `s`, and `F` is the direct image along `s`
of `f_* F`. -/
@[stacks 0FZP]
public theorem exists_section_iso_pushforward_of_invertible_pushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    [IsFinite ((Scheme.Modules.annihilatorIdeal F).subschemeι ≫ f)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property
      ((Scheme.Modules.pushforward f).obj F)] :
    ∃ s : Y ⟶ X, s ≫ f = 𝟙 Y ∧
      Nonempty (F ≅ (Scheme.Modules.pushforward s).obj
        ((Scheme.Modules.pushforward f).obj F)) := by
  classical
  let I := Scheme.Modules.annihilatorIdeal F
  let i := I.subschemeι
  obtain ⟨G, hGqc, hGft, ⟨e⟩⟩ := exists_module_on_annihilatorIdeal F
  let : G.IsQuasicoherent := hGqc
  let : G.IsFiniteType := hGft
  let g : I.subscheme ⟶ Y := i ≫ f
  let L : Y.Modules := (Scheme.Modules.pushforward f).obj F
  let H : Y.Modules := (Scheme.Modules.pushforward g).obj G
  let eH : H ≅ L := ((Scheme.Modules.pushforwardComp i f).app G).symm ≪≫
    (Scheme.Modules.pushforward f).mapIso e
  obtain ⟨hLrank, hLqc⟩ := isFiniteLocallyFreeOfRank_one_and_isQuasicoherent Y L inferInstance
  have hHrank : H.IsFiniteLocallyFreeOfRank 1 :=
    IsFiniteLocallyFreeOfRank.of_iso eH.symm hLrank
  let : L.IsQuasicoherent := hLqc
  let : H.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso eH.symm inferInstance
  have hIso : IsIso g := by
    apply isIso_of_affineOpen_app_bijective g
    intro U hU
    let V : I.subscheme.Opens := g ⁻¹ᵁ U
    let A := Γ(Y, U)
    let B := Γ(I.subscheme, V)
    let M := Γ(G, V)
    let Vaff : I.subscheme.affineOpens := ⟨V, hU.preimage g⟩
    let : Algebra A B := (g.app U).hom.toAlgebra
    let : Module B M := inferInstance
    let : Module A M := Module.compHom (M := M) (algebraMap A B)
    let : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let : SMulCommClass B A M := inferInstance
    have hInvM : Module.Invertible A M := by
      change Module.Invertible A Γ(H, U)
      exact invertible_sections_of_rank_one H hHrank ⟨U, hU⟩
    let : Module.Invertible A M := hInvM
    have hAnn : Module.annihilator B M = ⊥ := by
      rw [← annihilatorIdeal_ideal G Vaff, annihilatorIdeal_on_support_eq_bot F G e]
      simp
    let : FaithfulSMul B M := Module.annihilator_eq_bot.mp hAnn
    change Function.Bijective (g.app U).hom
    exact algebraMap_bijective_of_faithful_invertible (A := A) (B := B) (M := M)
  exact exists_section_iso_of_isIso_map f i F G e hIso

/-! ### A module supported on a section -/

/-- The annihilator of an invertible module vanishes. -/
private theorem annihilator_eq_bot_of_invertible (R M : Type u) [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Invertible R M] : Module.annihilator R M = ⊥ := by
  refine le_antisymm (fun a ha => ?_) bot_le
  have h : Module.toModuleEnd R M a = Module.toModuleEnd R M (0 : R) := by
    ext m
    simpa using Module.mem_annihilator.mp ha m
  simpa using (Module.Invertible.toModuleEnd_bijective R M).injective h

/-- The support of a quasi-coherent module of rank one is the whole scheme: over an affine open
its sections form an invertible module, whose annihilator vanishes. -/
private theorem supp_eq_univ_of_rank_one {Y : Scheme.{u}} (L : Y.Modules) [L.IsQuasicoherent]
    (h : L.IsFiniteLocallyFreeOfRank 1) : SheafOfModules.supp L = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  let : Module.Invertible Γ(Y, U) Γ(L, U) := invertible_sections_of_rank_one L h ⟨U, hU⟩
  have hsupp : Module.support Γ(Y, U) Γ(L, U) = Set.univ := by
    rw [Module.support_eq_zeroLocus, annihilator_eq_bot_of_invertible]
    simp
  exact (mem_support_sections_iff_mem_supp L ⟨U, hU⟩ y hyU).mp (hsupp ▸ Set.mem_univ _)

/-- The image of a closed immersion lies in the support of the direct image of a module whose
own support is everything. -/
private theorem range_subset_supp_pushforward
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (M : Z.Modules)
    (hM : SheafOfModules.supp M = Set.univ) :
    Set.range i.base ⊆ SheafOfModules.supp ((Scheme.Modules.pushforward i).obj M) := by
  intro x hx
  obtain ⟨z, rfl⟩ := hx
  refine (SheafOfModules.mem_supp_iff_nontrivial_stalk
    ((Scheme.Modules.pushforward i).obj M) (i.base z)).mpr ?_
  have hnt : Nontrivial (((Scheme.Modules.toPresheaf Z).obj M).stalk z) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk M z).mp (hM ▸ Set.mem_univ z)
  let α := ((Scheme.Modules.toPresheaf Z).obj M).stalkPushforward Ab.{u} i.base z
  have hα : IsIso α :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Ab.{u}
      i.isClosedEmbedding.isInducing _ z
  have hinj : Function.Injective (ConcreteCategory.hom (asIso α).inv) :=
    (ConcreteCategory.bijective_of_isIso (asIso α).inv).1
  obtain ⟨a, b, hab⟩ := @exists_pair_ne _ hnt
  exact ⟨ConcreteCategory.hom (asIso α).inv a, ConcreteCategory.hom (asIso α).inv b,
    fun h => hab (hinj h)⟩

/-- A closed subscheme whose points lie on a section of a separated morphism of finite type is
finite over the base: it is injective over the base, hence locally quasi-finite, and the base
change of the section is a closed immersion through which the base change of the subscheme
factors, so the morphism is universally closed. -/
private theorem finite_of_range_subset_section {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) (f : X ⟶ Y) (s : Y ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion s] [IsSeparated f]
    [LocallyOfFiniteType (i ≫ f)]
    (hs : s ≫ f = 𝟙 Y)
    (hsub : Set.range i.base ⊆ Set.range s.base) : IsFinite (i ≫ f) := by
  have hinj : Function.Injective (i ≫ f).base := by
    intro a b hab
    obtain ⟨ya, hya⟩ := hsub ⟨a, rfl⟩
    obtain ⟨yb, hyb⟩ := hsub ⟨b, rfl⟩
    have hh : f.base (i.base a) = f.base (i.base b) := by
      simpa [Scheme.Hom.comp_base] using hab
    have hyab : ya = yb := by
      rw [← base_section_apply f s hs ya, ← base_section_apply f s hs yb, hya, hyb]
      exact hh
    apply_fun s.base at hyab
    rw [hya, hyb] at hyab
    exact (Scheme.Hom.isClosedEmbedding i).injective hyab
  have hqf : LocallyQuasiFinite (i ≫ f) := LocallyQuasiFinite.of_injective (f := i ≫ f) hinj
  have huc : UniversallyClosed (i ≫ f) := by
    rw [universallyClosed_eq]
    apply MorphismProperty.universally_mk' (P := topologically @IsClosedMap) (i ≫ f)
    intro T g _
    let XT := Limits.pullback g f
    let qT : XT ⟶ T := pullback.fst g f
    let qX : XT ⟶ X := pullback.snd g f
    let P := Limits.pullback qX i
    let j : P ⟶ XT := pullback.fst qX i
    let l : P ⟶ Z := pullback.snd qX i
    let r : P ⟶ T := j ≫ qT
    let k : T ⟶ XT := pullback.lift (𝟙 T) (g ≫ s) (by simp [hs])
    have hkT : k ≫ qT = 𝟙 T := by
      dsimp [k, qT]
      rw [pullback.lift_fst]
    have hkX : k ≫ qX = g ≫ s := by
      dsimp [k, qX]
      rw [pullback.lift_snd]
    have hkT' (t : T) : qT.base (k.base t) = t := by
      change (k ≫ qT).base t = t
      rw [hkT]
      rfl
    have : IsClosedImmersion (k ≫ qT) := by rw [hkT]; infer_instance
    have : IsClosedImmersion k := IsClosedImmersion.of_comp k qT
    have hXT : pullback.fst qX s ≫ qT ≫ k = pullback.fst qX s := by
      apply pullback.hom_ext (f := g) (g := f)
      · calc
          (pullback.fst qX s ≫ qT ≫ k) ≫ qT =
              (pullback.fst qX s ≫ qT) ≫ (k ≫ qT) := Category.assoc _ _ _
          _ = pullback.fst qX s ≫ qT := by rw [hkT, Category.comp_id]
      · change (pullback.fst qX s ≫ qT ≫ k) ≫ qX = pullback.fst qX s ≫ qX
        calc
          (pullback.fst qX s ≫ qT ≫ k) ≫ qX =
              pullback.fst qX s ≫ qT ≫ (k ≫ qX) := by simp
          _ = pullback.fst qX s ≫ qT ≫ (g ≫ s) := by rw [hkX]
          _ = pullback.fst qX s ≫ qX := by
            calc
              pullback.fst qX s ≫ qT ≫ (g ≫ s) =
                  pullback.fst qX s ≫ (qT ≫ g) ≫ s := by simp
              _ = pullback.fst qX s ≫ (qX ≫ f) ≫ s := by rw [pullback.condition]
              _ = pullback.fst qX s ≫ qX := by
                change (pullback.fst qX s ≫ (qX ≫ f)) ≫ s =
                  pullback.fst qX s ≫ qX
                calc
                  (pullback.fst qX s ≫ (qX ≫ f)) ≫ s =
                      ((pullback.fst qX s ≫ qX) ≫ f) ≫ s := by simp
                  _ = ((pullback.snd qX s ≫ s) ≫ f) ≫ s := by rw [pullback.condition]
                  _ = pullback.snd qX s ≫ s := by simp [Category.assoc, hs]
                  _ = pullback.fst qX s ≫ qX := pullback.condition.symm
    let e : T ≅ Limits.pullback qX s := {
      hom := pullback.lift k g hkX
      inv := pullback.fst qX s ≫ qT
      hom_inv_id := by
        change (pullback.lift k g hkX ≫ pullback.fst qX s) ≫ qT = 𝟙 T
        rw [pullback.lift_fst, hkT]
      inv_hom_id := by
        apply pullback.hom_ext
        · change (pullback.fst qX s ≫ qT ≫ pullback.lift k g hkX) ≫
            pullback.fst qX s = pullback.fst qX s
          calc
            (pullback.fst qX s ≫ qT ≫ pullback.lift k g hkX) ≫ pullback.fst qX s =
                pullback.fst qX s ≫ qT ≫
                  (pullback.lift k g hkX ≫ pullback.fst qX s) := by simp
            _ = pullback.fst qX s ≫ qT ≫ k := by rw [pullback.lift_fst]
            _ = pullback.fst qX s := hXT
        · change pullback.fst qX s ≫ qT ≫ pullback.lift k g hkX ≫
            pullback.snd qX s = pullback.snd qX s
          rw [pullback.lift_snd]
          calc
            pullback.fst qX s ≫ qT ≫ g = pullback.fst qX s ≫ qX ≫ f := by
              calc
                pullback.fst qX s ≫ qT ≫ g = pullback.fst qX s ≫ (qT ≫ g) := by simp
                _ = pullback.fst qX s ≫ (qX ≫ f) := by rw [pullback.condition]
                _ = pullback.fst qX s ≫ qX ≫ f := by simp
            _ = pullback.snd qX s := by
              change (pullback.fst qX s ≫ qX) ≫ f = pullback.snd qX s
              rw [pullback.condition]
              simp [Category.assoc, hs]
    }
    have he₁ : e.hom ≫ pullback.fst qX s = k := by
      change pullback.lift k g hkX ≫ pullback.fst qX s = k
      exact pullback.lift_fst k g hkX
    have he₂ : e.hom ≫ pullback.snd qX s = g := by
      change pullback.lift k g hkX ≫ pullback.snd qX s = g
      exact pullback.lift_snd k g hkX
    have hsq : IsPullback k g qX s := IsPullback.of_iso_pullback ⟨hkX⟩ e he₁ he₂
    have hkRange : Set.range k.base = qX.base ⁻¹' Set.range s.base := by
      calc
        Set.range k.base = Set.range ((pullback.fst qX s).base ∘ e.hom.base) := by
          congr 1
          ext x
          exact (congrArg (fun m : T ⟶ XT => m.base x) he₁).symm
        _ = Set.range (pullback.fst qX s).base := by
          have hsurj : Function.Surjective e.hom.base := by
            intro x
            have hinv : e.inv.base ≫ e.hom.base = 𝟙 _ :=
              congrArg (fun m : Limits.pullback qX s ⟶ Limits.pullback qX s => m.base) e.inv_hom_id
            refine ⟨e.inv.base x, ?_⟩
            change (e.inv.base ≫ e.hom.base) x = x
            simp
          rw [Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
        _ = qX.base ⁻¹' Set.range s.base := Scheme.Pullback.range_fst qX s
    have hjRange : Set.range j.base = qX.base ⁻¹' Set.range i.base :=
      Scheme.Pullback.range_fst qX i
    have hjSub : Set.range j.base ⊆ Set.range k.base := by
      rw [hjRange, hkRange]
      exact Set.preimage_mono hsub
    have hfac (z : P) : j.base z = k.base (r.base z) := by
      obtain ⟨t, ht⟩ := hjSub ⟨z, rfl⟩
      have ht' : k.base t = j.base z := ht
      have hrt : r.base z = t := by
        have hqt : qT.base (j.base z) = t := by rw [← ht']; exact hkT' t
        simpa [r, Scheme.Hom.comp_base] using hqt
      rw [hrt]
      exact ht'.symm
    have hsqP : IsPullback r l g (i ≫ f) := by
      dsimp [r, l, j, P, XT, qT, qX]
      exact (IsPullback.of_hasPullback (pullback.snd g f) i).paste_horiz
        (IsPullback.of_hasPullback g f)
    have hr : IsClosedMap r.base := by
      intro C hC
      have hj : IsClosed (j.base '' C) := (Scheme.Hom.isClosedEmbedding j).isClosedMap C hC
      have himg : r.base '' C = k.base ⁻¹' (j.base '' C) := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          simp only [Set.mem_preimage, Set.mem_image]
          exact ⟨z, hz, hfac z⟩
        · intro hy
          simp only [Set.mem_preimage, Set.mem_image] at hy
          obtain ⟨z, hz, hzy⟩ := hy
          refine ⟨z, hz, ?_⟩
          have hqt : qT.base (j.base z) = y := by rw [hzy]; exact hkT' y
          simpa [r, Scheme.Hom.comp_base] using hqt
      rw [himg]
      exact hj.preimage (Scheme.Hom.continuous k)
    have hcanon : IsClosedMap (pullback.fst g (i ≫ f)).base := by
      have hcomp : topologically @IsClosedMap
          (hsqP.isoPullback.hom ≫ pullback.fst g (i ≫ f)) := by
        change IsClosedMap (hsqP.isoPullback.hom ≫ pullback.fst g (i ≫ f)).base
        simpa [hsqP.isoPullback_hom_fst] using hr
      have h := MorphismProperty.cancel_left_of_respectsIso
        (P := topologically @IsClosedMap) hsqP.isoPullback.hom
        (pullback.fst g (i ≫ f))
      exact h.mp (by simpa [Scheme.Hom.comp_base] using hcomp)
    change IsClosedMap (pullback.fst g (i ≫ f)).base
    exact hcanon
  let : UniversallyClosed (i ≫ f) := huc
  let : LocallyOfFiniteType (i ≫ f) := inferInstance
  let : IsProper (i ≫ f) := IsProper.mk
  let : LocallyQuasiFinite (i ≫ f) := hqf
  exact (IsFinite.iff_isProper_and_locallyQuasiFinite (i ≫ f)).2 ⟨inferInstance, inferInstance⟩

/-- A reduced closed subscheme is the vanishing-ideal subscheme of its support. -/
private alias ker_eq_vanishingIdeal_of_reduced_closed_immersion :=
  AlgebraicGeometry.ker_eq_vanishingIdeal_of_reduced_closed_immersion

/-- Let `f : X ⟶ Y` be a separated morphism of finite type with a section `s`, and let `Y` be
reduced. A quasi-coherent `𝒪_X`-module `F` of finite type supported on the image of `s` and with
invertible direct image `f_* F` is the direct image along `s` of `f_* F`. -/
@[stacks 0FZQ]
public theorem iso_pushforward_section_of_invertible_pushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (hs : s ≫ f = 𝟙 Y) [IsReduced Y]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hsupp : SheafOfModules.supp F ⊆ Set.range s.base)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property
      ((Scheme.Modules.pushforward f).obj F)] :
    Nonempty (F ≅ (Scheme.Modules.pushforward s).obj
      ((Scheme.Modules.pushforward f).obj F)) := by
  have : IsClosedImmersion s := isClosedImmersion_of_section f s hs
  let I := Scheme.Modules.annihilatorIdeal F
  have hsub : Set.range I.subschemeι.base ⊆ Set.range s.base := by
    rw [show Set.range I.subschemeι.base = (I.support : Set X) from I.range_subschemeι,
      ← supp_eq_support_annihilatorIdeal F]
    exact hsupp
  have : LocallyOfFiniteType (I.subschemeι ≫ f) := inferInstance
  let : IsFinite (I.subschemeι ≫ f) :=
    finite_of_range_subset_section I.subschemeι f s hs hsub
  obtain ⟨s', hs', ⟨e⟩⟩ := exists_section_iso_pushforward_of_invertible_pushforward f F
  have : IsClosedImmersion s' := isClosedImmersion_of_section f s' hs'
  let L := (Scheme.Modules.pushforward f).obj F
  obtain ⟨hLrank, hLqc⟩ := isFiniteLocallyFreeOfRank_one_and_isQuasicoherent Y L inferInstance
  let : L.IsQuasicoherent := hLqc
  have hLsupp : SheafOfModules.supp L = Set.univ := supp_eq_univ_of_rank_one L hLrank
  have hrangePush : Set.range s'.base ⊆
      SheafOfModules.supp ((Scheme.Modules.pushforward s').obj L) :=
    range_subset_supp_pushforward s' L hLsupp
  have hsuppIso : SheafOfModules.supp F =
      SheafOfModules.supp ((Scheme.Modules.pushforward s').obj L) :=
    SheafOfModules.supp_eq_of_iso e
  have hrange : Set.range s'.base ⊆ Set.range s.base :=
    (hrangePush.trans hsuppIso.symm.subset).trans hsupp
  have hpoint (y : Y) : s'.base y = s.base y := by
    obtain ⟨z, hz⟩ := hrange ⟨y, rfl⟩
    have hzy : z = y := by
      rw [← base_section_apply f s hs z, hz, base_section_apply f s' hs']
    subst z
    exact hz.symm
  have hrangeEq : Set.range s'.base = Set.range s.base :=
    hrange.antisymm (Set.range_subset_iff.2 fun y ↦ ⟨y, hpoint y⟩)
  have hkerSupport : s'.ker.support = s.ker.support := by
    apply SetLike.coe_injective
    calc
      s'.ker.support = closure (Set.range s'.base) := Scheme.Hom.support_ker s'
      _ = closure (Set.range s.base) := congrArg closure hrangeEq
      _ = s.ker.support := (Scheme.Hom.support_ker s).symm
  have hker : s'.ker = s.ker := by
    rw [ker_eq_vanishingIdeal_of_reduced_closed_immersion s',
      ker_eq_vanishingIdeal_of_reduced_closed_immersion s, hkerSupport]
  let t := IsClosedImmersion.lift s s' hker.symm.le
  have ht : t ≫ s = s' := IsClosedImmersion.lift_fac s s' hker.symm.le
  have htId : t = 𝟙 Y := by
    calc
      t = t ≫ (s ≫ f) := by rw [hs]; simp
      _ = s' ≫ f := by simpa only [Category.assoc] using congrArg (· ≫ f) ht
      _ = 𝟙 Y := hs'
  have hsections : s' = s := by simpa [htId] using ht.symm
  exact ⟨hsections ▸ e⟩

end AlgebraicGeometry.Scheme.Modules

end
