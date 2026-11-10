module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.BigSiteModuleInjectives
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionExactness
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCoreflection
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PushforwardIndexIso
public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.Algebra.Homology.RightDerivedBiprod
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.InjectiveRestrictionAlongAMono
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AcyclicityForAContinuousPushforward
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-!
# Cohomology along a family of objects of a big site, as module-valued functors

Let `C` be a chosen big `τ`-site over a scheme `T`, let `A` be a ring and let `𝒟` be the
`A`-algebras whose spectra lie below a cutoff `κ`. A functor `W : 𝒟ᵒᵖ ⥤ C` together with a
compatible family of ring maps `B ⟶ Γ(W(B))` turns every sheaf of `𝒪`-modules `𝓖` on `C` into a
module-valued functor on `𝒟`,

`B ↦ 𝓖(W(B))`,

and so the right derived functors of `𝓖 ↦ (B ↦ 𝓖(W(B)))` are module-valued functors
`B ↦ H^q(W(B), 𝓖)` on `𝒟`. This module proves the cohomological half of [Stacks, Tag 06VR]
for such families:

* if every `W(B)` is affine and `𝓖` is adequate, these functors vanish in positive degrees,
  which is [Stacks, Tag 06VM] (3) at each `W(B)`;
* for the family of the preimages of the opens `U` of an object `X` the family maps to, a
  Mayer–Vietoris sequence relates the functors of `U ∪ V`, of `U`, of `V` and of `U ∩ V`, and
  the induction principle of [Stacks, Tag 08DR] then makes all of them adequate as soon as they
  are adequate in degree zero on the affine opens: this is Cases I–III of the source's proof.

## Main definitions

* `Stacks.Adequate.sectionsAlong` — the functor `𝓖 ↦ (B ↦ 𝓖(W(B)))`.
* `Stacks.Adequate.openFamily` — for a family mapping to an object `X` of the site and an open
  `U` of `X`, the family `B ↦ W(B) ×_X U` of the preimages of `U`.
* `Stacks.Adequate.openFamilyRestriction` — the restriction from the family of `U` to the family
  of `V ⊆ U`.

## Main results

* `Stacks.Adequate.isZero_rightDerived_sectionsAlong` — the derived functors vanish as soon as
  the cohomology of `𝓖` vanishes at every `W(B)`.
* `Stacks.Adequate.isZero_rightDerived_evaluation_of_isAdequate` — the cohomology of an adequate
  module over an affine object of the site, computed in sheaves of modules, vanishes in positive
  degrees: [Stacks, Tag 06VM] (3) read through [Stacks, Tag 03FD].
* `Stacks.Adequate.prop_rightDerived_of_mayerVietoris` — for a square of additive functors which
  is a pullback, with an epimorphic edge, on injectives, the right derived functors of its corner
  take values in a weak Serre class as soon as those of the other three corners do.
* `Stacks.Adequate.isPullback_openFamilyRestriction` and
  `Stacks.Adequate.epi_openFamilyRestriction_of_injective` — the sections over the preimages of
  two opens form such a square ([Stacks, Tag 093X] for the epimorphism).
* `Stacks.Adequate.prop_rightDerived_openFamilySections` — **the induction of the source's
  proof**: over a quasi-separated `X`, the derived sections over the preimages of every
  quasi-compact open take values in a weak Serre class as soon as those over the affine opens do.
* `Stacks.Adequate.openFamilySectionsTopIso` — the preimages of `⊤` are the family itself.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {T : Scheme.{u}} (C : BigSite τ T) {A : CommRingCat.{u}}
  {κ : Cardinal.{u}}

/-- Sections over an object of the site are additive, `SheafOfModules.evaluation_additive` at
the structure sheaf of the site; recorded locally so that instance search sees it at the
universe of the site's modules. -/
local instance evaluation_additive_site (Y : C.categoryᵒᵖ) :
    (_root_.SheafOfModules.evaluation.{u} C.structureSheaf Y).Additive :=
  SheafOfModules.evaluation_additive _ _

/-! ### Sections along a family of objects -/

section SectionsAlong

variable (W : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow κ))ᵒᵖ ⥤ C.category)
  (φ : AdequateFunctor.algebraRingDiagramOn
      (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow κ)) ⟶
    W.op ⋙ C.structureSheaf.obj)

/-- **The sections of a sheaf of modules along a family of objects of the site**, as a
module-valued functor on the algebras: `𝓖 ↦ (B ↦ 𝓖(W(B)))`, each `𝓖(W(B))` a `B`-module through
the ring map `φ`. -/
public abbrev sectionsAlong :
    SheafOfModules.{u} C.structureSheaf ⥤
      AdequateFunctor.ModuleValuedFunctorOn.{u}
        (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow κ)) :=
  SheafOfModules.forget C.structureSheaf ⋙ PresheafOfModules.pushforward.{u} φ

/-- The sections along a family are additive: neither factor changes the underlying morphisms of
abelian groups. -/
public instance additive_sectionsAlong : (sectionsAlong C W φ).Additive where
  map_add := rfl

/-- The sections along a family preserve finite limits: both factors do, limits of presheaves of
modules being computed objectwise. -/
public instance preservesFiniteLimits_sectionsAlong :
    PreservesFiniteLimits (sectionsAlong C W φ) :=
  inferInstance

/-- **Vanishing of the derived functors of the sections along a family.** If the `q`-th derived
module-valued sections of `𝓖` vanish at every member `W(B)` of the family, then so does the
`q`-th right derived functor of `sectionsAlong` at `𝓖`: evaluation at an algebra and restriction
of scalars are exact, so they commute with the derived functors. -/
public theorem isZero_rightDerived_sectionsAlong (G : SheafOfModules.{u} C.structureSheaf) (q : ℕ)
    (h : ∀ Y, IsZero ((((_root_.SheafOfModules.evaluation C.structureSheaf (op (W.obj Y)) :
      SheafOfModules.{u} C.structureSheaf ⥤ _)).rightDerived
      q).obj G)) :
    IsZero (((sectionsAlong C W φ).rightDerived q).obj G) := by
  apply Stacks.Cohomology.ContinuousPushforward.isZero_presheafOfModules
  intro X
  let e₂ : sectionsAlong C W φ ⋙ PresheafOfModules.evaluation _ X ≅
      (_root_.SheafOfModules.evaluation C.structureSheaf (op (W.obj X.unop)) :
        SheafOfModules.{u} C.structureSheaf ⥤ _) ⋙
        ModuleCat.restrictScalars (φ.app X).hom := Iso.refl _
  refine IsZero.of_iso ?_ ((Functor.rightDerivedCompIso (sectionsAlong C W φ)
    (PresheafOfModules.evaluation _ X) q).app G).symm
  refine IsZero.of_iso ?_ ((Functor.rightDerivedIsoOfNatIso e₂ q).app G)
  let E : SheafOfModules.{u} C.structureSheaf ⥤ ModuleCat.{u} _ :=
    _root_.SheafOfModules.evaluation.{u} C.structureSheaf (op (W.obj X.unop))
  have : E.Additive := evaluation_additive_site C _
  refine IsZero.of_iso ?_ ((Functor.rightDerivedCompIso E
    (ModuleCat.restrictScalars (φ.app X).hom) q).app G)
  exact (ModuleCat.restrictScalars (φ.app X).hom).map_isZero (h X.unop)

end SectionsAlong

/-! ### Vanishing over an affine object -/

/-- **[Stacks, Tag 06VM] (3) in sheaves of modules.** The positive-degree derived functors of the
module-valued sections over an affine object of the site vanish at an adequate module. The
vanishing is [Stacks, Tag 06VM] (3) for the underlying abelian sheaf,
`Stacks.Adequate.BigSite.isZero_rightDerived_sections_of_isAdequate`; the comparison of the two
cohomologies is [Stacks, Tag 03FD] on the site, through the `Ext` description of cohomology. -/
public theorem isZero_rightDerived_evaluation_of_isAdequate
    (G : SheafOfModules.{u} C.structureSheaf) (hG : IsAdequate C G) (Y : C.category)
    [IsAffine Y.left.obj] (q : ℕ) (hq : 0 < q) :
    IsZero ((((_root_.SheafOfModules.evaluation C.structureSheaf (op Y) :
      SheafOfModules.{u} C.structureSheaf ⥤ _)).rightDerived q).obj G) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have := C.essentiallySmall_category
  have : IsGrothendieckAbelian.{u} (Sheaf C.topology AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} C.topology AddCommGrpCat.{u}
  have : HasExt.{u + 1} (Sheaf C.topology AddCommGrpCat.{u}) :=
    Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse
      (Sheaf C.topology AddCommGrpCat.{u})
  have : HasExt.{u + 1} (SheafOfModules.{u} C.structureSheaf) :=
    Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse
      (SheafOfModules.{u} C.structureSheaf)
  have : HasExt.{u} (Sheaf C.topology AddCommGrpCat.{u}) :=
    Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite C.topology
  have h₁ : IsZero (Sheaf.H'.{u} ((SheafOfModules.toSheaf C.structureSheaf).obj G) (p + 1) Y) :=
    (C.isZero_rightDerived_sections_of_isAdequate.{u, u} G hG Y (p + 1) (by omega)).of_iso
      (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSectionsOfEssentiallySmall
        C.topology _ (p + 1) Y)
  exact
    Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'_chgUniv
      C.topology C.structureSheaf Y p G h₁

/-! ### Weak Serre classes and Mayer–Vietoris squares of functors -/

section MayerVietorisDerived

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasInjectiveResolutions 𝒜]
  {ℬ : Type*} [Category* ℬ] [Abelian ℬ] (P : ObjectProperty ℬ) [P.IsWeakSerreClass]

omit [Abelian 𝒜] [HasInjectiveResolutions 𝒜] [P.IsWeakSerreClass] in
/-- The value at an object of a binary biproduct of functors is the binary biproduct of the
values: the projections and inclusions of the biproduct of functors, evaluated at the object,
form a bilimit bicone because `biprod.total` holds there. -/
public def biprodObjIso (G₁ G₂ : 𝒜 ⥤ ℬ) (X : 𝒜) : (G₁ ⊞ G₂).obj X ≅ G₁.obj X ⊞ G₂.obj X :=
  biprod.uniqueUpToIso _ _ (isBinaryBilimitOfTotal
    (BinaryBicone.mk ((G₁ ⊞ G₂).obj X) ((biprod.fst : G₁ ⊞ G₂ ⟶ G₁).app X)
      ((biprod.snd : G₁ ⊞ G₂ ⟶ G₂).app X) ((biprod.inl : G₁ ⟶ G₁ ⊞ G₂).app X)
      ((biprod.inr : G₂ ⟶ G₁ ⊞ G₂).app X)
      (by rw [← NatTrans.comp_app, biprod.inl_fst]; rfl)
      (by rw [← NatTrans.comp_app, biprod.inl_snd]; rfl)
      (by rw [← NatTrans.comp_app, biprod.inr_fst]; rfl)
      (by rw [← NatTrans.comp_app, biprod.inr_snd]; rfl))
    (by
      change (biprod.fst : G₁ ⊞ G₂ ⟶ G₁).app X ≫ (biprod.inl : G₁ ⟶ G₁ ⊞ G₂).app X +
        (biprod.snd : G₁ ⊞ G₂ ⟶ G₂).app X ≫ (biprod.inr : G₂ ⟶ G₁ ⊞ G₂).app X = 𝟙 _
      rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← NatTrans.app_add, biprod.total]
      rfl))

omit [Abelian 𝒜] [HasInjectiveResolutions 𝒜] [P.IsWeakSerreClass] in
/-- The forward map of `biprodObjIso` is the lift of the two projections evaluated at `X`. -/
@[simp] public theorem biprodObjIso_hom (G₁ G₂ : 𝒜 ⥤ ℬ) (X : 𝒜) :
    (biprodObjIso G₁ G₂ X).hom =
      biprod.lift ((biprod.fst : G₁ ⊞ G₂ ⟶ G₁).app X) ((biprod.snd : G₁ ⊞ G₂ ⟶ G₂).app X) :=
  rfl

omit [Abelian 𝒜] [HasInjectiveResolutions 𝒜] [P.IsWeakSerreClass] in
/-- The inverse map of `biprodObjIso` is the descent of the two inclusions evaluated at `X`. -/
@[simp] public theorem biprodObjIso_inv (G₁ G₂ : 𝒜 ⥤ ℬ) (X : 𝒜) :
    (biprodObjIso G₁ G₂ X).inv =
      biprod.desc ((biprod.inl : G₁ ⟶ G₁ ⊞ G₂).app X) ((biprod.inr : G₂ ⟶ G₁ ⊞ G₂).app X) :=
  rfl

variable {F G₁ G₂ H : 𝒜 ⥤ ℬ} [F.Additive] [G₁.Additive] [G₂.Additive] [H.Additive]
  (r₁ : F ⟶ G₁) (r₂ : F ⟶ G₂) (s₁ : G₁ ⟶ H) (s₂ : G₂ ⟶ H) (w : r₁ ≫ s₁ = r₂ ≫ s₂)

omit [Abelian 𝒜] [HasInjectiveResolutions 𝒜] [F.Additive] [G₁.Additive] [G₂.Additive] in
/-- The short complex `F ⟶ G₁ ⊞ G₂ ⟶ H` of a commutative square of functors, at an object `I`,
is short exact as soon as the square is a pullback at `I` and `G₁ ⟶ H` is an epimorphism there:
this is the kernel description of a pullback square in an additive category. -/
public theorem shortExact_appShortComplex_of_isPullback (I : 𝒜)
    (hpb : IsPullback (r₁.app I) (r₂.app I) (s₁.app I) (s₂.app I)) (hepi : Epi (s₁.app I)) :
    (NatTrans.appShortComplex (biprod.lift r₁ r₂) (biprod.desc s₁ (-s₂))
      (by simp [w]) I).ShortExact := by
  let e : (G₁ ⊞ G₂).obj I ≅ G₁.obj I ⊞ G₂.obj I := biprodObjIso G₁ G₂ I
  let sq : Square ℬ :=
    { X₁ := F.obj I, X₂ := G₁.obj I, X₃ := G₂.obj I, X₄ := H.obj I
      f₁₂ := r₁.app I, f₁₃ := r₂.app I, f₂₄ := s₁.app I, f₃₄ := s₂.app I
      fac := by rw [← NatTrans.comp_app, w, NatTrans.comp_app] }
  let S' : ShortComplex ℬ := ShortComplex.mk sq.kernelFork.ι (biprod.desc sq.f₂₄ (-sq.f₃₄))
    sq.kernelFork.condition
  have hS' : S'.ShortExact := by
    have hk := Square.IsPullback.isLimitKernelFork (show sq.IsPullback from hpb)
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hk)
      (Fork.IsLimit.mono hk) (epi_of_epi_fac (biprod.inl_desc _ _ : biprod.inl ≫ S'.g = s₁.app I))
  refine ShortComplex.shortExact_of_iso ?_ hS'
  refine ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) ?_ ?_
  · change 𝟙 _ ≫ (biprod.lift r₁ r₂).app I = biprod.lift (r₁.app I) (r₂.app I) ≫ e.inv
    rw [Category.id_comp, Iso.eq_comp_inv]
    apply biprod.hom_ext
    · simp only [e, biprodObjIso_hom, Category.assoc, biprod.lift_fst]
      rw [← NatTrans.comp_app, biprod.lift_fst]
    · simp only [e, biprodObjIso_hom, Category.assoc, biprod.lift_snd]
      rw [← NatTrans.comp_app, biprod.lift_snd]
  · change e.inv ≫ (biprod.desc s₁ (-s₂)).app I = biprod.desc (s₁.app I) (-s₂.app I) ≫ 𝟙 _
    rw [Category.comp_id]
    apply biprod.hom_ext'
    · change biprod.inl ≫ biprod.desc ((biprod.inl : G₁ ⟶ G₁ ⊞ G₂).app I)
        ((biprod.inr : G₂ ⟶ G₁ ⊞ G₂).app I) ≫
        (biprod.desc s₁ (-s₂)).app I = _
      rw [biprod.inl_desc_assoc, ← NatTrans.comp_app, biprod.inl_desc, biprod.inl_desc]
    · change biprod.inr ≫ biprod.desc ((biprod.inl : G₁ ⟶ G₁ ⊞ G₂).app I)
        ((biprod.inr : G₂ ⟶ G₁ ⊞ G₂).app I) ≫
        (biprod.desc s₁ (-s₂)).app I = _
      rw [biprod.inr_desc_assoc, ← NatTrans.comp_app, biprod.inr_desc, biprod.inr_desc,
        NatTrans.app_neg]

variable (hinj : ∀ I : 𝒜, Injective I →
    IsPullback (r₁.app I) (r₂.app I) (s₁.app I) (s₂.app I) ∧ Epi (s₁.app I))

include w hinj in
/-- **The Mayer–Vietoris induction step for the right derived functors of a square of
functors.** Let `F ⟶ G₁, G₂ ⟶ H` be a commutative square of additive functors which is a
pullback square, with `G₁ ⟶ H` an epimorphism, at every injective object. If all right derived
functors of `G₁`, `G₂` and `H` take a value in a weak Serre class `P` at `X`, then so do those of
`F`: they sit in the long exact sequence of right derived functors of
`0 ⟶ F ⟶ G₁ ⊞ G₂ ⟶ H ⟶ 0`, which is short exact on injectives. -/
public theorem prop_rightDerived_of_mayerVietoris (X : 𝒜)
    (h₁ : ∀ k, P ((G₁.rightDerived k).obj X)) (h₂ : ∀ k, P ((G₂.rightDerived k).obj X))
    (h₃ : ∀ k, P ((H.rightDerived k).obj X)) (n : ℕ) :
    P ((F.rightDerived n).obj X) := by
  have hz : biprod.lift r₁ r₂ ≫ biprod.desc s₁ (-s₂) = 0 := by simp [w]
  have hse : ∀ I : 𝒜, Injective I →
      (NatTrans.appShortComplex (biprod.lift r₁ r₂) (biprod.desc s₁ (-s₂)) hz I).ShortExact :=
    fun I hI => shortExact_appShortComplex_of_isPullback r₁ r₂ s₁ s₂ w I (hinj I hI).1
      (hinj I hI).2
  have hG : ∀ k, P (((G₁ ⊞ G₂).rightDerived k).obj X) := fun k =>
    P.prop_of_iso (((Functor.rightDerivedBiprodIso G₁ G₂ k).app X) ≪≫
        biprodObjIso _ _ X).symm
      (P.prop_biprod (h₁ k) (h₂ k))
  cases n with
  | zero =>
    have hmono := mono_rightDerived_zero_app (biprod.lift r₁ r₂) (biprod.desc s₁ (-s₂)) hz hse X
    have hex := (exact_rightDerived_composableArrows₅ (biprod.lift r₁ r₂)
      (biprod.desc s₁ (-s₂)) hz hse (injectiveResolution X) 0).exact 0
    have hz₀ : (NatTrans.rightDerived (biprod.lift r₁ r₂) 0).app X ≫
        (NatTrans.rightDerived (biprod.desc s₁ (-s₂)) 0).app X = 0 := by
      rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, hz, NatTrans.rightDerived_zero]
      rfl
    have hex' : (ShortComplex.mk _ _ hz₀).Exact := hex
    exact P.prop_of_isLimit_kernelFork hex'.fIsKernel (hG 0) (h₃ 0)
  | succ n =>
    have hex := (exact_rightDerived_composableArrows₅ (biprod.lift r₁ r₂)
      (biprod.desc s₁ (-s₂)) hz hse (injectiveResolution X) n).δ₀
    exact P.prop_obj₂_of_exact _ hex (hG n) (h₃ n) (hG (n + 1)) (h₃ (n + 1))

end MayerVietorisDerived

/-! ### The family of preimages of an open -/

section OpenFamily

variable (W : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow κ))ᵒᵖ ⥤ C.category)
  (X : C.category) (π : W ⟶ (Functor.const _).obj X)
  (φ : AdequateFunctor.algebraRingDiagramOn
      (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow κ)) ⟶
    W.op ⋙ C.structureSheaf.obj)

/-- The preimage in `W(B)` of an open `U` of `X`. -/
public abbrev openFamilyOpen (U : X.left.obj.Opens)
    (d : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow κ))ᵒᵖ) :
    (W.obj d).left.obj.Opens :=
  (π.app d).left.hom ⁻¹ᵁ U

/-- The maps of the family to `X` are compatible with the transition maps of the family. -/
public theorem openFamily_comp {d d' : (AdequateFunctor.AlgebrasInSite (A : Type u)
    (schemeSizeBelow κ))ᵒᵖ} (g : d ⟶ d') :
    (W.map g).left.hom ≫ (π.app d').left.hom = (π.app d).left.hom := by
  have h := congrArg (fun k => k.left.hom) (π.naturality g)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h
  exact h

/-- The preimages of an open are compatible with the transition maps of the family. -/
public theorem openFamilyOpen_eq {d d' : (AdequateFunctor.AlgebrasInSite (A : Type u)
    (schemeSizeBelow κ))ᵒᵖ} (g : d ⟶ d') (U : X.left.obj.Opens) :
    openFamilyOpen C W X π U d = (W.map g).left.hom ⁻¹ᵁ openFamilyOpen C W X π U d' := by
  rw [openFamilyOpen, openFamilyOpen, ← Scheme.Hom.comp_preimage, openFamily_comp]

/-- Preimages are monotone. -/
public theorem openFamilyOpen_mono {U V : X.left.obj.Opens} (h : U ≤ V)
    (d : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow κ))ᵒᵖ) :
    openFamilyOpen C W X π U d ≤ openFamilyOpen C W X π V d :=
  Scheme.Hom.preimage_mono _ h

/-- **The family of the preimages of an open `U` of `X`**: `B ↦ W(B) ×_X U`, as the open
subschemes of the members of the family. -/
public def openFamily (U : X.left.obj.Opens) :
    (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow κ))ᵒᵖ ⥤ C.category where
  obj d := C.restrictOpen (W.obj d) (openFamilyOpen C W X π U d)
  map g := C.restrictOpenHom (W.map g) _ _ (le_of_eq (openFamilyOpen_eq C W X π g U))
  map_id d := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change (W.map (𝟙 d)).left.hom.resLE _ _ _ = 𝟙 _
    rw [← cancel_mono (openFamilyOpen C W X π U d).ι, Scheme.Hom.resLE_comp_ι, W.map_id]
    simp
  map_comp g g' := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change (W.map (g ≫ g')).left.hom.resLE _ _ _ =
      (W.map g).left.hom.resLE _ _ _ ≫ (W.map g').left.hom.resLE _ _ _
    rw [← cancel_mono (openFamilyOpen C W X π U _).ι, Scheme.Hom.resLE_comp_ι, Category.assoc,
      Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, W.map_comp]
    rfl

/-- The inclusion of the family of preimages of `U` into the family. -/
public def openFamilyι (U : X.left.obj.Opens) : openFamily C W X π U ⟶ W where
  app d := C.restrictOpenι (W.obj d) _
  naturality _ _ _ := C.restrictOpenHom_comp_ι _ _ _ _

/-- The inclusion of the family of preimages of `U` into that of `V`, for `U ⊆ V`. -/
public def openFamilyHomOfLE {U V : X.left.obj.Opens} (h : U ≤ V) :
    openFamily C W X π U ⟶ openFamily C W X π V where
  app d := C.restrictOpenHomOfLE (W.obj d) (openFamilyOpen_mono C W X π h d)
  naturality _ _ _ := C.restrictOpenHom_comp_homOfLE _ _ _ _ _

/-- The inclusion of the family of preimages of `U` into that of `V`, followed by the inclusion
of the latter into the family, is the inclusion of the family of preimages of `U`. -/
@[reassoc (attr := simp)]
public theorem openFamilyHomOfLE_comp_ι {U V : X.left.obj.Opens} (h : U ≤ V) :
    openFamilyHomOfLE C W X π h ≫ openFamilyι C W X π V = openFamilyι C W X π U :=
  NatTrans.ext (funext fun _ => C.restrictOpenHomOfLE_comp_ι _ _)

/-- The inclusions of families of preimages for `U ⊆ V` and `V ⊆ V'` compose to the inclusion
for `U ⊆ V'`. -/
@[reassoc (attr := simp)]
public theorem openFamilyHomOfLE_comp {U V V' : X.left.obj.Opens} (h : U ≤ V) (h' : V ≤ V') :
    openFamilyHomOfLE C W X π h ≫ openFamilyHomOfLE C W X π h' =
      openFamilyHomOfLE C W X π (h.trans h') :=
  NatTrans.ext (funext fun _ => C.restrictOpenHomOfLE_comp _ _ _)

/-- The ring maps of the family of preimages of `U`: those of the family followed by
restriction to the preimages. -/
public abbrev openFamilyRingMap (U : X.left.obj.Opens) :
    AdequateFunctor.algebraRingDiagramOn
        (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow κ)) ⟶
      (openFamily C W X π U).op ⋙ C.structureSheaf.obj :=
  φ ≫ Functor.whiskerRight (NatTrans.op (openFamilyι C W X π U)) C.structureSheaf.obj

/-- **The sections over the preimages of an open `U` of `X`**, `𝓖 ↦ (B ↦ 𝓖(W(B) ×_X U))`. -/
public abbrev openFamilySections (U : X.left.obj.Opens) :
    SheafOfModules.{u} C.structureSheaf ⥤
      AdequateFunctor.ModuleValuedFunctorOn.{u}
        (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow κ)) :=
  sectionsAlong C (openFamily C W X π U) (openFamilyRingMap C W X π φ U)

/-- The compatibility of the ring maps with the inclusion of the families of `U ⊆ V`. -/
public theorem openFamilyRingMap_comp {U V : X.left.obj.Opens} (h : U ≤ V) :
    openFamilyRingMap C W X π φ V ≫
        Functor.whiskerRight (NatTrans.op (openFamilyHomOfLE C W X π h)) C.structureSheaf.obj =
      openFamilyRingMap C W X π φ U := by
  rw [openFamilyRingMap, openFamilyRingMap, Category.assoc, ← Functor.whiskerRight_comp,
    ← NatTrans.op_comp, openFamilyHomOfLE_comp_ι]

/-- **Restriction of sections from the preimages of `V` to those of `U ⊆ V`.** -/
public def openFamilyRestriction {U V : X.left.obj.Opens} (h : U ≤ V) :
    openFamilySections C W X π φ V ⟶ openFamilySections C W X π φ U :=
  Functor.whiskerLeft (SheafOfModules.forget C.structureSheaf)
    (Stacks.PresheafOfModules.pushforwardIndexMap.{u}
      (NatTrans.op (openFamilyHomOfLE C W X π h)) (openFamilyRingMap_comp C W X π φ h))

/-- The restriction of sections is the restriction map of the sheaf. -/
public theorem openFamilyRestriction_app_app_apply {U V : X.left.obj.Opens} (h : U ≤ V)
    (G : SheafOfModules.{u} C.structureSheaf) (Z)
    (x : ((openFamilySections C W X π φ V).obj G).obj Z) :
    (((openFamilyRestriction C W X π φ h).app G).app Z) x =
      G.val.map ((openFamilyHomOfLE C W X π h).app Z.unop).op x := rfl

/-- Restrictions compose. -/
public theorem openFamilyRestriction_comp {U V V' : X.left.obj.Opens} (h : U ≤ V) (h' : V ≤ V') :
    openFamilyRestriction C W X π φ h' ≫ openFamilyRestriction C W X π φ h =
      openFamilyRestriction C W X π φ (h.trans h') := by
  refine NatTrans.ext (funext fun G => (PresheafOfModules.toPresheaf _).map_injective ?_)
  refine NatTrans.ext (funext fun Z => ?_)
  change G.val.presheaf.map ((openFamilyHomOfLE C W X π h').app Z.unop).op ≫
      G.val.presheaf.map ((openFamilyHomOfLE C W X π h).app Z.unop).op =
    G.val.presheaf.map ((openFamilyHomOfLE C W X π (h.trans h')).app Z.unop).op
  rw [← Functor.map_comp, ← op_comp, ← NatTrans.comp_app, openFamilyHomOfLE_comp]

/-- **The sections over two opens form a pullback square**, for every sheaf of modules: the
Mayer–Vietoris square of the two preimages in each member of the family. -/
public theorem isPullback_openFamilyRestriction (U₁ U₂ : X.left.obj.Opens)
    (G : SheafOfModules.{u} C.structureSheaf) :
    IsPullback ((openFamilyRestriction C W X π φ (le_sup_left : U₁ ≤ U₁ ⊔ U₂)).app G)
      ((openFamilyRestriction C W X π φ (le_sup_right : U₂ ≤ U₁ ⊔ U₂)).app G)
      ((openFamilyRestriction C W X π φ (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).app G)
      ((openFamilyRestriction C W X π φ (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).app G) := by
  have w : (openFamilyRestriction C W X π φ (le_sup_left : U₁ ≤ U₁ ⊔ U₂)).app G ≫
        (openFamilyRestriction C W X π φ (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).app G =
      (openFamilyRestriction C W X π φ (le_sup_right : U₂ ≤ U₁ ⊔ U₂)).app G ≫
        (openFamilyRestriction C W X π φ (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).app G := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, openFamilyRestriction_comp,
      openFamilyRestriction_comp]
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ w)
    (PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun Z => ?_)
  refine (isLimitMapConePullbackConeEquiv (PresheafOfModules.evaluation _ Z) w).symm ?_
  refine IsPullback.isLimit ?_
  refine IsPullback.of_map (forget₂ (ModuleCat _) AddCommGrpCat) (by
    simp only [← Functor.map_comp, w]) ?_
  exact C.isPullback_sections_restrictOpenSquare G (W.obj Z.unop)
    (openFamilyOpen C W X π U₁ Z.unop) (openFamilyOpen C W X π U₂ Z.unop)

/-- Abelian presheaves on a chosen big site admit sheafification at the universe of its schemes. -/
local instance hasSheafify_site : HasSheafify C.topology AddCommGrpCat.{u} :=
  C.hasSheafify_addCommGrpCat.{u, u}

/-- **Restriction of sections of an injective module to a smaller family is an epimorphism**:
the restriction maps of an injective sheaf of modules along monomorphisms of the site are
surjective, [Stacks, Tag 093X]. -/
public theorem epi_openFamilyRestriction_of_injective {U V : X.left.obj.Opens} (h : U ≤ V)
    (G : SheafOfModules.{u} C.structureSheaf) [Injective G] :
    Epi ((openFamilyRestriction C W X π φ h).app G) := by
  apply PresheafOfModules.epi_of_surjective
  intro Z
  have : Mono ((openFamilyHomOfLE C W X π h).app Z.unop) :=
    C.mono_restrictOpenHomOfLE (W.obj Z.unop) (openFamilyOpen_mono C W X π h Z.unop)
  exact Stacks.Injectives.surjective_presheaf_map_of_injective
    ((openFamilyHomOfLE C W X π h).app Z.unop) G

end OpenFamily

/-! ### The induction over the quasi-compact opens -/

section Induction

variable (W : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow κ))ᵒᵖ ⥤ C.category)
  (X : C.category) (π : W ⟶ (Functor.const _).obj X)
  (φ : AdequateFunctor.algebraRingDiagramOn
      (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow κ)) ⟶
    W.op ⋙ C.structureSheaf.obj)
  (P : ObjectProperty (AdequateFunctor.ModuleValuedFunctorOn.{u}
    (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow κ))))
  [P.IsWeakSerreClass]

/-- **The Mayer–Vietoris step**: if all derived functors of the sections over the preimages of
`U`, of `V` and of `U ∩ V` take values in a weak Serre class `P` at `𝓖`, then so do those of
the sections over the preimages of `U ∪ V`. -/
public theorem prop_rightDerived_openFamilySections_sup (U V : X.left.obj.Opens)
    (G : SheafOfModules.{u} C.structureSheaf)
    (hU : ∀ k, P (((openFamilySections C W X π φ U).rightDerived k).obj G))
    (hV : ∀ k, P (((openFamilySections C W X π φ V).rightDerived k).obj G))
    (hUV : ∀ k, P (((openFamilySections C W X π φ (U ⊓ V)).rightDerived k).obj G)) (k : ℕ) :
    P (((openFamilySections C W X π φ (U ⊔ V)).rightDerived k).obj G) :=
  prop_rightDerived_of_mayerVietoris P
    (openFamilyRestriction C W X π φ (le_sup_left : U ≤ U ⊔ V))
    (openFamilyRestriction C W X π φ (le_sup_right : V ≤ U ⊔ V))
    (openFamilyRestriction C W X π φ (inf_le_left : U ⊓ V ≤ U))
    (openFamilyRestriction C W X π φ (inf_le_right : U ⊓ V ≤ V))
    (by rw [openFamilyRestriction_comp, openFamilyRestriction_comp])
    (fun I _ => ⟨isPullback_openFamilyRestriction C W X π φ U V I,
      epi_openFamilyRestriction_of_injective C W X π φ _ I⟩) G hU hV hUV k

/-- **Cases I–III of the source's proof of [Stacks, Tag 06VR]**, for a family over a
quasi-separated scheme `X`: if every derived functor of the sections over the preimages of
every affine open of `X` takes values in a weak Serre class `P` at `𝓖`, then so does every
derived functor of the sections over the preimages of every quasi-compact open of `X`. This is
the induction principle of [Stacks, Tag 08DR], whose induction step is the Mayer–Vietoris
sequence `Stacks.Adequate.prop_rightDerived_openFamilySections_sup`. -/
public theorem prop_rightDerived_openFamilySections [QuasiSeparatedSpace X.left.obj]
    (G : SheafOfModules.{u} C.structureSheaf)
    (haff : ∀ U : X.left.obj.Opens, IsAffineOpen U →
      ∀ k, P (((openFamilySections C W X π φ U).rightDerived k).obj G))
    (U : X.left.obj.Opens) (hU : IsCompact (U : Set X.left.obj)) (k : ℕ) :
    P (((openFamilySections C W X π φ U).rightDerived k).obj G) :=
  Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open
    (fun U => ∀ k, P (((openFamilySections C W X π φ U).rightDerived k).obj G)) haff
    (fun U V _ _ hU hV hUV => prop_rightDerived_openFamilySections_sup C W X π φ P U V G hU hV hUV)
    U hU k

end Induction

/-! ### The family over the open `⊤` -/

section Top

variable (W : (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow κ))ᵒᵖ ⥤ C.category)
  (X : C.category) (π : W ⟶ (Functor.const _).obj X)
  (φ : AdequateFunctor.algebraRingDiagramOn
      (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow κ)) ⟶
    W.op ⋙ C.structureSheaf.obj)

/-- The inclusion of the family of preimages of `⊤` is an isomorphism of families. -/
public instance isIso_openFamilyι_top : IsIso (openFamilyι C W X π ⊤) := by
  have : ∀ d, IsIso ((openFamilyι C W X π ⊤).app d) := fun d =>
    C.isIso_restrictOpenι_of_eq_top (W.obj d) _ (Scheme.Hom.preimage_top _)
  exact NatIso.isIso_of_isIso_app _

/-- **The sections over the preimages of `⊤` are the sections along the family.** -/
public def openFamilySectionsTopIso :
    openFamilySections C W X π φ ⊤ ≅ sectionsAlong C W φ :=
  Functor.isoWhiskerLeft (SheafOfModules.forget C.structureSheaf)
    (Stacks.PresheafOfModules.pushforwardIsoOfIndexIso.{u} (asIso (openFamilyι C W X π ⊤)) (by
      rw [openFamilyRingMap, Category.assoc, ← Functor.whiskerRight_comp]
      change φ ≫ Functor.whiskerRight (NatTrans.op (openFamilyι C W X π ⊤) ≫
        NatTrans.op (inv (openFamilyι C W X π ⊤))) C.structureSheaf.obj = φ
      rw [← NatTrans.op_comp, IsIso.inv_hom_id, NatTrans.op_id, Functor.whiskerRight_id',
        Category.comp_id]))

end Top

end Stacks.Adequate

end
