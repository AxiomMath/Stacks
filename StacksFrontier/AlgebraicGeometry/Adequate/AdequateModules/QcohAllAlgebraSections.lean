module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineQuasiInverse
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedModuleAdequacy
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedSheafNaturality

/-!
# The pullback sections of a quasi-coherent module over all algebras of the base

Over an affine base `Spec A`, the sections `C ↦ Γ(Spec C, f_C^*𝓖)` of a quasi-coherent module
`𝓖`, defined by `Stacks.Adequate.affineSectionsFunctor` over the `A`-algebras of a chosen big
site, extend to an adequate `AdequateFunctor.ModuleValuedFunctor` on all `A`-algebras.

The construction sends `𝓖` to the module extension `C ↦ C ⊗_A 𝓖ᵃ(Spec A)` of its module of
sections over the base affine. A module extension is adequate,
`AdequateFunctor.isAdequate_moduleExtension`, and its restriction to the algebras of the site is
identified with the sections `C ↦ Γ(Spec C, f_C^*𝓖)` by the comparison
`Stacks.Adequate.affineSectionsCompare` of [Stacks, Tag 03DX], which is an isomorphism at an
associated module.

## Main definitions

* `Stacks.Adequate.BigSite.qcohAffineBaseSections` — the sections of `𝓖ᵃ` over the base affine,
  as a functor on the quasi-coherent `𝒪_{Spec A}`-modules. Over an affine base this is
  `𝓖 ↦ Γ(Spec A, 𝓖)`.
* `Stacks.Adequate.BigSite.qcohAllAlgebraSections` — **the sections construction on all
  `A`-algebras**: `𝓖 ↦ (C ↦ C ⊗_A 𝓖ᵃ(Spec A))`, a functor from the quasi-coherent
  `𝒪_{Spec A}`-modules to `AdequateFunctor.ModuleValuedFunctor`.

## Main results

* `Stacks.Adequate.BigSite.pullbackSectionsSheafIsoAssociatedModule` — the pullback-sections
  sheaf of a quasi-coherent `𝒪_{Spec A}`-module is isomorphic to its associated module.
* `Stacks.Adequate.BigSite.isIso_affineSectionsCompareNatTrans_app_pullbackSections` — the
  comparison `C ⊗_A 𝓖ᵃ(Spec A) ⟶ 𝓖ᵃ(Spec C)` is an isomorphism at every pullback-sections
  sheaf.
* `Stacks.Adequate.BigSite.isAdequate_qcohAllAlgebraSections_obj` — **the sections construction
  on all `A`-algebras is adequate**.
* `Stacks.Adequate.BigSite.qcohAllAlgebraSectionsRestrictionIso` — **its restriction to the
  `A`-algebras of the site is the affine-section functor of `𝓖ᵃ`**, naturally in `𝓖`.

## References

* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Adequate

/-- A component of a natural transformation at an object isomorphic to one where it is an
isomorphism is an isomorphism. -/
public theorem isIso_natTrans_app_of_iso {C D : Type*} [Category* C] [Category* D]
    {X Y : C ⥤ D} (η : X ⟶ Y) {c c' : C} (e : c ≅ c') [IsIso (η.app c')] :
    IsIso (η.app c) := by
  have h : η.app c = X.map e.hom ≫ η.app c' ≫ Y.map e.inv := by
    rw [← Category.assoc, η.naturality, Category.assoc, ← Y.map_comp, e.hom_inv_id,
      Y.map_id, Category.comp_id]
  rw [h]
  infer_instance

/-- The functor of sections over the base affine is additive. -/
public instance additive_affineBaseSectionsFunctor {τ : CoveringTopology} {A : CommRingCat.{u}}
    (B : BigSite τ (Spec A)) : (affineBaseSectionsFunctor B).Additive where
  map_add {F G} u v := by
    change ((affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).map (u + v)).app
        (op (op (baseSiteAlgebra B A B.base_mem))) = _
    rw [Functor.map_add]
    rfl

section Sections

variable {A : CommRingCat.{u}} (B : BigFppfSite.{u}) (hS : B.Contains (Spec A))

/-! ### The pullback-sections sheaf is an associated module -/

/-- The pullback-sections sheaf of a quasi-coherent `𝒪_{Spec A}`-module is isomorphic to its
associated module in the sense of [Stacks, Tag 03DU] (3). -/
public noncomputable def BigSite.pullbackSectionsSheafIsoAssociatedModule
    (F : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory) :
    (BigSite.pullbackSectionsSheafFunctor B hS).obj F ≅
      (BigSite.ofBigFppfSite B (Spec A) hS).associatedModule F.obj
        (isSheaf_associatedPresheaf _ F.obj) :=
  let := F.property
  (associatedModuleIsoSectionsSheaf B (Spec A) hS F.obj).symm ≪≫
    BigSite.associatedModuleFunctorObjIso B hS F.obj

/-- The comparison `C ⊗_A 𝓖ᵃ(Spec A) ⟶ 𝓖ᵃ(Spec C)` is an isomorphism at every
pullback-sections sheaf. -/
public instance BigSite.isIso_affineSectionsCompareNatTrans_app_pullbackSections
    (F : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory) :
    IsIso ((affineSectionsCompareNatTrans (BigSite.ofBigFppfSite B (Spec A) hS)).app
      ((BigSite.pullbackSectionsSheafFunctor B hS).obj F)) :=
  let := F.property
  let : IsIso ((affineSectionsCompareNatTrans (BigSite.ofBigFppfSite B (Spec A) hS)).app
      ((BigSite.ofBigFppfSite B (Spec A) hS).associatedModule F.obj
        (isSheaf_associatedPresheaf _ F.obj))) :=
    isIso_affineSectionsCompare (BigSite.ofBigFppfSite B (Spec A) hS) A (𝟙 (Spec A))
      (BigSite.ofBigFppfSite B (Spec A) hS).base_mem F.obj (isSheaf_associatedPresheaf _ F.obj)
  isIso_natTrans_app_of_iso _ (BigSite.pullbackSectionsSheafIsoAssociatedModule B hS F)

/-- The comparison at the pullback-sections sheaves is an isomorphism of functors: it is one at
every quasi-coherent `𝒪_{Spec A}`-module. -/
public instance BigSite.isIso_whiskerLeft_affineSectionsCompareNatTrans :
    IsIso (Functor.whiskerLeft (BigSite.pullbackSectionsSheafFunctor B hS)
      (affineSectionsCompareNatTrans (BigSite.ofBigFppfSite B (Spec A) hS))) :=
  have : ∀ F : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory,
      IsIso ((Functor.whiskerLeft (BigSite.pullbackSectionsSheafFunctor B hS)
        (affineSectionsCompareNatTrans (BigSite.ofBigFppfSite B (Spec A) hS))).app F) :=
    fun F => BigSite.isIso_affineSectionsCompareNatTrans_app_pullbackSections B hS F
  NatIso.isIso_of_isIso_app _

/-! ### The sections construction on all algebras of the base -/

/-- The sections of `𝓖ᵃ` over the base affine, as a functor on the quasi-coherent
`𝒪_{Spec A}`-modules: `𝓖 ↦ Γ(Spec A, 𝓖)`. -/
public noncomputable abbrev BigSite.qcohAffineBaseSections :
    (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory ⥤
      ModuleCat.{u} ↥A :=
  BigSite.pullbackSectionsSheafFunctor B hS ⋙
    affineBaseSectionsFunctor (BigSite.ofBigFppfSite B (Spec A) hS)

/-- The sections construction of [Stacks, Tag 03DU] (3) as a module-valued functor on all
`A`-algebras: the quasi-coherent `𝒪_{Spec A}`-module `𝓖` is sent to the extension of scalars
`C ↦ C ⊗_A 𝓖ᵃ(Spec A)` of its module of sections over the base affine. -/
public noncomputable def BigSite.qcohAllAlgebraSections :
    (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory ⥤
      AdequateFunctor.ModuleValuedFunctor.{u, u} ↥A :=
  BigSite.qcohAffineBaseSections B hS ⋙ AdequateFunctor.moduleExtensionFunctor.{u, u} ↥A

/-- The sections construction on all `A`-algebras is adequate. -/
public theorem BigSite.isAdequate_qcohAllAlgebraSections_obj
    (F : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory) :
    AdequateFunctor.IsAdequate (𝟭 _) ((BigSite.qcohAllAlgebraSections B hS).obj F) :=
  AdequateFunctor.isAdequate_moduleExtension _

/-- **The restriction of the all-algebras sections construction to the `A`-algebras of the site
is the affine-section functor of `𝓖ᵃ`**, naturally in the quasi-coherent `𝒪_{Spec A}`-module
`𝓖`. -/
public noncomputable def BigSite.qcohAllAlgebraSectionsRestrictionIso :
    BigSite.qcohAllAlgebraSections B hS ⋙
        PresheafOfModules.pushforward₀
          (AdequateFunctor.siteAlgebraInclusion ↥A
            (schemeSizeBelow (BigSite.ofBigFppfSite B (Spec A) hS).cutoff)).op
          (AdequateFunctor.algebraRingDiagram.{u} ↥A) ≅
      BigSite.pullbackSectionsSheafFunctor B hS ⋙
        affineSectionsFunctor.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS) A (𝟙 (Spec A)) :=
  @asIso _ _ _ _ _ (BigSite.isIso_whiskerLeft_affineSectionsCompareNatTrans B hS)

end Sections

end Stacks.Adequate

end
