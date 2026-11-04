module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalenceStructureSheaf

/-!
# The transport of `R𝓗om(𝒪, -) ≅ id` along an equivalence of ringed sites, in `D(𝒪)`

The derived half of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalenceStructureSheaf`:
the transport `φ_* R𝓗om(𝒪_C, L) ≅ R𝓗om(φ_* 𝒪_C, φ_* L)` of
`AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIso`, followed by the canonical morphism
`𝒪_D ⟶ φ_* 𝒪_C` and by `R𝓗om(𝒪_D, φ_* L) ≅ φ_* L`, is `φ_*` of `R𝓗om(𝒪_C, L) ≅ L`. On a
K-injective representative both identifications are evaluation at the unit section, and the
chain-level statement is
`AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIso_comp_structureSheafHomEvaluation`.

## Main definitions

* `AlgebraicGeometry.RingedSite.siteEquivDerivedStructureSheafHom`: `𝒪_D ⟶ φ_* 𝒪_C` in `D(𝒪_D)`.

## Main results

* `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIso_structureSheaf` and its variant
  `siteEquivDerivedSheafHomIsoOfIso_structureSheaf` for an invertible structure map.

## Implementation notes

The statements use `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIso`, which exists only
at `CategoryTheory.HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

variable {X Y : RingedSite.{u, u, u}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{u} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

/-! ### In the derived category -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [hlim : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [hcolim : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]

/-- **The canonical morphism `𝒪_D ⟶ φ_* 𝒪_C` in `D(𝒪_D)`.** -/
def siteEquivDerivedStructureSheafHom :
    derivedStructureSheaf Y ⟶
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj (derivedStructureSheaf X) :=
  DerivedCategory.Q.map (siteEquivStructureSheafComplexHom eqv φ) ≫
    ((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app
      (structureSheafComplex X)).inv

/-- The derived identification `R𝓗om(𝒪, L) ≅ L`, through a K-injective representative `I` of `L`. -/
private theorem derivedStructureSheafHomIso_hom_eq_of_iso
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] (e : DerivedCategory.Q.obj I ≅ L) :
    (derivedStructureSheafHomIso X L).hom =
      ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map e.inv ≫
        (derivedSheafHomComparison X (structureSheafComplex X) I).hom ≫
          DerivedCategory.Q.map (structureSheafHomEvaluation X I) ≫ e.hom := by
  rw [← reassoc_of% (derivedStructureSheafHomIso_model X I),
    reassoc_of% (derivedStructureSheafHomIso_naturality X e.inv), Iso.inv_hom_id,
    Category.comp_id]

/-- The transport on representatives, at the structure sheaf complex, is compatible with the
identifications `R𝓗om(𝒪, -) ≅ id`. -/
theorem siteEquivModelHom_structureSheaf
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [((pushComplex eqv φ).obj I).IsKInjective]
    (eI : DerivedCategory.Q.obj I ≅ L) :
    siteEquivModelHom eqv φ ψ H₁ H₂ eI (structureSheafComplex X) ≫
        ((derivedSheafHomBifunctor Y).map (siteEquivDerivedStructureSheafHom eqv φ).op).app
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) ≫
        (derivedStructureSheafHomIso Y
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L)).hom =
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (derivedStructureSheafHomIso X L).hom := by
  have hg := (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.hom.naturality
    (structureSheafHomEvaluation X I)
  simp only [Functor.comp_map] at hg
  -- the identifications on `X` and `Y`, through the representatives `I` and `φ_* I`
  have hηX := derivedStructureSheafHomIso_hom_eq_of_iso eI
  have hηY := derivedStructureSheafHomIso_hom_eq_of_iso
    (((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app I).symm ≪≫
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso eI)
  -- the morphism of structure sheaves, against the factorization isomorphism
  have ha : ((derivedSheafHomBifunctor Y).map
        ((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.hom.app
          (structureSheafComplex X)).op).app
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) ≫
      ((derivedSheafHomBifunctor Y).map (siteEquivDerivedStructureSheafHom eqv φ).op).app
        ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) =
      ((derivedSheafHomBifunctor Y).map
        (DerivedCategory.Q.map (siteEquivStructureSheafComplexHom eqv φ)).op).app
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) := by
    rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, siteEquivDerivedStructureSheafHom,
      Category.assoc, Iso.app_inv, Iso.inv_hom_id_app]
    exact congrArg (fun g => ((derivedSheafHomBifunctor Y).map g.op).app
      ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L)) (Category.comp_id _)
  have he := derivedSheafHomComparison_naturality Y (siteEquivStructureSheafComplexHom eqv φ)
    (𝟙 ((pushComplex eqv φ).obj I))
  simp only [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at he
  have hf := DerivedCategory.Q.congr_map
    (siteEquivSheafHomComplexIso_comp_structureSheafHomEvaluation eqv φ ψ H₁ H₂ I)
  simp only [Functor.map_comp] at hf
  have hM : (siteEquivDerivedSheafHomModelIso eqv φ ψ H₁ H₂ (structureSheafComplex X) I).hom =
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
          (derivedSheafHomComparison X (structureSheafComplex X) I).hom ≫
        (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.hom.app
          (sheafHomComplex X (structureSheafComplex X) I).obj ≫
        DerivedCategory.Q.map
          (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ (structureSheafComplex X) I).hom ≫
        (derivedSheafHomComparison Y ((pushComplex eqv φ).obj (structureSheafComplex X))
          ((pushComplex eqv φ).obj I)).inv := rfl
  simp only [hηX, hηY, siteEquivModelHom, hM, Category.assoc]
  simp only [reassoc_of% ha]
  simp only [NatTrans.naturality_assoc, Iso.map_hom_inv_id_assoc]
  simp only [reassoc_of% he, Iso.inv_hom_id_assoc]
  simp only [reassoc_of% hf]
  simp only [← reassoc_of% hg]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Iso.hom_inv_id_app_assoc,
    Functor.map_comp]

/-- **The transport of `R𝓗om(𝒪_C, L) ≅ L` along an equivalence of ringed sites.** The transport
`φ_* R𝓗om(𝒪_C, L) ≅ R𝓗om(φ_* 𝒪_C, φ_* L)`, followed by the canonical morphism `𝒪_D ⟶ φ_* 𝒪_C`
in the first variable and by `R𝓗om(𝒪_D, φ_* L) ≅ φ_* L`, is `φ_*` of `R𝓗om(𝒪_C, L) ≅ L`. -/
theorem siteEquivDerivedSheafHomIso_structureSheaf
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (siteEquivDerivedSheafHomIso eqv φ ψ H₁ H₂ (derivedStructureSheaf X) L).hom ≫
        ((derivedSheafHomBifunctor Y).map (siteEquivDerivedStructureSheafHom eqv φ).op).app
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) ≫
        (derivedStructureSheafHomIso Y
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L)).hom =
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (derivedStructureSheafHomIso X L).hom := by
  let := pushforward_inverse_preservesFiniteLimits eqv φ ψ H₁ H₂
  let := pushforward_inverse_preservesFiniteColimits eqv φ ψ H₁ H₂
  let : ((kInjectiveResolution X).obj (DerivedCategory.Q.objPreimage L)).IsKInjective :=
    Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (DerivedCategory.Q.objPreimage L)
  let : ((pushComplex eqv φ).obj
      ((kInjectiveResolution X).obj (DerivedCategory.Q.objPreimage L))).IsKInjective :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact
      (SheafOfModules.pushforward.{u} φ) (SheafOfModules.pushforward.{u} ψ)
      (modulesEquiv eqv φ ψ H₁ H₂).symm.toAdjunction _
  rw [siteEquivDerivedSheafHomIso_hom_eq,
    ← siteEquivDerivedSheafHomIsoOfModels_hom_eq eqv φ ψ H₁ H₂ _
      (Iso.refl (DerivedCategory.Q.obj (structureSheafComplex X))),
    siteEquivDerivedSheafHomIsoOfModels_hom]
  simp only [Iso.refl_hom, Iso.refl_inv, op_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id]
  exact siteEquivModelHom_structureSheaf eqv φ ψ H₁ H₂ _

end Derived

section OfIso

attribute [local instance] HasDerivedCategory.standard

variable [hφ : IsIso φ] [hlim : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [hcolim : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]

/-- `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIso_structureSheaf` for the variant
`siteEquivDerivedSheafHomIsoOfIso` with an invertible structure map. -/
theorem siteEquivDerivedSheafHomIsoOfIso_structureSheaf
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (siteEquivDerivedSheafHomIsoOfIso eqv φ (derivedStructureSheaf X) L).hom ≫
        ((derivedSheafHomBifunctor Y).map (siteEquivDerivedStructureSheafHom eqv φ).op).app
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) ≫
        (derivedStructureSheafHomIso Y
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L)).hom =
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (derivedStructureSheafHomIso X L).hom :=
  siteEquivDerivedSheafHomIso_structureSheaf eqv φ _
    (Stacks.SheafOfModules.InternalHom.psiOfIso_counit eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_unit eqv φ) L

end OfIso

end AlgebraicGeometry.RingedSite

end
