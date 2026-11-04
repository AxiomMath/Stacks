module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EssImageGlobalization
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullOnFree
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.MemberLocalStep

/-!
# Modules with a local global presentation on the big sites of a scheme

Let `S` be a scheme and `τ : AlgebraicGeometry.SiteKind` one of the five big topologies. If the
restriction of a module `𝒢` on `(Sch/S)_τ` to the localization at an object `T` has a global
presentation, then its restriction to the big `τ` site of the scheme `X` of `T` is `𝓕^a` for a
quasi-coherent `𝒪_X`-module `𝓕`. This is the local step in the proof of [Stacks, Tag 03DX] (1).

## Main definitions

* `AlgebraicGeometry.BigFppfOver.baseObjRestrictFunctor` and
  `AlgebraicGeometry.BigFppfOver.baseObjRestrict`: reindexing a module on the localization of
  `(Sch/S)_τ` at `T` along `AlgebraicGeometry.BigFppfOver.objEquiv`, and the restriction
  `𝒢 ↦ 𝒢|_{(Sch/X)_τ}`.

## Main results

* `AlgebraicGeometry.BigFppfOver.baseIsFullOnFree`: `𝓕 ↦ 𝓕^a` is full on free modules at
  every `τ`.
* `AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_baseAssociatedModule_of_cokernelFree`
  and
  `AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_baseAssociatedModule_of_presentation`:
  a module on `(Sch/S)_τ` presented as a cokernel of a morphism of free modules is `𝓕^a` for a
  quasi-coherent `𝒪_S`-module `𝓕`.
* `AlgebraicGeometry.BigFppfOver.baseIsDenseSubsite_objEquiv_inverse`: the localization of
  `(Sch/S)_τ` at `T` and the big `τ` site of the scheme of `T` are the same site.
* `AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_baseAssociatedModule_baseObjRestrict`:
  if the restriction of `𝒢` to the localization at `T` has a global presentation, then its
  restriction to the big `τ` site of the scheme `X` of `T` is `𝓕^a` for a quasi-coherent
  `𝒪_X`-module `𝓕`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (τ : SiteKind)

/-! ### Modules presented by free modules -/

/-- Every morphism between the associated modules on `(Sch/S)_τ` of two free `𝒪_S`-modules is
the associated morphism of a morphism of free `𝒪_S`-modules. -/
public theorem baseIsFullOnFree (I₁ I₂ : Type u)
    (α : (baseAssociatedModule B S hS τ).obj
        (SheafOfModules.free (R := S.ringCatSheaf) I₂) ⟶
      (baseAssociatedModule B S hS τ).obj (SheafOfModules.free (R := S.ringCatSheaf) I₁)) :
    ∃ β : SheafOfModules.free (R := S.ringCatSheaf) I₂ ⟶ SheafOfModules.free I₁,
      (baseAssociatedModule B S hS τ).map β = α :=
  SheafOfModules.exists_pullback_map_eq_of_surjective_sectionsMap_unit
    (baseStructureMap B S hS τ)
    (SheafOfModules.surjective_sectionsMap_of_isIso _
      (isIso_baseUnit_app B S hS τ (SheafOfModules.free (R := S.ringCatSheaf) I₁))) α

/-- A sheaf of modules on `(Sch/S)_τ` presented as a cokernel
`⊕_{i ∈ I₂} 𝒪 ⟶ ⊕_{i ∈ I₁} 𝒪 ⟶ 𝒢 ⟶ 0` is the associated module `𝓕^a` of a quasi-coherent
`𝒪_S`-module `𝓕`. -/
public theorem exists_isQuasicoherent_iso_baseAssociatedModule_of_cokernelFree {I₁ I₂ : Type u}
    (α : SheafOfModules.free (R := FibredSite.baseRingStructureSheaf B S hS τ) I₂ ⟶
      SheafOfModules.free I₁)
    {G : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)}
    {π : SheafOfModules.free (R := FibredSite.baseRingStructureSheaf B S hS τ) I₁ ⟶ G}
    (hπ : α ≫ π = 0) (hc : IsColimit (CokernelCofork.ofπ π hπ)) :
    ∃ G' : S.Modules, G'.IsQuasicoherent ∧
      Nonempty ((baseAssociatedModule B S hS τ).obj G' ≅ G) := by
  obtain ⟨β, hβ⟩ := baseIsFullOnFree B S hS τ I₁ I₂
    ((SheafOfModules.pullbackObjFreeIso (baseStructureMap B S hS τ) I₂).hom ≫ α ≫
      (SheafOfModules.pullbackObjFreeIso (baseStructureMap B S hS τ) I₁).inv)
  refine ⟨cokernel β, Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
    (X := S) (M := SheafOfModules.free I₂) (N := SheafOfModules.free I₁) β, ?_⟩
  exact SheafOfModules.nonempty_iso_pullbackObj_cokernel_free (baseStructureMap B S hS τ)
    α β hβ hπ hc

/-- A sheaf of modules on `(Sch/S)_τ` with a `SheafOfModules.Presentation` is the associated
module `𝓕^a` of a quasi-coherent `𝒪_S`-module `𝓕`. -/
public theorem exists_isQuasicoherent_iso_baseAssociatedModule_of_presentation
    {G : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)}
    (P : G.Presentation) :
    ∃ G' : S.Modules, G'.IsQuasicoherent ∧
      Nonempty ((baseAssociatedModule B S hS τ).obj G' ≅ G) :=
  let : HasSheafify (baseOverTopology B S hS τ) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  exists_isQuasicoherent_iso_baseAssociatedModule_of_cokernelFree B S hS τ
    ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π)
    (by simp) P.isColimit

/-- A module with a global presentation on `(Sch/S)_τ` has a `SheafOfModules.Presentation`. -/
public theorem nonempty_presentation_of_hasGlobalPresentation_base
    {G : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)}
    (h : G.HasGlobalPresentation) : Nonempty G.Presentation :=
  let : HasSheafify (baseOverTopology B S hS τ) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  h.nonempty_presentation_of_isTerminal (isTerminalOpensObjTop B S hS)

/-! ### The localization at an object, at every `τ` -/

section Obj

variable (T : BigFppfOver B S hS)

/-- Passing from the big `τ` site of the scheme of `T` to the localization of `(Sch/S)_τ` at `T`
is continuous. -/
public instance baseIsContinuous_objEquiv_functor :
    (objEquiv B S hS T).functor.IsContinuous
      (baseOverTopology B (objScheme B S hS T) (contains_objScheme B S hS T) τ)
      ((baseOverTopology B S hS τ).over T) :=
  have h : (Over.iteratedSliceBackward T).IsContinuous
      ((B.baseTopology τ).over T.left) (((B.baseTopology τ).over (B.obj hS)).over T) :=
    inferInstance
  h

/-- Passing from the localization of `(Sch/S)_τ` at `T` to the big `τ` site of the scheme of `T`
is continuous. -/
public instance baseIsContinuous_objEquiv_inverse :
    (objEquiv B S hS T).inverse.IsContinuous ((baseOverTopology B S hS τ).over T)
      (baseOverTopology B (objScheme B S hS T) (contains_objScheme B S hS T) τ) :=
  have h : (Over.iteratedSliceForward T).IsContinuous
      (((B.baseTopology τ).over (B.obj hS)).over T) ((B.baseTopology τ).over T.left) :=
    inferInstance
  h

/-- Passing from the big `τ` site of the scheme of `T` to the localization of `(Sch/S)_τ` at `T`
is cocontinuous. -/
public instance baseIsCocontinuous_objEquiv_functor :
    (objEquiv B S hS T).functor.IsCocontinuous
      (baseOverTopology B (objScheme B S hS T) (contains_objScheme B S hS T) τ)
      ((baseOverTopology B S hS τ).over T) :=
  have h : (Over.iteratedSliceBackward T).IsCocontinuous
      ((B.baseTopology τ).over T.left) (((B.baseTopology τ).over (B.obj hS)).over T) :=
    inferInstance
  h

/-- Passing from the localization of `(Sch/S)_τ` at `T` to the big `τ` site of the scheme of `T`
is cocontinuous. -/
public instance baseIsCocontinuous_objEquiv_inverse :
    (objEquiv B S hS T).inverse.IsCocontinuous ((baseOverTopology B S hS τ).over T)
      (baseOverTopology B (objScheme B S hS T) (contains_objScheme B S hS T) τ) :=
  have h : (Over.iteratedSliceForward T).IsCocontinuous
      (((B.baseTopology τ).over (B.obj hS)).over T) ((B.baseTopology τ).over T.left) :=
    inferInstance
  h

/-- The two `τ` topologies correspond under the equivalence of [Stacks, Tag 06WI]: a sieve of the
localization of `(Sch/S)_τ` at `T` is covering exactly when its image in the big `τ` site of the
scheme of `T` is. -/
public instance baseIsDenseSubsite_objEquiv_inverse :
    (objEquiv B S hS T).inverse.IsDenseSubsite ((baseOverTopology B S hS τ).over T)
      (baseOverTopology B (objScheme B S hS T) (contains_objScheme B S hS T) τ) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ (objEquiv B S hS T)

/-- The structure sheaf of the localization of `(Sch/S)_τ` at `T`, transported along
`AlgebraicGeometry.BigFppfOver.objEquiv`, is the structure sheaf of the big `τ` site of the
scheme of `T`. -/
public theorem baseReindexRing_objEquiv :
    Stacks.SheafOfModules.reindexRing
        (baseOverTopology B (objScheme B S hS T) (contains_objScheme B S hS T) τ)
        (objEquiv B S hS T) ((FibredSite.baseRingStructureSheaf B S hS τ).over T) =
      FibredSite.baseRingStructureSheaf B (objScheme B S hS T)
        (contains_objScheme B S hS T) τ :=
  rfl

/-- Reindexing a module on the localization of `(Sch/S)_τ` at `T` along
`AlgebraicGeometry.BigFppfOver.objEquiv` — a module on the big `τ` site of the scheme of `T`. -/
public noncomputable abbrev baseObjRestrictFunctor :
    SheafOfModules.{u} ((FibredSite.baseRingStructureSheaf B S hS τ).over T) ⥤
      SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B (objScheme B S hS T)
        (contains_objScheme B S hS T) τ) :=
  SheafOfModules.pushforward.{u} (𝟙 (Stacks.SheafOfModules.reindexRing
    (baseOverTopology B (objScheme B S hS T) (contains_objScheme B S hS T) τ)
    (objEquiv B S hS T) ((FibredSite.baseRingStructureSheaf B S hS τ).over T)))

/-- The restriction `𝒢 ↦ 𝒢|_{(Sch/X)_τ}`: a module on `(Sch/S)_τ` restricted to the
localization at `T` and read on the big `τ` site of the scheme `X` of `T`. -/
public noncomputable abbrev baseObjRestrict :
    SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ) ⥤
      SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B (objScheme B S hS T)
        (contains_objScheme B S hS T) τ) :=
  SheafOfModules.overFunctor.{u} (FibredSite.baseRingStructureSheaf B S hS τ) T ⋙
    baseObjRestrictFunctor B S hS τ T

/-- A global presentation of the restriction of `𝒢` to the localization of `(Sch/S)_τ` at `T` is a
global presentation of its restriction to the big `τ` site of the scheme of `T`. -/
public theorem hasGlobalPresentation_baseObjRestrict
    {G : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)}
    (h : (G.over T).HasGlobalPresentation) :
    ((baseObjRestrict B S hS τ T).obj G).HasGlobalPresentation :=
  Stacks.SheafOfModules.hasGlobalPresentation_reindex (objEquiv B S hS T)
    ((FibredSite.baseRingStructureSheaf B S hS τ).over T) (G.over T) h

/-- Reindexing along `AlgebraicGeometry.BigFppfOver.objEquiv` is precomposition with its functor
on the underlying presheaves of abelian groups. -/
public theorem val_presheaf_baseObjRestrict
    (G : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)) :
    ((baseObjRestrict B S hS τ T).obj G).val.presheaf =
      (objEquiv B S hS T).functor.op ⋙ (G.over T).val.presheaf :=
  rfl

/-- If the restriction of `𝒢` to the localization of `(Sch/S)_τ` at `T` has a global
presentation, then its restriction to the big `τ` site of the scheme `X` of `T` is the
associated module `𝓕^a` of a quasi-coherent `𝒪_X`-module `𝓕`. -/
public theorem exists_isQuasicoherent_iso_baseAssociatedModule_baseObjRestrict
    {G : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)}
    (h : (G.over T).HasGlobalPresentation) :
    ∃ F : (objScheme B S hS T).Modules, F.IsQuasicoherent ∧
      Nonempty ((baseAssociatedModule B (objScheme B S hS T)
        (contains_objScheme B S hS T) τ).obj F ≅ (baseObjRestrict B S hS τ T).obj G) :=
  exists_isQuasicoherent_iso_baseAssociatedModule_of_presentation B _ _ τ
    (nonempty_presentation_of_hasGlobalPresentation_base B _ _ τ
      (hasGlobalPresentation_baseObjRestrict B S hS τ T h)).some

end Obj

end AlgebraicGeometry.BigFppfOver

end
