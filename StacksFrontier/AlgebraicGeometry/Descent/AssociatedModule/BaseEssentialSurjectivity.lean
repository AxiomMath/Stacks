module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseMemberLocalStep
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreementTransport
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence
public import StacksFrontier.CategoryTheory.Sites.Glueing.SheafConditionLocalOnCover
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 03DX (1) on each of the five big sites of a scheme

Let `S` be a scheme and `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.  Descent,
Proposition 03DX (1) says that `𝓕 ↦ 𝓕^a` is an equivalence
`QCoh(𝒪_S) ⟶ QCoh((Sch/S)_τ, 𝒪)`. This file proves its essential surjectivity at every `τ`,
and that a quasi-coherent module on `(Sch/S)_τ` is a sheaf for the fppf topology.

## Main results

* `AlgebraicGeometry.BigFppfOver.isSheaf_fppf_over_of_hasGlobalPresentation`: a module on
  `(Sch/S)_τ` whose restriction to the localization at an object has a global presentation is an
  fppf sheaf on that localization.
* `AlgebraicGeometry.BigFppfOver.isSheaf_fppf_of_isQuasicoherentOnSite`: a quasi-coherent
  module on `(Sch/S)_τ` is a sheaf for the fppf topology.
* `AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`: Stacks
  03DX (1), essential surjectivity, at every `τ` — every quasi-coherent `𝒪`-module on
  `(Sch/S)_τ` is isomorphic to `𝓕^a` for a quasi-coherent `𝒪_S`-module `𝓕`.
* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_restrictTopology`: a quasi-coherent
  module on `(Sch/S)_fppf`, read for the coarser topology `τ`, is quasi-coherent on
  `(Sch/S)_τ`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (τ : SiteKind)

/-- The underlying presheaf of the restriction of a module to the localization at an object is
the restriction of its underlying presheaf. -/
public theorem val_presheaf_over
    (G : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))
    (X : BigFppfOver B S hS) :
    (G.over X).val.presheaf = (Over.forget X).op ⋙ G.val.presheaf := rfl

/-- **A module on `(Sch/S)_τ` with a global presentation on the localization at `T` is an fppf
sheaf there.** -/
public theorem isSheaf_fppf_over_of_hasGlobalPresentation (T : BigFppfOver B S hS)
    {G : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)}
    (h : (G.over T).HasGlobalPresentation) :
    Presheaf.IsSheaf ((topology B S hS).over T) (G.over T).val.presheaf := by
  obtain ⟨F, hF, ⟨e⟩⟩ :=
    exists_isQuasicoherent_iso_baseAssociatedModule_baseObjRestrict B S hS τ T h
  have := hF
  have e₂ : (restrictTopology B (objScheme B S hS T) (contains_objScheme B S hS T) τ).obj
        ((associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T)).obj F) ≅
      (baseObjRestrict B S hS τ T).obj G :=
    restrictTopologyAssociatedModuleIso B (objScheme B S hS T)
      (contains_objScheme B S hS T) τ F ≪≫ e
  have e₃ := ((SheafOfModules.forget
    (FibredSite.baseRingStructureSheaf B (objScheme B S hS T)
      (contains_objScheme B S hS T) τ)) ⋙
    PresheafOfModules.toPresheaf _).mapIso e₂
  have hsh : Presheaf.IsSheaf
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T))
      ((objEquiv B S hS T).functor.op ⋙ (G.over T).val.presheaf) :=
    (Presheaf.isSheaf_of_iso_iff e₃).mp
      ((associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T)).obj F).isSheaf
  have h₂ := (objEquiv B S hS T).inverse.op_comp_isSheaf ((topology B S hS).over T)
    (topology B (objScheme B S hS T) (contains_objScheme B S hS T)) ⟨_, hsh⟩
  exact (Presheaf.isSheaf_of_iso_iff
    (Functor.isoWhiskerRight (objEquiv B S hS T).op.counitIso
      (G.over T).val.presheaf)).mp h₂

/-- **A quasi-coherent module on `(Sch/S)_τ` is a sheaf for the fppf topology.** -/
public theorem isSheaf_fppf_of_isQuasicoherentOnSite
    (G : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))
    (hG : G.IsQuasicoherentOnSite) :
    Presheaf.IsSheaf (topology B S hS) G.val.presheaf := by
  obtain ⟨I, X, hX, hP⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation G).1 hG
  exact CategoryTheory.SiteGlueing.isSheaf_of_coversTop_of_isSheaf_over'
    (topology B S hS) hX G.val.presheaf G.isSheaf fun i =>
      isSheaf_fppf_over_of_hasGlobalPresentation B S hS τ (X i) (hP i)

/-- A quasi-coherent module on `(Sch/S)_fppf`, read for `τ`, is isomorphic to `𝓕^a` for a
quasi-coherent `𝒪_S`-module `𝓕`. -/
private theorem exists_isQuasicoherent_iso_restrictTopology
    (M : SheafOfModules.{u} (structureSheaf B S hS)) (hM : M.IsQuasicoherentOnSite) :
    (baseAssociatedModuleQcoh B S hS τ).essImage ((restrictTopology B S hS τ).obj M) := by
  obtain ⟨F, ⟨iso⟩⟩ :=
    AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule' B S hS M hM
  have := F.property
  exact ⟨F, ⟨(restrictTopologyAssociatedModuleIso B S hS τ F.obj).symm ≪≫
    (restrictTopology B S hS τ).mapIso iso⟩⟩

/-- **Essential surjectivity of `𝓕 ↦ 𝓕^a` at every `τ`.**  Every quasi-coherent `𝒪`-module on
the big `τ` site of `S` is isomorphic to `𝓕^a` for a quasi-coherent `𝒪_S`-module `𝓕`. -/
public theorem baseQuasicoherentIsEssImageAssociatedModule :
    SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf B S hS τ) ≤
      (baseAssociatedModuleQcoh B S hS τ).essImage := by
  intro G hG
  let G' : SheafOfModules.{u} (structureSheaf B S hS) :=
    ⟨G.val, isSheaf_fppf_of_isQuasicoherentOnSite B S hS τ G hG⟩
  have hG' : G'.IsQuasicoherentOnSite :=
    Stacks.SheafOfModules.isQuasicoherentOnSite_of_le (baseOverTopology_le_fppf B S hS τ)
      (structureSheaf B S hS) G' hG
  exact exists_isQuasicoherent_iso_restrictTopology B S hS τ G' hG'

/-- **A quasi-coherent module on `(Sch/S)_fppf`, read for a coarser topology `τ`, is
quasi-coherent on `(Sch/S)_τ`.** -/
public theorem isQuasicoherentOnSite_restrictTopology
    (M : SheafOfModules.{u} (structureSheaf B S hS)) (hM : M.IsQuasicoherentOnSite) :
    ((restrictTopology B S hS τ).obj M).IsQuasicoherentOnSite := by
  obtain ⟨F, ⟨iso⟩⟩ := exists_isQuasicoherent_iso_restrictTopology B S hS τ M hM
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso iso
    (isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent B S hS τ F.obj F.property)

add_to_stacks 03DX "clause (1) at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}: \
essential surjectivity of 𝓕 ↦ 𝓕ᵃ onto the quasi-coherent 𝒪-modules of the big τ site of S"
  baseQuasicoherentIsEssImageAssociatedModule

end AlgebraicGeometry.BigFppfOver

end
