module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.QuasicoherentTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSystemSmallEtaleModuleColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSystemSpaceModuleColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleColimitClauseTransferInto

/-!
# Descent of morphisms into a quasi-coherent module through a limit of affine schemes

For a cofiltered diagram of affine schemes with limit cone `c`, the faithfulness and fullness
clauses of Stacks 01ZR hold for morphisms from a module of finite presentation to a merely
quasi-coherent module at a stage.  This file states them as
`Stacks.ModuleColimit.PullbackSystem.FaithfulnessInto` and `.FullnessInto` for the Zariski
pullback system of the underlying schemes, from
`Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isAffine_of_isQuasicoherent`
and `.exists_map_of_pullback_canonical_of_isAffine_of_isQuasicoherent`, and carries them to the
small étale sites through the associated-module functor of Stacks 03DU (4), which is an
equivalence on quasi-coherent modules (Stacks 03DX (2)), and then to the algebraic spaces the
affine schemes represent.

## Main results

* `AlgebraicGeometry.SmallEtale.zariskiSystem_faithfulnessInto_of_isAffine` and
  `AlgebraicGeometry.SmallEtale.zariskiSystem_fullnessInto_of_isAffine`: the two clauses on the
  Zariski sites.
* `AlgebraicGeometry.SmallEtale.smallEtalePullbackSystem_faithfulnessInto_of_isAffine` and
  `AlgebraicGeometry.SmallEtale.smallEtalePullbackSystem_fullnessInto_of_isAffine`: the two
  clauses on the small étale sites.
* `AlgebraicGeometry.Space.affineSpacePullbackSystem_faithfulnessInto` and
  `AlgebraicGeometry.Space.affineSpacePullbackSystem_fullnessInto`: the two clauses on the
  algebraic spaces represented by an inverse system of affine schemes of the site, through
  `AlgebraicGeometry.Space.affineSpaceTransfer`.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 08K4](https://stacks.math.columbia.edu/tag/08K4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {I : Type u} [Category.{u} I] [IsCofiltered I]
  (X : I ⥤ B.Scheme) (c : Cone X)

/-- **Stacks 01ZR (3) into a quasi-coherent module**, for the Zariski system of a cofiltered
diagram of affine schemes. -/
theorem zariskiSystem_faithfulnessInto_of_isAffine
    (hX : ∀ i, _root_.AlgebraicGeometry.IsAffine ((X ⋙ B.inclusion).obj i))
    (hc : IsLimit (B.inclusion.mapCone c)) :
    (zariskiSystem B X c).FaithfulnessInto fun _ N ↦ N.IsQuasicoherent := by
  intro k M N hM hN φ ψ h
  have : M.IsFinitePresentation := hM
  have : N.IsQuasicoherent := hN
  have : ∀ i, _root_.AlgebraicGeometry.IsAffine ((X ⋙ B.inclusion).obj i) := hX
  exact Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isAffine_of_isQuasicoherent
    (X ⋙ B.inclusion) (B.inclusion.mapCone c) hc k M N φ ψ h

/-- **Stacks 01ZR (2) into a quasi-coherent module**, for the Zariski system of a cofiltered
diagram of affine schemes. -/
theorem zariskiSystem_fullnessInto_of_isAffine
    (hX : ∀ i, _root_.AlgebraicGeometry.IsAffine ((X ⋙ B.inclusion).obj i))
    (hc : IsLimit (B.inclusion.mapCone c)) :
    (zariskiSystem B X c).FullnessInto fun _ N ↦ N.IsQuasicoherent := by
  intro k M N hM hN φ
  have : M.IsFinitePresentation := hM
  have : N.IsQuasicoherent := hN
  have : ∀ i, _root_.AlgebraicGeometry.IsAffine ((X ⋙ B.inclusion).obj i) := hX
  open Stacks.AlgebraicGeometry in
  obtain ⟨j, e, φj, h⟩ :=
    ModuleLimits.exists_map_of_pullback_canonical_of_isAffine_of_isQuasicoherent
      (X ⋙ B.inclusion) (B.inclusion.mapCone c) hc k M N φ
  refine ⟨j, e, φj, ?_⟩
  have h₂ : (Scheme.Modules.pullback (schemeHom B (X := c.pt) (c.π.app j))).map φj ≫
      ((zariskiSystem B X c).comp e).inv.app N = ((zariskiSystem B X c).comp e).inv.app M ≫ φ := by
    simp only [Iso.symm_inv, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    rw [Stacks.AlgebraicGeometry.ModuleLimits.canHom,
      Stacks.AlgebraicGeometry.ModuleLimits.canHom] at h
    exact h
  rw [← reassoc_of% h₂]
  simp

/-- Every quasi-coherent module on the small étale site of a scheme is associated to a
quasi-coherent module on the Zariski site. -/
theorem exists_isQuasicoherent_associatedModule_iso (S : Scheme.{u}) (hS : B.Contains S)
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite) :
    ∃ M : S.Modules, M.IsQuasicoherent ∧ Nonempty ((associatedModule B S hS).obj M ≅ G) := by
  obtain ⟨M, ⟨e⟩⟩ := quasicoherentIsEssImageAssociatedModule B S hS G hG
  exact ⟨M.obj, M.property, ⟨e⟩⟩

/-- **Stacks 01ZR (3) into a quasi-coherent module on the small étale sites** of a cofiltered
diagram of affine schemes. -/
theorem smallEtalePullbackSystem_faithfulnessInto_of_isAffine
    (hX : ∀ i, _root_.AlgebraicGeometry.IsAffine ((X ⋙ B.inclusion).obj i))
    (hc : IsLimit (B.inclusion.mapCone c)) :
    (smallEtalePullbackSystem B X c).FaithfulnessInto fun _ N ↦ N.IsQuasicoherentOnSite :=
  (associatedModuleTransferUp B X c).faithfulnessInto (fun _ _ h ↦ h)
    (fun _ G hG ↦ exists_isQuasicoherent_associatedModule_iso B _ _ G hG)
    (zariskiSystem_faithfulnessInto_of_isAffine B X c hX hc)

/-- **Stacks 01ZR (2) into a quasi-coherent module on the small étale sites** of a cofiltered
diagram of affine schemes. -/
theorem smallEtalePullbackSystem_fullnessInto_of_isAffine
    (hX : ∀ i, _root_.AlgebraicGeometry.IsAffine ((X ⋙ B.inclusion).obj i))
    (hc : IsLimit (B.inclusion.mapCone c)) :
    (smallEtalePullbackSystem B X c).FullnessInto fun _ N ↦ N.IsQuasicoherentOnSite :=
  (associatedModuleTransferUp B X c).fullnessInto (fun _ _ h ↦ h)
    (fun _ G hG ↦ exists_isQuasicoherent_associatedModule_iso B _ _ G hG)
    (zariskiSystem_fullnessInto_of_isAffine B X c hX hc)

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type u} [Category.{u} I] [IsCofiltered I] (V : I ⥤ BigFppfOver B S hS) (c : Cone V)
  (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
  (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))

include hV hc in
/-- **Stacks 01ZR (3) into a quasi-coherent module**, on the small étale sites of the schemes
underlying an inverse system of affine schemes of the site. -/
theorem etalePullbackSystem_faithfulnessInto :
    (etalePullbackSystem B S hS V c).FaithfulnessInto fun _ N ↦ N.IsQuasicoherentOnSite  := by
  exact SmallEtale.smallEtalePullbackSystem_faithfulnessInto_of_isAffine (associatedBigEtaleSite B)
    (etaleDiagram B S hS V) (etaleCone B S hS V c) hV hc

include hV hc in
/-- **Stacks 01ZR (2) into a quasi-coherent module**, on the small étale sites of the schemes
underlying an inverse system of affine schemes of the site. -/
theorem etalePullbackSystem_fullnessInto :
    (etalePullbackSystem B S hS V c).FullnessInto fun _ N ↦ N.IsQuasicoherentOnSite  := by
  exact SmallEtale.smallEtalePullbackSystem_fullnessInto_of_isAffine (associatedBigEtaleSite B)
    (etaleDiagram B S hS V) (etaleCone B S hS V c) hV hc

include hV hc in
/-- **Stacks 07V7 (3) into a quasi-coherent module, for an inverse system of affine schemes**, on
their algebraic spaces: two morphisms from a module of finite presentation to a quasi-coherent
module at a stage whose inverse images to the limit agree have equal inverse images at a later
stage. -/
theorem affineSpacePullbackSystem_faithfulnessInto :
    (affineSpacePullbackSystem B S hS V c).FaithfulnessInto fun _ N ↦ N.IsQuasicoherentOnSite :=
  (affineSpaceTransfer B S hS V c).faithfulnessInto
    (fun _ N hN ↦ isQuasicoherentOnSite_representedSmallEtaleModuleInverse N hN)
    (fun _ _ h ↦ h) (etalePullbackSystem_faithfulnessInto B S hS V c hV hc)

include hV hc in
/-- **Stacks 07V7 (2) into a quasi-coherent module, for an inverse system of affine schemes**, on
their algebraic spaces: a morphism from the inverse image to the limit of a module of finite
presentation at a stage to that of a quasi-coherent module is, through the comparisons
`AlgebraicGeometry.Space.modulePullbackTriangle`, the inverse image of a morphism at a later
stage. -/
theorem affineSpacePullbackSystem_fullnessInto :
    (affineSpacePullbackSystem B S hS V c).FullnessInto fun _ N ↦ N.IsQuasicoherentOnSite :=
  (affineSpaceTransfer B S hS V c).fullnessInto
    (fun _ N hN ↦ isQuasicoherentOnSite_representedSmallEtaleModuleInverse N hN)
    (fun _ _ h ↦ h) (etalePullbackSystem_fullnessInto B S hS V c hV hc)

end AlgebraicGeometry.Space

end
