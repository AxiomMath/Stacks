module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteFlatCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.AffineChartsQuasicoherentDerived
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSiteLiftedCartesian

/-!
# The subcategory of Stacks 0GZS on the lifted affine étale site is `D_QCoh`

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `Y` be
its lifted affine étale site (`AlgebraicGeometry.Space.affineEtaleLiftedSite`): the affine étale
charts of `F` with the étale topology (Stacks 0H01), transported to a small model in the
universe `max u m` of the modules, with the rings of functions of the charts raised to that
universe. This file identifies the subcategory of the derived category of sheaves of modules on
`Y` appearing in Stacks 0GZS — the objects `K` with `Rε_*K` cartesian — with `D_QCoh(𝒪_F)`.

## Main results

* `AlgebraicGeometry.Space.AffineEtale.isFlatCofinal`: the affine étale site of `F` is flatly
  cofinal for its scheme functor, and so is `Y`
  (`AlgebraicGeometry.Space.isFlatCofinal_affineEtaleLiftedSite`).
* `AlgebraicGeometry.Space.isCartesianPushforward_affineEtaleLiftedSite_iff`: on `Y`, the
  subcategory of Stacks 0GZS is the subcategory of the objects with cartesian cohomology sheaves.
* `AlgebraicGeometry.Space.cartesianPushforwardEquivalenceQuasicoherentDerived`: **that
  subcategory is equivalent to `D_QCoh(𝒪_F)`.**
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

open Stacks.AffineSiteBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The affine étale site of `F` is flatly cofinal for its underlying scheme functor**: every
covering sieve contains a finite covering family of affine étale charts, which is a flat
covering of affine schemes. -/
theorem AffineEtale.isFlatCofinal :
    IsFlatCofinal (AffineEtale.toScheme B S hS F) (AffineEtale.topology B S hS F) := by
  intro x T hT
  obtain ⟨E, hfin, hE, hEJ, hle⟩ := Stacks.Sites.exists_finite_flat_covering_refinement
    (AffineEtale.toScheme B S hS F) (AffineEtale.precoverage B S hS F)
    (affineEtale_covering_finite_flat B S hS F) T hT
  let e : Fin (Nat.card E.I₀) ≃ E.I₀ := (Finite.equivFin E.I₀).symm
  have hs : (E.reindex e).sieve₀ = E.sieve₀ :=
    congrArg Sieve.generate (E.presieve₀_reindex e)
  refine ⟨E.reindex e, inferInstanceAs (Finite (Fin _)), ?_, hs ▸ hle, hs ▸ hEJ⟩
  have hpr : ((E.reindex e).map (AffineEtale.toScheme B S hS F)).presieve₀ =
      (E.map (AffineEtale.toScheme B S hS F)).presieve₀ := by
    rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_map,
      E.presieve₀_reindex e]
  exact hpr ▸ hE

/-- The scheme underlying an object of the lifted affine étale site
`AlgebraicGeometry.Space.affineEtaleLiftedSite`: the scheme of the affine étale chart it
corresponds to in the small model. -/
noncomputable abbrev affineEtaleLiftedToScheme :
    (affineEtaleLiftedSite.{u, m} B S hS F hF).C ⥤ Scheme.{u} :=
  haveI := essentiallySmall_lift.{m, u} (AffineEtale B S hS F)
  (equivSmallModel.{max u m} (AffineEtale B S hS F)).inverse ⋙ AffineEtale.toScheme B S hS F

/-- The lifted affine étale site has fibre products, the affine étale site having them. -/
instance affineEtaleLiftedSite_hasPullbacks :
    HasPullbacks (affineEtaleLiftedSite.{u, m} B S hS F hF).C :=
  haveI := essentiallySmall_lift.{m, u} (AffineEtale B S hS F)
  Adjunction.hasLimitsOfShape_of_equivalence
    (equivSmallModel.{max u m} (AffineEtale B S hS F)).inverse

/-- The scheme functor of the lifted affine étale site preserves fibre products. -/
instance affineEtaleLiftedToScheme_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (affineEtaleLiftedToScheme.{u, m} B S hS F hF) :=
  haveI := essentiallySmall_lift.{m, u} (AffineEtale B S hS F)
  comp_preservesLimitsOfShape _ _

/-- The schemes underlying the objects of the lifted affine étale site are affine. -/
instance isAffine_affineEtaleLiftedToScheme
    (y : (affineEtaleLiftedSite.{u, m} B S hS F hF).C) :
    IsAffine ((affineEtaleLiftedToScheme.{u, m} B S hS F hF).obj y) :=
  AffineEtale.isAffine_toScheme B S hS F _

/-- **The lifted affine étale site is flatly cofinal for its scheme functor**: flat cofinality of
the affine étale site, transported along its small model. -/
theorem isFlatCofinal_affineEtaleLiftedSite :
    IsFlatCofinal (affineEtaleLiftedToScheme.{u, m} B S hS F hF)
      (affineEtaleLiftedSite.{u, m} B S hS F hF).J :=
  have := essentiallySmall_lift.{m, u} (AffineEtale B S hS F)
  (AffineEtale.isFlatCofinal B S hS F).inducedTopology
    (equivSmallModel.{max u m} (AffineEtale B S hS F))

open Stacks.ModulesOnACategory.ChaoticComparison
  Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange in
/-- **On the lifted affine étale site, the subcategory of Stacks 0GZS is the subcategory of
objects with cartesian cohomology sheaves**: an object `K` of the derived category of sheaves of
modules on `AlgebraicGeometry.Space.affineEtaleLiftedSite` has `Rε_*K` cartesian exactly when
every cohomology sheaf of `K` is cartesian. The three inputs of
`ChaoticComparison.isCartesianPushforward_iff_isCartesianPresheaf_homology`
are supplied by `Stacks.AffineSiteBaseChange.isCartesianPushforward_iff_of_ringTransport`: the
lifted site is flatly cofinal for the scheme functor of its affine étale charts, whose morphisms
are flat, and its structure sheaf is the global functions of that functor with the rings raised
to the module universe. -/
theorem isCartesianPushforward_affineEtaleLiftedSite_iff
    (K : DerivedCategory (SheafOfModules.{max u m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleLiftedSite.{u, m} B S hS F hF).O))) :
    letI := Stacks.ModulesOnACategory.TildePullback.commSections_ringSheaf
      (affineEtaleLiftedSite.{u, m} B S hS F hF)
    IsCartesianPushforward.{max u m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleLiftedSite.{u, m} B S hS F hF).O)
        (baseChangeDataOfComm.{max u m, max u m, max u m, max u m}
          (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleLiftedSite.{u, m} B S hS F hF).O).obj
          Stacks.TerminalBaseChange.CommSections.mul_comm) K ↔
      DerivedCategoryB.derivedCategoryB (cartesianSheaves.{max u m}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (affineEtaleLiftedSite.{u, m} B S hS F hF).O)) K :=
  have := essentiallySmall_lift.{m, u} (AffineEtale B S hS F)
  isCartesianPushforward_iff_of_ringTransport.{u, m}
    (affineEtaleLiftedSite.{u, m} B S hS F hF) (affineEtaleLiftedToScheme.{u, m} B S hS F hF)
    (isFlatCofinal_affineEtaleLiftedSite.{u, m} B S hS F hF)
    (Stacks.UniverseLift.uliftRingTransport.{m}
      (rings (affineEtaleLiftedToScheme.{u, m} B S hS F hF)))
    (fun f => AffineEtale.flat_toScheme_map B S hS F
      ((equivSmallModel.{max u m} (AffineEtale B S hS F)).inverse.map f)) K

open Stacks.ModulesOnACategory.ChaoticComparison
  Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange in
/-- **The subcategory of Stacks 0GZS on the lifted affine étale site of `F` is `D_QCoh(𝒪_F)`.**
For module sections in `max u m`, the full subcategory of the derived category of sheaves of
modules on `AlgebraicGeometry.Space.affineEtaleLiftedSite` of the objects `K` with `Rε_*K`
cartesian is equivalent to `D_QCoh(𝒪_F)`, the derived category of `𝒪_F`-modules with
quasi-coherent cohomology sheaves.

The subcategory is that of the objects with cartesian cohomology sheaves
(`AlgebraicGeometry.Space.isCartesianPushforward_affineEtaleLiftedSite_iff`), and the derived
functor of restriction to the affine étale charts followed by the transport to the small model
identifies those with `D_QCoh(𝒪_F)`
(`AlgebraicGeometry.Space.quasicoherentDerivedCategoryEquivalenceCartesian`): an `𝒪_F`-module is
quasi-coherent exactly when it is cartesian on affine charts, Descent, Proposition 03DX (2). The
functor of the equivalence is the inclusion followed by the derived functor of the inverse of
`AlgebraicGeometry.Space.affineEtaleLiftedModulesEquivalence`.

The source is, unfolded, `IsCartesianPushforwardOn` (in the namespace
`Stacks.Cohomology.SubsiteQuasiCoherentEquivalence`) of the lifted affine étale site. -/
noncomputable def cartesianPushforwardEquivalenceQuasicoherentDerived :
    letI := Stacks.ModulesOnACategory.TildePullback.commSections_ringSheaf
      (affineEtaleLiftedSite.{u, m} B S hS F hF)
    (IsCartesianPushforward.{max u m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleLiftedSite.{u, m} B S hS F hF).O)
        (baseChangeDataOfComm.{max u m, max u m, max u m, max u m}
          (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleLiftedSite.{u, m} B S hS F hF).O).obj
          Stacks.TerminalBaseChange.CommSections.mul_comm)).FullSubcategory ≌
      QuasicoherentDerivedCategory.{u, max u m} B S hS F hF :=
  letI := Stacks.ModulesOnACategory.TildePullback.commSections_ringSheaf
    (affineEtaleLiftedSite.{u, m} B S hS F hF)
  letI : (DerivedCategoryB.derivedCategoryB (cartesianSheaves.{max u m}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (affineEtaleLiftedSite.{u, m} B S hS F hF).O))).IsClosedUnderIsomorphisms :=
    ⟨fun {_ _} e hX n => (cartesianSheaves.{max u m}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (affineEtaleLiftedSite.{u, m} B S hS F hF).O)).prop_of_iso
        ((DerivedCategory.homologyFunctor _ n).mapIso e) (hX n)⟩
  (CategoryTheory.Equivalence.refl.congrFullSubcategory (by
      ext K
      exact (isCartesianPushforward_affineEtaleLiftedSite_iff.{u, m} B S hS F hF K).symm)).trans
    (quasicoherentDerivedCategoryEquivalenceCartesian.{u, m} B S hS F hF).symm

end AlgebraicGeometry.Space

end
