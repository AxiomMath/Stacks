module

public import StacksFrontier.AlgebraicGeometry.Descent.SmallAffineZariskiCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteFlatCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.AffineEtaleLiftedCartesian
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.SmallAffineDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits

/-!
# The affine Zariski charts of a scheme as a lifted ringed site

Let `S` be a scheme in a big fppf site `B`. Its small affine Zariski site `S_{affine, Zar}` —
the affine open subschemes of `S` with the standard Zariski coverings (Stacks 020T (4)), read in
the big Zariski site carried by `B` (Stacks 03FF) — is essentially small, and this file
transports it, with the global functions as structure sheaf, to its small model in the universe
`max (u + 1) m` of the modules (`AlgebraicGeometry.ZariskiCharts.zariskiChartLiftedSite`), with
the rings raised to that universe. It then identifies the subcategory of the derived category of
sheaves of modules on that site appearing in Stacks 0GZS — the objects `K` with `Rε_*K`
cartesian — with the objects with cartesian cohomology sheaves.

This is the Zariski counterpart, for a scheme, of
`RepresentableQC/AffineEtaleLiftedCartesian.lean`.

## Main definitions

* `AlgebraicGeometry.ZariskiCharts.zariskiChartRingedSite`: the small affine Zariski ringed site
  of `S`.
* `AlgebraicGeometry.ZariskiCharts.zariskiChartLiftedSite`: its transport to the small model in
  the universe `max (u + 1) m`.

## Main results

* `AlgebraicGeometry.ZariskiCharts.isFlatCofinal_smallAffineZariski` and
  `AlgebraicGeometry.ZariskiCharts.isFlatCofinal_zariskiChartLiftedSite`: the small affine Zariski
  site and its lift are flatly cofinal for their scheme functors.
* `AlgebraicGeometry.ZariskiCharts.isCartesianPushforward_zariskiChartLiftedSite_iff`: on the
  lift, the subcategory of Stacks 0GZS is that of the objects with cartesian cohomology sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.ZariskiCharts

open Stacks.AffineSiteBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

include hS in
/-- `S` lies in the big Zariski site carried by `B`, the two containment predicates being the
same size bound; stated separately because instance search does not identify them. -/
theorem zariskiContains : B.toBigZariskiSite.Contains S := hS

/-- **The small affine Zariski ringed site of `S`**: the affine opens of `S`, read in the big
Zariski site carried by `B`, with the standard Zariski coverings and the sheaf of global
functions. -/
noncomputable abbrev zariskiChartRingedSite : RingedSite.{u + 1, u, u} :=
  smallAffineZariskiRingedSite B.toBigZariskiSite S (zariskiContains B S hS)

/-- **The lift of the small affine Zariski ringed site of `S` to the universe `max (u + 1) m`**:
its transport along the comparison with its small model at that universe, with the section
rings raised to it. -/
noncomputable abbrev zariskiChartLiftedSite :
    RingedSite.{max (u + 1) m, max (u + 1) m, max (u + 1) m} :=
  haveI := essentiallySmall_lift.{max (u + 1) m, u}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  (zariskiChartRingedSite B S hS).transport.{max (u + 1) m}
    (equivSmallModel.{max (u + 1) m}
      (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS)))

/-- **The small affine Zariski site of `S` is flatly cofinal for its scheme functor**: every
covering sieve contains a finite covering family of affine opens, which is a flat covering of
affine schemes. -/
theorem isFlatCofinal_smallAffineZariski :
    IsFlatCofinal (SmallAffineZariski.toScheme B.toBigZariskiSite S (zariskiContains B S hS))
      (SmallAffineZariski.topology B.toBigZariskiSite S (zariskiContains B S hS)) := by
  intro x T hT
  obtain ⟨E, hfin, hE, hEJ, hle⟩ := Stacks.Sites.exists_finite_flat_covering_refinement
    (SmallAffineZariski.toScheme B.toBigZariskiSite S (zariskiContains B S hS))
    (SmallAffineZariski.precoverage B.toBigZariskiSite S (zariskiContains B S hS))
    (SmallAffineZariski.covering_finite_flat B.toBigZariskiSite S (zariskiContains B S hS)) T hT
  let e : Fin (Nat.card E.I₀) ≃ E.I₀ := (Finite.equivFin E.I₀).symm
  have hs : (E.reindex e).sieve₀ = E.sieve₀ :=
    congrArg Sieve.generate (E.presieve₀_reindex e)
  refine ⟨E.reindex e, inferInstanceAs (Finite (Fin _)), ?_, hs ▸ hle, hs ▸ hEJ⟩
  have hpr :
      ((E.reindex e).map
        (SmallAffineZariski.toScheme B.toBigZariskiSite S (zariskiContains B S hS))).presieve₀ =
      (E.map
        (SmallAffineZariski.toScheme B.toBigZariskiSite S (zariskiContains B S hS))).presieve₀ := by
    rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_map,
      E.presieve₀_reindex e]
  exact hpr ▸ hE

/-- The scheme underlying an object of the lifted chart site: the affine open of `S` it
corresponds to in the small model. -/
noncomputable abbrev zariskiChartLiftedToScheme :
    (zariskiChartLiftedSite.{u, m} B S hS).C ⥤ Scheme.{u} :=
  haveI := essentiallySmall_lift.{max (u + 1) m, u}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  (equivSmallModel.{max (u + 1) m}
      (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))).inverse ⋙
    SmallAffineZariski.toScheme B.toBigZariskiSite S (zariskiContains B S hS)

/-- The lifted chart site has fibre products, the small affine Zariski site having them. -/
instance zariskiChartLiftedSite_hasPullbacks :
    HasPullbacks (zariskiChartLiftedSite.{u, m} B S hS).C :=
  haveI := essentiallySmall_lift.{max (u + 1) m, u}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  Adjunction.hasLimitsOfShape_of_equivalence
    (equivSmallModel.{max (u + 1) m}
      (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))).inverse

/-- The scheme functor of the lifted chart site preserves fibre products. -/
instance zariskiChartLiftedToScheme_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (zariskiChartLiftedToScheme.{u, m} B S hS) :=
  haveI := essentiallySmall_lift.{max (u + 1) m, u}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  comp_preservesLimitsOfShape _ _

/-- The schemes underlying the objects of the lifted chart site are affine. -/
instance isAffine_zariskiChartLiftedToScheme (y : (zariskiChartLiftedSite.{u, m} B S hS).C) :
    IsAffine ((zariskiChartLiftedToScheme.{u, m} B S hS).obj y) :=
  SmallAffineZariski.isAffine_toScheme_obj B.toBigZariskiSite S (zariskiContains B S hS) _

/-- **The lifted chart site is flatly cofinal for its scheme functor**: flat cofinality of the
small affine Zariski site, transported along its small model. -/
theorem isFlatCofinal_zariskiChartLiftedSite :
    IsFlatCofinal (zariskiChartLiftedToScheme.{u, m} B S hS)
      (zariskiChartLiftedSite.{u, m} B S hS).J :=
  have := essentiallySmall_lift.{max (u + 1) m, u}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  (isFlatCofinal_smallAffineZariski B S hS).inducedTopology
    (equivSmallModel.{max (u + 1) m}
      (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS)))

open Stacks.ModulesOnACategory.ChaoticComparison
  Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange in
/-- **On the lifted chart site, the subcategory of Stacks 0GZS is the subcategory of objects
with cartesian cohomology sheaves**: an object `K` of the derived category of sheaves of modules
on `AlgebraicGeometry.ZariskiCharts.zariskiChartLiftedSite` has `Rε_*K` cartesian exactly when
every cohomology sheaf of `K` is cartesian. The inputs are flat cofinality of the site for its
scheme functor, whose morphisms are open immersions, hence flat, and the identification of its
structure sheaf with the global functions of that functor raised to the module universe. -/
theorem isCartesianPushforward_zariskiChartLiftedSite_iff
    (K : DerivedCategory (SheafOfModules.{max (u + 1) m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiChartLiftedSite.{u, m} B S hS).O))) :
    letI := Stacks.ModulesOnACategory.TildePullback.commSections_ringSheaf
      (zariskiChartLiftedSite.{u, m} B S hS)
    IsCartesianPushforward.{max (u + 1) m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiChartLiftedSite.{u, m} B S hS).O)
        (baseChangeDataOfComm.{max (u + 1) m, max (u + 1) m, max (u + 1) m, max (u + 1) m}
          (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiChartLiftedSite.{u, m} B S hS).O).obj
          Stacks.TerminalBaseChange.CommSections.mul_comm) K ↔
      DerivedCategoryB.derivedCategoryB (cartesianSheaves.{max (u + 1) m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiChartLiftedSite.{u, m} B S hS).O)) K := by
  have := essentiallySmall_lift.{max (u + 1) m, u}
    (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))
  exact isCartesianPushforward_iff_of_ringTransport.{u, max (u + 1) m}
    (zariskiChartLiftedSite.{u, m} B S hS) (zariskiChartLiftedToScheme.{u, m} B S hS)
    (isFlatCofinal_zariskiChartLiftedSite.{u, m} B S hS)
    (Stacks.UniverseLift.uliftRingTransport.{max (u + 1) m}
      (rings (zariskiChartLiftedToScheme.{u, m} B S hS)))
    (fun f => SmallAffineZariski.flat_toScheme_map B.toBigZariskiSite S (zariskiContains B S hS)
      ((equivSmallModel.{max (u + 1) m}
        (SmallAffineZariski B.toBigZariskiSite S (zariskiContains B S hS))).inverse.map f)) K

end AlgebraicGeometry.ZariskiCharts
