module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenCoarserSites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmoothEqualsEtale
public import StacksCore.Tactic.StacksAttribute

/-!
# The big smooth and big étale topologies carried by one chosen big fppf site are equal

`AlgebraicGeometry.Scheme.grothendieckTopology_smooth_eq_etaleTopology` identifies the smooth and
the étale topology on *all* schemes. This file carries that identification over to the
size-bounded setting of Stacks 03FF, where a chosen big fppf site `B` carries all five
topologies on its one category `Sch_κ`, and concludes with the localized topologies over a base
scheme:

`B.smoothTopology = B.etaleTopology`, hence
`BigFppfOver.baseOverTopology B S hS .smooth = BigFppfOver.baseOverTopology B S hS .etale`.

## What has to be added to the unbounded statement

Two things, and neither is mathematics about smoothness.

First, the refining étale family produced by Tag 055V is a family of *arbitrary* schemes, while
a covering family of `B` must consist of objects below `B`'s size cutoff. That is exactly what
`AlgebraicGeometry.BigEtaleSite.exists_covering_refining_etale_cover` (Tag 03WW) repairs: it
refines any étale family over an object of a bounded category by one internal to it, by passing
to affine opens, whose sizes are controlled by
`AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion` and
`AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact`. It applies here because
`AlgebraicGeometry.BigFppfSite.toBigEtaleSite` has `B`'s own cutoff, syntactically.

Second, the resulting family must be one of `B`'s *chosen* families, i.e. satisfy
`AlgebraicGeometry.BigFppfSite.IsCovering`. Tag 03WW already delivers the covering bound, and
`AlgebraicGeometry.covBounded_iff_chosenCovering` converts a bounded étale family into a chosen
one, the fppf condition being implied by the étale one.

Refinement is then transported from the ambient category of schemes back into `Sch_κ` by
`CategoryTheory.PreZeroHypercover.factorsThru_presieve₀_of_map`, the inclusion of a
size-bounded category of schemes being fully faithful.

## Main results

* `AlgebraicGeometry.BigFppfSite.exists_etaleCovering_refining_smoothCovering`: a chosen smooth
  covering presieve of `Sch_κ` is refined by a chosen étale covering presieve of `Sch_κ`.
* `AlgebraicGeometry.BigFppfSite.etalePrecoverage_le_smoothPrecoverage`: the easy direction.
* `AlgebraicGeometry.BigFppfSite.smoothTopology_eq_etaleTopology`: **the two topologies are
  equal.**
* `AlgebraicGeometry.BigFppfSite.baseTopology_smooth_eq_etale` and
  `AlgebraicGeometry.BigFppfOver.baseOverTopology_smooth_eq_etale`: the same equality through
  the `AlgebraicGeometry.SiteKind` indexing, and after localizing over a base scheme.
* `AlgebraicGeometry.BigFppfOver.isSheaf_baseOverTopology_smooth_iff_etale` and
  `AlgebraicGeometry.BigFppfOver.sheafCategory_baseOverTopology_smooth_eq_etale`: hence
  `(Sch/S)_smooth` and `(Sch/S)_etale` have the same sheaves, and the same category of sheaves.

## References

* [Stacks Project, Tag 055V](https://stacks.math.columbia.edu/tag/055V)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 03WW](https://stacks.math.columbia.edu/tag/03WW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace BigFppfSite

variable (B : BigFppfSite.{u})

/-- A chosen smooth covering presieve of the common category of schemes of a big fppf site is
refined by a chosen *étale* covering presieve of that same category.

This is Tag 055V in the size-bounded setting: the étale refinement of the smooth family is
first produced among all schemes, then pushed inside the bounded category by Tag 03WW, and
finally recognised as one of `B`'s chosen families. -/
theorem exists_etaleCovering_refining_smoothCovering {X : B.Schemes} (R : Presieve X)
    (hR : R ∈ B.smoothPrecoverage X) :
    ∃ R' ∈ B.etalePrecoverage X, Presieve.FactorsThru R' R := by
  obtain ⟨E, rfl, hE⟩ := hR
  -- The image family in all schemes is a jointly surjective family of smooth morphisms.
  have hsm : (E.map B.inclusion).presieve₀ ∈
      Scheme.precoverage (@Smooth.{u}) (B.inclusion.obj X) :=
    (smoothCovering_iff_mem_precoverage B.cutoff ⟨X, E⟩).mp hE.2
  -- Tag 055V, among all schemes.
  obtain ⟨R'', hR''et, hfac⟩ := exists_etale_refinement_of_mem_smoothPrecoverage _ hsm
  -- Tag 03WW: refine it again by a family internal to the bounded category.
  obtain ⟨𝒱, h𝒱, ⟨φ⟩⟩ := BigEtaleSite.exists_covering_refining_etale_cover B.toBigEtaleSite
    (T := X) R''.preZeroHypercover (by rwa [Presieve.presieve₀_preZeroHypercover])
  refine ⟨𝒱.presieve₀, ⟨𝒱, rfl, ?_⟩, ?_⟩
  · exact (covBounded_iff_chosenCovering B Scheme.etalePrecoverage
      Scheme.etalePrecoverage_le_fppfPrecoverage _ (fun _ => Iff.rfl) ⟨X, 𝒱⟩).mp h𝒱
  · refine PreZeroHypercover.factorsThru_presieve₀_of_map B.inclusion ?_
    refine Presieve.FactorsThru.trans ?_ hfac
    have hφ := φ.factorsThru_presieve₀
    rwa [Presieve.presieve₀_preZeroHypercover] at hφ

/-- A chosen étale covering family of a big fppf site is a chosen smooth covering family, since
an étale morphism is smooth. Hence the étale precoverage of the common category is contained in
the smooth one. -/
theorem etalePrecoverage_le_smoothPrecoverage : B.etalePrecoverage ≤ B.smoothPrecoverage := by
  intro X R hR
  obtain ⟨E, rfl, hE⟩ := hR
  exact ⟨E, rfl, hE.1, (smoothCovering_iff_mem_precoverage B.cutoff ⟨X, E⟩).mpr
    (Scheme.etalePrecoverage_le_smoothPrecoverage _ hE.2)⟩

/-- **The big smooth and the big étale topology carried by one chosen big fppf site are equal.**

Both are generated by a collection of chosen covering families of the one category `Sch_κ` of
Stacks 03FF, and the two collections refine each other: an étale family is a smooth family, and
a smooth family is refined by an étale one by Tag 055V. -/
theorem smoothTopology_eq_etaleTopology : B.smoothTopology = B.etaleTopology :=
  Precoverage.toGrothendieck_eq_of_refines _ _
    (fun _ R hR => B.exists_etaleCovering_refining_smoothCovering R hR)
    fun _ R hR => ⟨R, B.etalePrecoverage_le_smoothPrecoverage _ hR,
      Presieve.factorsThru_of_le _ _ le_rfl⟩

/-- The smooth and étale entries of the five topologies indexed by
`AlgebraicGeometry.SiteKind` are the same topology. -/
theorem baseTopology_smooth_eq_etale :
    B.baseTopology .smooth = B.baseTopology .etale :=
  B.smoothTopology_eq_etaleTopology

end BigFppfSite

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The localized big smooth and big étale topologies on the big fppf category over `S` are the
same topology: `(\Sch/S)_{smooth}` and `(\Sch/S)_\etale` are the same site, not merely sites
with the same sheaves. -/
theorem baseOverTopology_smooth_eq_etale :
    baseOverTopology B S hS .smooth = baseOverTopology B S hS .etale :=
  congrArg (fun J => GrothendieckTopology.over J (B.obj hS)) B.baseTopology_smooth_eq_etale

/-- A presheaf on the big fppf category over `S` is a sheaf for the localized smooth topology
exactly when it is a sheaf for the localized étale topology — because the two topologies are
the same, so this holds for sheaves valued in any category. -/
theorem isSheaf_baseOverTopology_smooth_iff_etale {A : Type*} [Category A]
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (baseOverTopology B S hS .smooth) P ↔
      Presheaf.IsSheaf (baseOverTopology B S hS .etale) P := by
  rw [baseOverTopology_smooth_eq_etale]

/-- The two categories of sheaves are the *same* category, not merely equivalent ones.

This is what makes the quasi-coherent comparison at `τ = smooth` the one at `τ = étale` rather
than a second theorem. The coefficient sheaf of `QCoh((Sch/S)_τ, 𝒪)` is
`AlgebraicGeometry.FibredSite.baseRingStructureSheaf B S hS τ`, whose underlying presheaf is
independent of `τ` — `AlgebraicGeometry.FibredSite.baseRingStructureSheaf_obj` holds by `rfl`,
the sheaf condition for the coarser topology being obtained by restriction from the fppf one —
so at `τ = smooth` and `τ = étale` it is one presheaf, now over one topology. -/
theorem sheafCategory_baseOverTopology_smooth_eq_etale (A : Type*) [Category A] :
    Sheaf (baseOverTopology B S hS .smooth) A = Sheaf (baseOverTopology B S hS .etale) A :=
  congrArg (fun J => Sheaf J A) (baseOverTopology_smooth_eq_etale B S hS)

end BigFppfOver

end AlgebraicGeometry

end
