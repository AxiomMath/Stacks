module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.OverSliceContinuity
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# A big `τ`-site is one of the five topologies on a chosen big fppf site

A big site of a topology `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`
(`AlgebraicGeometry.BigSite τ`) is its own structure, with its own cutoff `κ` and its own chosen
bounded system of `τ`-covering families. A chosen big fppf site carries five topologies on its
category of schemes, `AlgebraicGeometry.BigFppfSite.baseTopology`, the one of `τ` being cut out
by the chosen fppf families which are `τ`-coverings. This file shows the two constructions give
the same site: at the big fppf site `AlgebraicGeometry.BigFppfSite.ofCutoff` with the cutoff `κ`
of the big `τ`-site, the categories of schemes agree on the nose and so do the two topologies of
`τ`. In both, a sieve covers exactly when it contains the presieve of a `τ`-covering family of
`Sch_κ`, since every `τ`-covering family has the same presieve as a chosen one in either system.

So everything the library proves on the big fppf category over `S` for a `τ : SiteKind` holds on
the localization at `S` of every big `τ`-site.

## Main definitions

* `AlgebraicGeometry.CoveringTopology.toSiteKind`: the `AlgebraicGeometry.SiteKind` naming a
  covering topology.
* `AlgebraicGeometry.bigFppfSiteOfCutoff`: the big fppf site with the cutoff of a big `τ`-site.

## Main results

* `AlgebraicGeometry.BigFppfSite.generate_mem_baseTopology_of_mem_precoverage`: a family of
  `Sch_κ` whose image in schemes is a `τ`-covering generates a covering sieve of the topology of
  `τ` on a chosen big fppf site.
* `AlgebraicGeometry.siteTopology_eq_baseTopology`: the topology of a big `τ`-site is the
  topology of `τ` on the big fppf site with the same cutoff.
* `AlgebraicGeometry.overTopology_eq_baseOverTopology`: the same after localizing at a scheme.

## References

* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 03WV](https://stacks.math.columbia.edu/tag/03WV)
-/

@[expose] public section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry

/-- The `AlgebraicGeometry.SiteKind` naming a covering topology. -/
public def CoveringTopology.toSiteKind : CoveringTopology → SiteKind
  | .fppf => .fppf
  | .syntomic => .syntomic
  | .smooth => .smooth
  | .etale => .etale
  | .zariski => .zariski

/-! ### Covering families on a chosen big fppf site -/

/-- **A `τ`-covering family generates a covering sieve of the topology of `τ` on a chosen big
fppf site.** A `τ`-covering family is an fppf covering family, so the chosen fppf system has a
combinatorially equivalent representative; it has the same presieve, so it is again a
`τ`-covering family, and it is therefore one of the chosen families presenting the topology of
`τ`. -/
public theorem BigFppfSite.generate_mem_baseTopology_of_mem_precoverage (P : BigFppfSite.{u})
    (τ : CoveringTopology) {X : P.Schemes} (E : PreZeroHypercover.{u + 1} X)
    (hE : (E.map P.inclusion).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty τ) (P.inclusion.obj X)) :
    Sieve.generate E.presieve₀ ∈ P.baseTopology τ.toSiteKind X := by
  have hEs := (Scheme.presieve₀_mem_precoverage_iff _).1 hE
  have hfppf : IsFppfCovering (κ := P.cutoff) ⟨X, E⟩ := by
    change Presieve.map P.inclusion E.presieve₀ ∈ Scheme.fppfPrecoverage.coverings _
    rw [← PreZeroHypercover.presieve₀_map]
    exact (Scheme.presieve₀_mem_precoverage_iff _).2 ⟨hEs.1, fun i =>
      coveringMorphismProperty_le_flat_inf_locallyOfFinitePresentation τ _ (hEs.2 i)⟩
  obtain ⟨E', hE', hcomb⟩ := P.fppf_has_representative ⟨X, E⟩ hfppf
  obtain ⟨W, F⟩ := E'
  obtain ⟨hobj, hce⟩ := hcomb
  cases hobj
  dsimp only at hce
  have hpre : F.presieve₀ = E.presieve₀ :=
    (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hce).symm
  have hF : (F.map P.inclusion).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty τ) (P.inclusion.obj X) := by
    rw [PreZeroHypercover.presieve₀_map, hpre, ← PreZeroHypercover.presieve₀_map]
    exact hE
  rw [← hpre]
  cases τ with
  | fppf => exact Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hE'⟩
  | zariski => exact Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hE', hF⟩
  | etale => exact Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hE', hF⟩
  | smooth => exact Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hE', hF⟩
  | syntomic =>
      refine Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hE', ?_⟩
      have h := (Scheme.presieve₀_mem_precoverage_iff (F.map P.inclusion)).1 hF
      exact ⟨h.2, Set.eq_univ_iff_forall.2 fun x => Set.mem_iUnion.2 (h.1 x)⟩

/-- A chosen covering family of the topology of `τ` on a chosen big fppf site is a `τ`-covering
family of schemes. -/
public theorem BigFppfSite.mem_precoverage_of_mem_baseTopology_precoverage (P : BigFppfSite.{u})
    (τ : CoveringTopology) {X : P.Schemes} (E : PreZeroHypercover.{u + 1} X)
    (hE : match τ with
      | .fppf => P.IsCovering ⟨X, E⟩
      | .zariski => P.zariskiCovering ⟨X, E⟩
      | .etale => P.etaleCovering ⟨X, E⟩
      | .smooth => P.smoothCovering ⟨X, E⟩
      | .syntomic => P.syntomicCovering ⟨X, E⟩) :
    (E.map P.inclusion).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty τ) (P.inclusion.obj X) := by
  cases τ with
  | fppf =>
      have h : E.presieve₀.map P.inclusion ∈ Scheme.fppfPrecoverage (P.inclusion.obj X) := hE.1
      rw [PreZeroHypercover.presieve₀_map]
      exact h
  | zariski => exact hE.2
  | etale => exact hE.2
  | smooth => exact hE.2
  | syntomic =>
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x => Set.mem_iUnion.1 (Set.eq_univ_iff_forall.1 hE.2.2 x), hE.2.1⟩

/-! ### The big fppf site with the cutoff of a big `τ`-site -/

/-- The cutoff of a big site has uncountable cofinality. -/
public theorem aleph0_lt_cutoff_ord_cof (τ : CoveringTopology) (B : BigSite.{u} τ) :
    ℵ₀ < (cutoff τ B).ord.cof := by
  cases τ with
  | zariski => exact B.aleph0_lt_schemeCardinal_cof
  | _ => exact B.aleph0_lt_cutoff_cof

/-- The big fppf site whose cutoff is the cutoff of a big `τ`-site, so whose category of schemes
is that of the big `τ`-site on the nose. -/
public noncomputable abbrev bigFppfSiteOfCutoff (τ : CoveringTopology) (B : BigSite.{u} τ) :
    BigFppfSite.{u} :=
  BigFppfSite.ofCutoff (cutoff τ B) (aleph0_lt_cutoff' τ B) (cutoff_isStrongPrelimit τ B)
    (aleph0_lt_cutoff_ord_cof τ B) ∅ (by simp)

/-- **The topology of a big `τ`-site is the topology of `τ` on the big fppf site with the same
cutoff.** In both, a sieve covers exactly when it contains the presieve of a `τ`-covering family
of `Sch_κ`: a chosen family of either system is a `τ`-covering family, and a `τ`-covering family
has the same presieve as a chosen family of either system. -/
public theorem siteTopology_eq_baseTopology (τ : CoveringTopology) (B : BigSite.{u} τ) :
    siteTopology τ B = (bigFppfSiteOfCutoff τ B).baseTopology τ.toSiteKind := by
  refine le_antisymm ?_ ?_
  · rw [siteTopology_eq_toGrothendieck, Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro X R hR
    obtain ⟨E, hE, rfl⟩ := (mem_bigSitePrecoverage_iff τ B).1 hR
    exact (bigFppfSiteOfCutoff τ B).generate_mem_baseTopology_of_mem_precoverage τ E
      (mem_precoverage_of_isCovering τ B E hE)
  · have key : ∀ {X : siteCategory B} (E : PreZeroHypercover.{u + 1} X),
        (E.map (schemeBelowInclusion (cutoff τ B))).presieve₀ ∈
          Scheme.precoverage (coveringMorphismProperty τ) X.obj →
        Sieve.generate E.presieve₀ ∈ siteTopology τ B X := by
      intro X E hE
      obtain ⟨F, hF, hEF⟩ := exists_isCovering_presieve₀_eq_aux τ B E hE
      rw [hEF]
      exact generate_mem_siteTopology τ B F hF
    cases τ <;>
    · refine Precoverage.toGrothendieck_le_iff_le_toPrecoverage.2 ?_
      rintro X R ⟨E, rfl, hE⟩
      exact key E (BigFppfSite.mem_precoverage_of_mem_baseTopology_precoverage _ _ E hE)

/-- **The localization at `S` of a big `τ`-site is the big fppf category over `S` of the big fppf
site with the same cutoff, with its topology of `τ`.** -/
public theorem overTopology_eq_baseOverTopology (τ : CoveringTopology) (B : BigSite.{u} τ)
    (S : Scheme.{u}) (hS : S.size < cutoff τ B) :
    overTopology τ B S hS =
      BigFppfOver.baseOverTopology (bigFppfSiteOfCutoff τ B) S hS τ.toSiteKind := by
  rw [overTopology_eq_siteTopology_over, siteTopology_eq_baseTopology]
  rfl

end AlgebraicGeometry

end
