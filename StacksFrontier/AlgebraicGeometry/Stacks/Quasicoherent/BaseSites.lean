module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ChosenCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Zariski.BigSite
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedSite
public import StacksCore.Tactic.StacksAttribute

/-!
# The five big sites on one category of schemes, and the sites they induce upstairs

The Zariski, étale, smooth, syntomic and fppf topologies of a chosen big fppf site all live on
the same category of schemes. For a category over the big fppf category of schemes over a base
scheme `S`, each of them induces a topology upstairs by
`CategoryTheory.Functor.inheritedTopology`, so that `𝒳_{Zar}`, `𝒳_{étale}`, `𝒳_{smooth}`,
`𝒳_{syntomic}` and `𝒳_{fppf}` are sites on one and the same category.

## Main definitions

* `AlgebraicGeometry.SiteKind` enumerates the five topologies.
* `AlgebraicGeometry.BigFppfSite.baseTopology` selects one of the five topologies on the
  common category of schemes by a `SiteKind`.
* `AlgebraicGeometry.BigFppfOver.associatedTopology` is the topology inherited upstairs along
  a functor to the big fppf category over `S`.

## Main results

* `AlgebraicGeometry.BigFppfSite.baseTopology_le_topology`: each of the five topologies on the
  common category is coarser than the fppf one.
* `AlgebraicGeometry.BigFppfOver.associatedTopology_le_fppf`: each inherited topology upstairs is
  coarser than the inherited fppf topology.

## References

* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

/-- The five topologies for which a big site of schemes is prescribed. -/
public inductive SiteKind where
  /-- The Zariski topology. -/
  | zariski
  /-- The étale topology. -/
  | etale
  /-- The smooth topology. -/
  | smooth
  /-- The syntomic topology. -/
  | syntomic
  /-- The fppf topology. -/
  | fppf

namespace BigFppfSite

variable (B : BigFppfSite.{u})

/-- The fppf precoverage of a big fppf site is the one presented by its own selected
collection of covering families. -/
public theorem precoverage_eq_chosenPrecoverage :
    B.precoverage = B.chosenPrecoverage B.IsCovering := rfl

/-- A collection of covering families contained in the fppf one presents a coarser
precoverage. -/
public theorem chosenPrecoverage_le_precoverage {P : Covering B.Schemes → Prop}
    (hP : ∀ E, P E → B.IsCovering E) : B.chosenPrecoverage P ≤ B.precoverage := by
  rintro X _ ⟨E, rfl, hE⟩
  exact ⟨E, rfl, hP _ hE⟩

/-- The topology of the indicated big site, all five on the common category of schemes of a
chosen big fppf site. -/
public def baseTopology : SiteKind → GrothendieckTopology B.Schemes
  | .zariski => B.zariskiTopology
  | .etale => B.etaleTopology
  | .smooth => B.smoothTopology
  | .syntomic => B.syntomicTopology
  | .fppf => B.topology

/-- Each of the five topologies on the common category of schemes is coarser than the fppf
topology. -/
public theorem baseTopology_le_topology (τ : SiteKind) : B.baseTopology τ ≤ B.topology := by
  cases τ
  case fppf => exact le_rfl
  all_goals
    exact Precoverage.toGrothendieck_mono (B.chosenPrecoverage_le_precoverage fun _ hE => hE.1)

end BigFppfSite

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The localization at `S` of the topology of the indicated big site. -/
public abbrev baseOverTopology (τ : SiteKind) :
    GrothendieckTopology (BigFppfOver B S hS) :=
  (B.baseTopology τ).over (B.obj hS)

/-- Each of the five localized topologies on the big fppf category over `S` is coarser than
the localized fppf topology. -/
public theorem baseOverTopology_le_fppf (τ : SiteKind) :
    baseOverTopology B S hS τ ≤ topology B S hS := by
  intro X R hR
  rw [GrothendieckTopology.mem_over_iff] at hR ⊢
  exact B.baseTopology_le_topology τ _ hR

/-- The site associated with a category over the big fppf category of schemes over `S`, for any
of the five indicated topologies: the topology inherited along the structure functor. -/
public abbrev associatedTopology {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (τ : SiteKind) : GrothendieckTopology 𝒳 :=
  p.inheritedTopology (baseOverTopology B S hS τ)

/-- Each of the five inherited topologies is coarser than the inherited fppf topology. -/
public theorem associatedTopology_le_fppf {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (τ : SiteKind) :
    associatedTopology B S hS p τ ≤ associatedTopology B S hS p .fppf := by
  apply Precoverage.toGrothendieck_mono
  intro X R hR
  exact ⟨hR.1, baseOverTopology_le_fppf B S hS τ _ hR.2⟩

end BigFppfOver

end AlgebraicGeometry

end
