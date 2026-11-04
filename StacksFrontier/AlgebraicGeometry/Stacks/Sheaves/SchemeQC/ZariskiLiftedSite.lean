module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.LiftedSiteBaseChange

/-!
# The lifted Zariski affine site of a category over `(Sch/S)_{fppf}`

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be fibred in groupoids. This file lifts the ringed site
`(𝒳_{affine, Zar}, 𝒪)` of Stacks 0H0D for the Zariski topology to the single universe
`max v w u t` of the modules of `QC(𝒳)` (`AlgebraicGeometry.Stack.zariskiAffineLiftedSite`), and
records on it the inputs on single modules of Stacks 0H0J for the Zariski topology: for an
object `x` and an `𝒪(x)`-module `N`, the base change `N ⊗_{𝒪(x)} 𝒪_x` on the slice at `x` is a
sheaf with vanishing higher cohomology; these are the inputs of the invertibility of the `ε`-unit
on every slice at a derived base change (in `Stacks.ModulesOnACategory.ChaoticComparison`,
`isIso_derivedEpsilonAdjunction_unit_app_Lpullback_of_baseChange`).

It is the Zariski counterpart of `RepresentableQC/LiftedSiteBaseChange.lean`, which treats the
étale topology; the inputs on the unlifted site are stated there for each of the five topologies
of Stacks 0H0A (`AlgebraicGeometry.Stack.AffineCategory.isSheaf_baseChange_affineSlice`,
`AlgebraicGeometry.Stack.AffineCategory.isZero_rightDerived_evaluation_baseChange_affineSlice`).

## Main definitions

* `AlgebraicGeometry.Stack.zariskiAffineLiftedSite`: the lift of `(𝒳_{affine, Zar}, 𝒪)`.

## Main results

* `AlgebraicGeometry.Stack.baseChangeIsSheaf_zariskiAffineLiftedSite` and
  `AlgebraicGeometry.Stack.baseChangeAcyclic_zariskiAffineLiftedSite`: the two halves of the
  base-change hypothesis on the lifted Zariski affine site.

## References

* [Stacks Project, Tag 0H0J](https://stacks.math.columbia.edu/tag/0H0J)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.TerminalBaseChange Stacks.Sites.OverModules Stacks.UniverseLift
open Stacks.ModulesOnACategory.ChaoticComparison
open Stacks.ModulesOnACategory.MorphismsOverAnObject (comm_overRingPresheaf)
open Stacks.ModulesOnACategory.TerminalMorphismOfSites (morphismOfSites)

-- The ambient-universe instances on sheaves of modules state their universe as a `max` pattern
-- that the module universes below do not match syntactically, which leaves the universe
-- constraints of their unification stuck; they are switched off and the instances are supplied
-- explicitly at the universes used here.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The lift of the Zariski affine ringed site of `𝒳` to a single universe**: the ringed site
`(𝒳_{affine, Zar}, 𝒪)` of Stacks 0H0D lifted, by `AlgebraicGeometry.RingedSite.lift`, to the
universe `max v w u t`, in which its underlying category, morphisms, section rings and modules
all live. -/
noncomputable abbrev zariskiAffineLiftedSite :
    RingedSite.{max v w u t, max v w u t, max v w u t} :=
  RingedSite.lift.{t} (AffineCategory.siteKindRingedSite B S hS p hp .zariski)

/-- The sheaf half of the base-change hypothesis on `𝒳_{affine, Zar}`, at the module universe
`max v w u t`. -/
theorem baseChangeIsSheaf_zariskiSiteKindRingedSite :
    BaseChangeIsSheaf.{max v w t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp .zariski).O)
      (RingedSite.mul_comm_ringSheaf _) :=
  fun x N => AffineCategory.isSheaf_baseChange_affineSlice.{u, v, w, t} B S hS hp .zariski x N

/-- The sheaf half of the base-change hypothesis on the lifted Zariski affine site. -/
theorem baseChangeIsSheaf_zariskiAffineLiftedSite :
    BaseChangeIsSheaf.{max v w u t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).O)
      (RingedSite.mul_comm_ringSheaf _) := by
  have h : BaseChangeIsSheaf.{max v w u t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp .zariski).O)
      (RingedSite.mul_comm_ringSheaf _) :=
    (baseChangeIsSheaf_max_iff.{max v w t} _ _).2
      (baseChangeIsSheaf_zariskiSiteKindRingedSite.{u, v, w, t} B S hS p hp)
  exact (RingedSite.liftRingTransport.{t}
    (AffineCategory.siteKindRingedSite B S hS p hp .zariski)).baseChangeIsSheaf
    (RingedSite.mul_comm_ringSheaf _)
    (RingedSite.mul_comm_ringSheaf (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp)) h

/-- The acyclicity half of the base-change hypothesis on `𝒳_{affine, Zar}`, at the module
universe `max v w u t`. -/
theorem baseChangeAcyclic_zariskiSiteKindRingedSite :
    letI (x : AffineCategory B S hS p) :=
      Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, max u t}
        (J := (AffineCategory.siteKindRingedSite B S hS p hp .zariski).J.over x)
    letI (x : AffineCategory B S hS p) :=
      Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{max v w, w, max u t}
        (J := (AffineCategory.siteKindRingedSite B S hS p hp .zariski).J.over x)
    letI (x : AffineCategory B S hS p) :=
      Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max v w, w, u, t}
        (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (AffineCategory.siteKindRingedSite B S hS p hp .zariski).O) x)
    BaseChangeAcyclic.{max v w t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp .zariski).O)
      (RingedSite.mul_comm_ringSheaf _)
      (baseChangeIsSheaf_zariskiSiteKindRingedSite.{u, v, w, t} B S hS p hp) :=
  fun x N V n hn =>
    AffineCategory.isZero_rightDerived_evaluation_baseChange_affineSlice.{u, v, w, t}
      B S hS hp .zariski x N V n hn

/-- The acyclicity half of the base-change hypothesis on the lifted Zariski affine site. -/
theorem baseChangeAcyclic_zariskiAffineLiftedSite :
    letI (x : (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).C) :=
      Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max v w u t, max v w u t,
        max v w u t, max v w u t}
        (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).O) x)
    BaseChangeAcyclic.{max v w u t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).O)
      (RingedSite.mul_comm_ringSheaf _)
      (baseChangeIsSheaf_zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp) := by
  let (x : AffineCategory B S hS p) :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, max u t}
      (J := (AffineCategory.siteKindRingedSite B S hS p hp .zariski).J.over x)
  let (x : AffineCategory B S hS p) :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{max v w, w, max u t}
      (J := (AffineCategory.siteKindRingedSite B S hS p hp .zariski).J.over x)
  let (x : AffineCategory B S hS p) :=
    Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max v w, w, u, t}
      (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp .zariski).O) x)
  let (x : (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).C) :=
    Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max v w u t, max v w u t,
      max v w u t, max v w u t}
      (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
        (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).O) x)
  have h : BaseChangeAcyclic.{max v w u t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp .zariski).O)
      (RingedSite.mul_comm_ringSheaf _)
      ((baseChangeIsSheaf_max_iff.{max v w t} _ _).2
        (baseChangeIsSheaf_zariskiSiteKindRingedSite.{u, v, w, t} B S hS p hp)) :=
    (baseChangeAcyclic_max_iff.{max v w t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp .zariski).O)
      (RingedSite.mul_comm_ringSheaf _) _).2
      (baseChangeAcyclic_zariskiSiteKindRingedSite.{u, v, w, t} B S hS p hp)
  exact (RingedSite.liftRingTransport.{t}
    (AffineCategory.siteKindRingedSite B S hS p hp .zariski)).baseChangeAcyclic
    (RingedSite.mul_comm_ringSheaf _)
    (RingedSite.mul_comm_ringSheaf (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp)) _ h


end AlgebraicGeometry.Stack
