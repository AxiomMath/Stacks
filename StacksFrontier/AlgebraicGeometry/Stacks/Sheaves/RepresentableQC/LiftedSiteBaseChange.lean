module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealAnnihilatorSubsheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSliceBaseChangeAcyclic
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.LiftedSites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.SubsiteQuasiCoherentEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftBaseChangeAcyclic

/-!
# The derived base changes on the slices of the lifted affine site

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be fibred in groupoids and `X↑` the lift of its étale affine ringed
site `(𝒳_{affine, étale}, 𝒪)` to the single universe `max v w u t`
(`AlgebraicGeometry.Stack.affineLiftedSite`). For an object `x` and an `𝒪(x)`-module `N`, the
base change `N ⊗_{𝒪(x)} 𝒪_x` on the slice `X↑/x` is a sheaf with vanishing higher cohomology over
every object: these are the inputs on single modules of Stacks 0H0J, known on
`𝒳_{affine, étale}` (`AlgebraicGeometry.Stack.AffineCategory.isSheaf_baseChange_affineSlice`,
`AlgebraicGeometry.Stack.AffineCategory.isZero_rightDerived_evaluation_baseChange_affineSlice`)
and transported to the lift along its ring transport (`Stacks.UniverseLift.RingTransport`).
They give the invertibility of the `ε`-unit on every slice of `X↑` at a derived base change.

## Main results

* `AlgebraicGeometry.Stack.baseChangeIsSheaf_affineLiftedSite` and
  `AlgebraicGeometry.Stack.baseChangeAcyclic_affineLiftedSite`: the two halves of the
  base-change hypothesis on the lifted affine site.
* `AlgebraicGeometry.Stack.affineLiftedSite_isIso_derivedEpsilonAdjunction_unit`: the `ε`-unit
  on every slice of the lifted affine site at a derived base change is an isomorphism.

## References

* [Stacks Project, Tag 0H0J](https://stacks.math.columbia.edu/tag/0H0J)
* [Stacks Project, Tag 0H0K](https://stacks.math.columbia.edu/tag/0H0K)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.TerminalBaseChange Stacks.Sites.OverModules Stacks.UniverseLift
open Stacks.ModulesOnACategory.ChaoticComparison
open Stacks.ModulesOnACategory.MorphismsOverAnObject (comm_overRingPresheaf)
open Stacks.ModulesOnACategory.TerminalMorphismOfSites (morphismOfSites)
open Stacks.Cohomology.SubsiteQuasiCoherentEquivalence (slicePullback)

-- The ambient-universe instances on sheaves of modules state their universe as a `max` pattern
-- that the module universes below do not match syntactically; they are supplied explicitly.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_isGrothendieckAbelian
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

attribute [local instance] Stacks.SheafOfModulesEvaluation.evaluation_additive
  HasDerivedCategory.standard

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The sheaf half of the base-change hypothesis on `𝒳_{affine, étale}`, at the module universe
`max v w u t`. -/
theorem baseChangeIsSheaf_siteKindRingedSite :
    BaseChangeIsSheaf.{max v w t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp .etale).O)
      (RingedSite.mul_comm_ringSheaf _) :=
  fun x N => AffineCategory.isSheaf_baseChange_affineSlice.{u, v, w, t} B S hS hp .etale x N

/-- The sheaf half of the base-change hypothesis on the lifted affine site. -/
theorem baseChangeIsSheaf_affineLiftedSite :
    BaseChangeIsSheaf.{max v w u t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineLiftedSite.{u, v, w, t} B S hS p hp).O)
      (RingedSite.mul_comm_ringSheaf _) := by
  have h : BaseChangeIsSheaf.{max v w u t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp .etale).O)
      (RingedSite.mul_comm_ringSheaf _) :=
    (baseChangeIsSheaf_max_iff.{max v w t} _ _).2
      (baseChangeIsSheaf_siteKindRingedSite.{u, v, w, t} B S hS p hp)
  exact (RingedSite.liftRingTransport.{t}
    (AffineCategory.siteKindRingedSite B S hS p hp .etale)).baseChangeIsSheaf
    (RingedSite.mul_comm_ringSheaf _)
    (RingedSite.mul_comm_ringSheaf (affineLiftedSite.{u, v, w, t} B S hS p hp)) h

/-- The acyclicity half of the base-change hypothesis on `𝒳_{affine, étale}`, at the module
universe `max v w u t`. -/
theorem baseChangeAcyclic_siteKindRingedSite :
    letI (x : AffineCategory B S hS p) :=
      Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, max u t}
        (J := (AffineCategory.siteKindRingedSite B S hS p hp .etale).J.over x)
    letI (x : AffineCategory B S hS p) :=
      Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{max v w, w, max u t}
        (J := (AffineCategory.siteKindRingedSite B S hS p hp .etale).J.over x)
    letI (x : AffineCategory B S hS p) :=
      Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max v w, w, u, t}
        (overRingSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (AffineCategory.siteKindRingedSite B S hS p hp .etale).O) x)
    BaseChangeAcyclic.{max v w t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp .etale).O)
      (RingedSite.mul_comm_ringSheaf _)
      (baseChangeIsSheaf_siteKindRingedSite.{u, v, w, t} B S hS p hp) :=
  fun x N V n hn =>
    AffineCategory.isZero_rightDerived_evaluation_baseChange_affineSlice.{u, v, w, t}
      B S hS hp .etale x N V n hn

/-- The acyclicity half of the base-change hypothesis on the lifted affine site. -/
theorem baseChangeAcyclic_affineLiftedSite :
    letI (x : (affineLiftedSite.{u, v, w, t} B S hS p hp).C) :=
      Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max v w u t, max v w u t,
        max v w u t, max v w u t}
        (overRingSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (affineLiftedSite.{u, v, w, t} B S hS p hp).O) x)
    BaseChangeAcyclic.{max v w u t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineLiftedSite.{u, v, w, t} B S hS p hp).O)
      (RingedSite.mul_comm_ringSheaf _)
      (baseChangeIsSheaf_affineLiftedSite.{u, v, w, t} B S hS p hp) := by
  let (x : AffineCategory B S hS p) :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, max u t}
      (J := (AffineCategory.siteKindRingedSite B S hS p hp .etale).J.over x)
  let (x : AffineCategory B S hS p) :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{max v w, w, max u t}
      (J := (AffineCategory.siteKindRingedSite B S hS p hp .etale).J.over x)
  let (x : AffineCategory B S hS p) :=
    Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max v w, w, u, t}
      (overRingSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (AffineCategory.siteKindRingedSite B S hS p hp .etale).O) x)
  have h : BaseChangeAcyclic.{max v w u t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp .etale).O)
      (RingedSite.mul_comm_ringSheaf _)
      ((baseChangeIsSheaf_max_iff.{max v w t} _ _).2
        (baseChangeIsSheaf_siteKindRingedSite.{u, v, w, t} B S hS p hp)) :=
    (baseChangeAcyclic_max_iff.{max v w t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp .etale).O)
      (RingedSite.mul_comm_ringSheaf _) _).2
      (baseChangeAcyclic_siteKindRingedSite.{u, v, w, t} B S hS p hp)
  exact (RingedSite.liftRingTransport.{t}
    (AffineCategory.siteKindRingedSite B S hS p hp .etale)).baseChangeAcyclic
    (RingedSite.mul_comm_ringSheaf _)
    (RingedSite.mul_comm_ringSheaf (affineLiftedSite.{u, v, w, t} B S hS p hp)) _ h

section Unit

-- The instance priorities of `SubsiteQuasiCoherentEquivalence.lean`, in
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/`.
attribute [local instance 1500] HasDerivedCategory.standard
attribute [local instance 2000]
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
attribute [local instance 2000]
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

/-- **The `ε`-unit on a slice of the lifted affine site at a derived base change is
invertible.** For every object `x` of the lifted `𝒳_{affine, étale}` and every object `P` of
`D(O(x))`, the unit `P ⊗^L_{O(x)} O_x ⟶ Rε_{x*}(ε_x^*(P ⊗^L_{O(x)} O_x))` of the derived
adjunction on the localized site is an isomorphism. -/
theorem affineLiftedSite_isIso_derivedEpsilonAdjunction_unit
    (x : (affineLiftedSite.{u, v, w, t} B S hS p hp).C)
    (P : DerivedCategory (ModuleCat.{max v w u t}
      ((overRingPresheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (affineLiftedSite.{u, v, w, t} B S hS p hp).O).obj x).obj
        (op (Over.mk (𝟙 x)))))) :
    IsIso ((derivedEpsilonAdjunction.{max v w u t}
      (overRingSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (affineLiftedSite.{u, v, w, t} B S hS p hp).O) x)).unit.app
      ((slicePullback (affineLiftedSite.{u, v, w, t} B S hS p hp) x
        (Over.mkIdTerminal (X := x))).obj P)) := by
  let (y : (affineLiftedSite.{u, v, w, t} B S hS p hp).C) :=
    Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max v w u t, max v w u t,
      max v w u t, max v w u t}
      (overRingSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineLiftedSite.{u, v, w, t} B S hS p hp).O) y)
  exact isIso_derivedEpsilonAdjunction_unit_app_Lpullback_of_baseChange
    (Stacks.SheafOfModules.Tensor.ringSheaf (affineLiftedSite.{u, v, w, t} B S hS p hp).O)
    (RingedSite.mul_comm_ringSheaf _) x
    (baseChangeIsSheaf_affineLiftedSite.{u, v, w, t} B S hS p hp x)
    (baseChangeAcyclic_affineLiftedSite.{u, v, w, t} B S hS p hp x) P

end Unit

end AlgebraicGeometry.Stack
