module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.LiftedQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.LiftedSiteBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.SubsiteQuasiCoherentEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftBaseChangeAcyclic

/-!
# `QC(𝒳)` as the subcategory of Stacks 0GZS of the lifted étale affine site

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `X` be the lift
(`AlgebraicGeometry.Stack.affineLiftedSite`) of its associated affine site with the étale
topology to the single universe `M = max v w u t` of the modules of `QC(𝒳)`. This file identifies
`QC(𝒳)` with the full subcategory of `D(X)` of the objects `K` with `Rε_*K` cartesian, through
`QC(𝒳) ≌ QC(X_{affine}, 𝒪)` (`quasiCoherentDerivedLiftEquivalence`) and the equivalence of
Stacks 0GZS on the lift, whose hypothesis (2) is the base-change acyclicity of the slices of `X`
(`baseChangeIsSheaf_affineLiftedSite`, `baseChangeAcyclic_affineLiftedSite`).

## Main definitions

* `AlgebraicGeometry.Stack.affineLiftedCartesianEquivalence`: `QC(X_{affine}, 𝒪) ≌` the 0GZS
  subcategory of `D(X)`, with functor `ε^*`.
* `AlgebraicGeometry.Stack.quasiCoherentDerivedLiftedCartesianEquivalence`: `QC(𝒳) ≌` the 0GZS
  subcategory of `D(X)`.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.ChaoticComparison
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)
open Stacks.Cohomology.SubsiteQuasiCoherentEquivalence (IsCartesianPushforwardOn)

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **Hypothesis (2) of Stacks 0GZS on the lifted étale affine site of `𝒳`**: the base changes
`N ⊗ O_x` on its slices are sheaves with vanishing higher cohomology. -/
theorem isLocallyKFlatAcyclic_affineLiftedSite :
    IsLocallyKFlatAcyclic.{max v w u t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineLiftedSite.{u, v, w, t} B S hS p hp).O)
      (RingedSite.mul_comm_ringSheaf _) := by
  let (x : (affineLiftedSite.{u, v, w, t} B S hS p hp).C) :=
    Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max v w u t, max v w u t,
      max v w u t, max v w u t}
      (overRingSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineLiftedSite.{u, v, w, t} B S hS p hp).O) x)
  exact Stacks.UniverseLift.isLocallyKFlatAcyclic_of_baseChangeAcyclic _ _
    (baseChangeIsSheaf_affineLiftedSite.{u, v, w, t} B S hS p hp)
    (baseChangeAcyclic_affineLiftedSite.{u, v, w, t} B S hS p hp)

/-- **Stacks 0GZS on the lifted étale affine site of `𝒳`.** `ε^*` and `Rε_*` are mutually
quasi-inverse equivalences between the quasi-coherent objects of the derived category of the
chaotic lifted affine site and the objects `K` of `D(X)` with `Rε_*K` cartesian. -/
def affineLiftedCartesianEquivalence :
    QC.{max v w u t} (affineLiftedBaseChangeData.{u, v, w, t} B S hS p hp) ≌
      (IsCartesianPushforwardOn (affineLiftedSite.{u, v, w, t} B S hS p hp)).FullSubcategory :=
  pullbackPushforwardEquivalence.{max v w u t}
    (Stacks.SheafOfModules.Tensor.ringSheaf (affineLiftedSite.{u, v, w, t} B S hS p hp).O)
    (IsQC.{max v w u t} (affineLiftedBaseChangeData.{u, v, w, t} B S hS p hp))
    (fun M hM ↦ isIso_unit_of_isLocallyKFlatAcyclic.{max v w u t} _ _
      (isLocallyKFlatAcyclic_affineLiftedSite.{u, v, w, t} B S hS p hp) M hM)

/-- **`QC(𝒳)` is the 0GZS subcategory of the lifted étale affine site.** The composite of
`QC(𝒳) ≌ QC(X_{affine}, 𝒪)` and Stacks 0GZS on the lift. -/
def quasiCoherentDerivedLiftedCartesianEquivalence :
    quasiCoherentDerived.{u, v, w, t} B S hS p ≌
      (IsCartesianPushforwardOn (affineLiftedSite.{u, v, w, t} B S hS p hp)).FullSubcategory :=
  (quasiCoherentDerivedLiftEquivalence.{u, v, w, t} B S hS p hp).trans
    (affineLiftedCartesianEquivalence.{u, v, w, t} B S hS p hp)

end AlgebraicGeometry.Stack

end
