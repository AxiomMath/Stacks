module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.LiftedQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SchemeQC.ZariskiLiftedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.SubsiteQuasiCoherentEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftBaseChangeAcyclic

/-!
# `QC(𝒳)` as the subcategory of Stacks 0GZS of the lifted Zariski affine site

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `X` be the lift
(`AlgebraicGeometry.Stack.zariskiAffineLiftedSite`) of its associated affine site with the
Zariski topology to the single universe `M = max v w u t` of the modules of `QC(𝒳)`. This file
identifies `QC(𝒳)` with the full subcategory of `D(X)` of the objects `K` with `Rε_*K`
cartesian, through `QC(𝒳) ≌ QC(X_{affine}, 𝒪)` and the equivalence of Stacks 0GZS on the lift,
whose hypothesis (2) is the base-change acyclicity of the slices of `X`.

This is Stacks 0H0J for the Zariski topology, read on the lift; the étale case is
`AlgebraicGeometry.Stack.quasiCoherentDerivedLiftedCartesianEquivalence`.

## Main definitions

* `AlgebraicGeometry.Stack.quasiCoherentDerivedZariskiLiftEquivalence`:
  `QC(𝒳) ≌ QC(X_{affine}, 𝒪)` on the lifted Zariski affine site.
* `AlgebraicGeometry.Stack.zariskiAffineLiftedCartesianEquivalence`: `QC(X_{affine}, 𝒪) ≌` the
  0GZS subcategory of `D(X)`, with functor `ε^*`.
* `AlgebraicGeometry.Stack.quasiCoherentDerivedZariskiLiftedCartesianEquivalence`: `QC(𝒳) ≌` the
  0GZS subcategory of `D(X)`.

## References

* [Stacks Project, Tag 0H0J](https://stacks.math.columbia.edu/tag/0H0J)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
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

/-- The derived base-change datum of the structure sheaf of the lifted Zariski affine site, at
the universe `max v w u t` of the lift. -/
abbrev zariskiAffineLiftedBaseChangeData :
    BaseChangeData.{max v w u t} (Stacks.SheafOfModules.Tensor.ringSheaf
      (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).O).obj :=
  baseChangeDataOfComm.{max v w u t, max v w u t, max v w u t, max v w u t}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).O).obj
    (RingedSite.mul_comm_ringSheaf (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp))

/-- **`QC(𝒳)` is the category of quasi-coherent objects on the lifted Zariski affine site.**
The triangulated category `QC(𝒳) = QC(𝒳_{affine}, 𝒪)` of Stacks 0H0H, with modules in the
universe `max v w u t`, is equivalent to the full subcategory of quasi-coherent objects of the
derived category of presheaves of modules on the lift of `(𝒳_{affine, Zar}, 𝒪)` to that universe;
the functor is the derived transport of presheaves of modules along the lift. -/
def quasiCoherentDerivedZariskiLiftEquivalence :
    quasiCoherentDerived.{u, v, w, t} B S hS p ≌
      QC.{max v w u t} (zariskiAffineLiftedBaseChangeData.{u, v, w, t} B S hS p hp) :=
  (affineBaseChangeData.{u, v, w, t} B S hS p).qcToMaxEquivalence.trans
    ((RingedSite.liftRingTransport.{t}
      (AffineCategory.siteKindRingedSite B S hS p hp .zariski)).qcEquivalence.{t}
      (affineBaseChangeData.{u, v, w, t} B S hS p).toMax
      (zariskiAffineLiftedBaseChangeData.{u, v, w, t} B S hS p hp))

/-- **Hypothesis (2) of Stacks 0GZS on the lifted Zariski affine site of `𝒳`**: the base changes
`N ⊗ O_x` on its slices are sheaves with vanishing higher cohomology. -/
theorem isLocallyKFlatAcyclic_zariskiAffineLiftedSite :
    IsLocallyKFlatAcyclic.{max v w u t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).O)
      (RingedSite.mul_comm_ringSheaf _) := by
  let (x : (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).C) :=
    Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max v w u t, max v w u t,
      max v w u t, max v w u t}
      (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
        (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).O) x)
  exact Stacks.UniverseLift.isLocallyKFlatAcyclic_of_baseChangeAcyclic _ _
    (baseChangeIsSheaf_zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp)
    (baseChangeAcyclic_zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp)

/-- **Stacks 0GZS on the lifted Zariski affine site of `𝒳`.** `ε^*` and `Rε_*` are mutually
quasi-inverse equivalences between the quasi-coherent objects of the derived category of the
chaotic lifted affine site and the objects `K` of `D(X)` with `Rε_*K` cartesian. -/
def zariskiAffineLiftedCartesianEquivalence :
    QC.{max v w u t} (zariskiAffineLiftedBaseChangeData.{u, v, w, t} B S hS p hp) ≌
      (IsCartesianPushforwardOn
        (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp)).FullSubcategory :=
  pullbackPushforwardEquivalence.{max v w u t}
    (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).O)
    (IsQC.{max v w u t} (zariskiAffineLiftedBaseChangeData.{u, v, w, t} B S hS p hp))
    (fun M hM ↦ isIso_unit_of_isLocallyKFlatAcyclic.{max v w u t} _ _
      (isLocallyKFlatAcyclic_zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp) M hM)

/-- **`QC(𝒳)` is the 0GZS subcategory of the lifted Zariski affine site** (Stacks 0H0J for the
Zariski topology). The composite of `QC(𝒳) ≌ QC(X_{affine}, 𝒪)` and Stacks 0GZS on the lift. -/
def quasiCoherentDerivedZariskiLiftedCartesianEquivalence :
    quasiCoherentDerived.{u, v, w, t} B S hS p ≌
      (IsCartesianPushforwardOn
        (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp)).FullSubcategory :=
  (quasiCoherentDerivedZariskiLiftEquivalence.{u, v, w, t} B S hS p hp).trans
    (zariskiAffineLiftedCartesianEquivalence.{u, v, w, t} B S hS p hp)

end AlgebraicGeometry.Stack
