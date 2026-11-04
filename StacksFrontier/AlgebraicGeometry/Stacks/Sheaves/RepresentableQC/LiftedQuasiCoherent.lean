module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealAnnihilatorSubsheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.LiftedSites
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftQC

/-!
# `QC(𝒳)` on the lifted affine site

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be fibred in groupoids. The triangulated category `QC(𝒳)` of
Stacks 0H0H is the category of quasi-coherent objects of `D(𝒳_{affine}, 𝒪)` for the chaotic
topology, with modules in the universe `max v w u t`. This file identifies it with the category
of quasi-coherent objects of the derived category of presheaves of modules on the lift of
`(𝒳_{affine, étale}, 𝒪)` to the single universe `max v w u t`
(`AlgebraicGeometry.Stack.affineLiftedSite`), the setting of the middle step of the proof of
Stacks 0H0K.

## Main definitions

* `AlgebraicGeometry.Stack.quasiCoherentDerivedLiftEquivalence`: the equivalence
  `QC(𝒳) ≌ QC(𝒳_{affine}↑, 𝒪↑)`.

## Implementation notes

The equivalence is the transport of quasi-coherent objects along the ring transport of the lift
(`Stacks.UniverseLift.RingTransport.qcEquivalence`), preceded by the identification of `QC(𝒳)`,
stated with a base-change datum at the free universe `t`, with the same category for that datum
read at the module universe `max v w u t` (`BaseChangeData.qcToMaxEquivalence`). On the lift the
base-change datum is `baseChangeDataOfComm`; quasi-coherence does not depend on the choice of
the datum (`isQC_iff_of_baseChangeData`).

## References

* [Stacks Project, Tag 0H0H](https://stacks.math.columbia.edu/tag/0H0H)
* [Stacks Project, Tag 0H0K](https://stacks.math.columbia.edu/tag/0H0K)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The derived base-change datum of the structure sheaf of the lifted affine site, at the
universe `max v w u t` of the lift. -/
abbrev affineLiftedBaseChangeData :
    BaseChangeData.{max v w u t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineLiftedSite.{u, v, w, t} B S hS p hp).O).obj :=
  baseChangeDataOfComm.{max v w u t, max v w u t, max v w u t, max v w u t}
    (Stacks.SheafOfModules.Tensor.ringSheaf (affineLiftedSite.{u, v, w, t} B S hS p hp).O).obj
    (RingedSite.mul_comm_ringSheaf (affineLiftedSite.{u, v, w, t} B S hS p hp))

/-- **`QC(𝒳)` is the category of quasi-coherent objects on the lifted affine site.** The
triangulated category `QC(𝒳) = QC(𝒳_{affine}, 𝒪)` of Stacks 0H0H, with modules in the universe
`max v w u t`, is equivalent to the full subcategory of quasi-coherent objects of the derived
category of presheaves of modules on the lift of `(𝒳_{affine, étale}, 𝒪)` to that universe; the
functor is the derived transport of presheaves of modules along the lift. -/
def quasiCoherentDerivedLiftEquivalence :
    quasiCoherentDerived.{u, v, w, t} B S hS p ≌
      QC.{max v w u t} (affineLiftedBaseChangeData.{u, v, w, t} B S hS p hp) :=
  (affineBaseChangeData.{u, v, w, t} B S hS p).qcToMaxEquivalence.trans
    ((RingedSite.liftRingTransport.{t}
      (AffineCategory.siteKindRingedSite B S hS p hp .etale)).qcEquivalence.{t}
      (affineBaseChangeData.{u, v, w, t} B S hS p).toMax
      (affineLiftedBaseChangeData.{u, v, w, t} B S hS p hp))

end AlgebraicGeometry.Stack
