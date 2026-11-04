module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackValue

/-!
# Multiplication by a meromorphic function on the sheaf of meromorphic sections

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `M` be a
sheaf of `𝒪_F`-modules. Over an étale scheme chart `V`, the sheafification map from the
meromorphic sections `𝒦_F(V) ⊗_{𝒪_F(V)} M(V)` to the sections of the sheaf `𝒦_F(M)` of
Stacks 0EN5 is linear over the meromorphic functions:

`r • [t] = [r • t]`.

## Main definitions

* `AlgebraicGeometry.Space.meromorphicSectionModuleRingedSiteModule` is the module structure on
  the meromorphic sections over a chart at the spelling of the ring of meromorphic functions
  that `AlgebraicGeometry.Space.IsRegularMeromorphicSection` multiplies by.

## Main results

* `AlgebraicGeometry.Space.toMeromorphicSectionSheaf_smul`: the sheafification map of
  Stacks 0EN5 over a chart is linear over the meromorphic functions.

## Implementation notes

The module structure that `AlgebraicGeometry.Space.meromorphicSectionModule` carries over a chart
`V` is over `(ringPresheaf 𝒦_F).obj (op V)`, while the module structure on the sheafification is
over `(meromorphicRingedSite …).ringSheaf.obj.obj (op V)`, which reaches `RingCat` through
`Stacks.SheafOfModules.Tensor.ringSheaf`. The two are the same `RingCat` object only after
unfolding `AlgebraicGeometry.Space.meromorphicFunctionSheaf`, which instance search does not do;
`AlgebraicGeometry.Space.meromorphicSectionModuleRingedSiteModule` is the first module structure
read at the second spelling.

`CategoryTheory.PresheafOfModules.toSheafify` asks for the sheafification map of the underlying
presheaf of abelian groups to be locally injective and locally surjective. Instance search for
these reaches `AlgebraicGeometry.Space.moduleWEqualsLocallyBijective`, whose coefficient universe
`max (u + 1) z` does not unify with `u + 1`, so both are supplied as local instances, extracted
from `CategoryTheory.GrothendieckTopology.W_toSheafify`.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct
open Stacks.PresheafOfModules.ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The meromorphic sections over a chart as a module at the ringed-site spelling of the ring
of meromorphic functions.**  The module structure of the change-of-rings presheaf of Stacks 03CU,
over `(ringPresheaf 𝒦_F).obj (op V)`, read over the same ring of sections of `𝒦_F` over `V`
spelled `(meromorphicRingedSite …).ringSheaf.obj.obj (op V)`. -/
@[instance_reducible]
noncomputable def meromorphicSectionModuleRingedSiteModule
    (M : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F) :
    Module
      ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj.obj
        (op V))
      ((meromorphicSectionModule B S hS F hF M).obj (op V)) :=
  inferInstanceAs (Module
    ((ringPresheaf (meromorphicChartSheaf B S hS F hF).obj).obj (op V))
    ((meromorphicSectionModule B S hS F hF M).obj (op V)))

attribute [local instance] meromorphicSectionModuleRingedSiteModule

/-- **The sheafification map of Stacks 0EN5 over a chart is linear over the meromorphic
functions.**  For a meromorphic function `r` on an étale scheme chart `V` and a meromorphic
section `t` of `M` over `V`, the section of the sheaf `𝒦_F(M)` that `r • t` becomes is `r` times
the one `t` becomes. -/
theorem toMeromorphicSectionSheaf_smul
    (M : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj.obj
      (op V))
    (t : (meromorphicSectionModule B S hS F hF M).obj (op V)) :
    toMeromorphicSectionSheaf B S hS F hF M V (r • t) =
      r • toMeromorphicSectionSheaf B S hS F hF M V t := by
  let := moduleHasWeakSheafify.{u, u} B S hS F
  let := moduleWEqualsLocallyBijective.{u, u} B S hS F
  let : Presheaf.IsLocallyInjective (meromorphicRingedSite B S hS F hF).J
      (CategoryTheory.toSheafify (meromorphicRingedSite B S hS F hF).J
        (meromorphicSectionPresheaf.{u, u} B S hS F hF M).presheaf) :=
    ((meromorphicRingedSite B S hS F hF).J.W_toSheafify _).isLocallyInjective
  let : Presheaf.IsLocallySurjective (meromorphicRingedSite B S hS F hF).J
      (CategoryTheory.toSheafify (meromorphicRingedSite B S hS F hF).J
        (meromorphicSectionPresheaf.{u, u} B S hS F hF M).presheaf) :=
    ((meromorphicRingedSite B S hS F hF).J.W_toSheafify _).isLocallySurjective
  exact map_smul (((PresheafOfModules.toSheafify
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj)
    (CategoryTheory.toSheafify (meromorphicRingedSite B S hS F hF).J
      (meromorphicSectionPresheaf.{u, u} B S hS F hF M).presheaf)).app (op V)).hom) r
    (ULift.up t)

end AlgebraicGeometry.Space

end
