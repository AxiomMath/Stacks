module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ZariskiBaseChange
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local

/-!
# The Zariski restriction of an adequate module is quasi-coherent

Let `S` be a scheme and let `𝓕` be an adequate `𝒪`-module on a chosen big `τ`-site `(Sch/S)_τ`
over `S`, for `τ` any of the five topologies. The restriction `𝓕|_{S_Zar}` of `𝓕` to the small
Zariski site of `S` is a quasi-coherent `𝒪_S`-module. This is **[Stacks, Tag 06VM] (1)**, and it
is what the functor `v : Adeq(𝒪) ⥤ QCoh(𝒪_S)` of [Stacks, Tag 06VN],
`Stacks.Adequate.BigSite.restrictModuleQCoh`, needs in order to be defined.

## Main results

* `Stacks.Adequate.BigSite.isQuasicoherent_zariskiRestrictModule` — **[Stacks, Tag 06VM] (1)**.

## Implementation notes

The source's proof reads the base-change formula `𝓕(U) = 𝓕(V) ⊗_{𝒪(V)} 𝒪(U)` on affine opens
`U ⊆ V ⊆ S`, which is `Stacks.Adequate.BigSite.affineOpenBaseChange`. The passage from it to
quasi-coherence is not formal: quasi-coherence is defined by the existence of local
presentations. It goes through
`Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ`,
which needs the sections over each basic open of an affine open to be a localization, and
Mathlib's `isLocalizedModule_iff_isBaseChange` turns the base-change formula into that
localization statement because `Γ(S, S.basicOpen a)` is the localization of `Γ(S, U)` away from
`a`.

## References

* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 06UW](https://stacks.math.columbia.edu/tag/06UW)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 06VN](https://stacks.math.columbia.edu/tag/06VN)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.TorsionQuasicoherent

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-- **[Stacks, Tag 06VM] (1).** Let `𝓕` be an adequate `𝒪`-module on a chosen big `τ`-site
`(Sch/S)_τ` over a scheme `S`. The restriction `𝓕|_{S_Zar}` of `𝓕` to the small Zariski site of
`S` is a quasi-coherent `𝒪_S`-module on the scheme `S`.

The sections of `𝓕|_{S_Zar}` over the basic open `D(a)` of an affine open `U` are the base change
of the sections over `U` along `𝒪(U) → 𝒪(D(a))`, by
`Stacks.Adequate.BigSite.affineOpenBaseChange`, hence their localization away from `a`. -/
@[stacks 06VM "(1): for an adequate 𝒪-module F on (Sch/S)_τ the restriction F|_{S_Zar} is a
quasi-coherent 𝒪_S-module on the scheme S"]
public theorem BigSite.isQuasicoherent_zariskiRestrictModule (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) :
    (B.zariskiRestrictModule.obj F).IsQuasicoherent := by
  refine isQuasicoherent_of_isLocalizedModule_restrictₗ _ fun U hU a ↦ ?_
  let := algebraOfLE S (S.basicOpen_le a)
  let := moduleOfLE (B.zariskiRestrictModule.obj F) (S.basicOpen_le a)
  let := isScalarTowerOfLE (B.zariskiRestrictModule.obj F) (S.basicOpen_le a)
  have : IsLocalization.Away a Γ(S, S.basicOpen a) := hU.isLocalization_basicOpen a
  exact (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) Γ(S, S.basicOpen a) _).mpr
    (B.affineOpenBaseChange F hF (S.basicOpen a) U (hU.basicOpen a) hU (S.basicOpen_le a))

end Stacks.Adequate

end
