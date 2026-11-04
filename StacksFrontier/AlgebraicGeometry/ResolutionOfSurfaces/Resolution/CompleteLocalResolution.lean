module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteLocalFinal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.InvertibleDualizingBlowupSequence
import StacksCore.Tactic.StacksAttribute

/-!
# Resolution of two-dimensional normal local rings

This file registers [Stacks, Tag 0BGM] and [Stacks, Tag 0BGN]. Both are the assemblies of
`…/Resolution/CompleteLocalFinal.lean` over [Stacks, Tag 0BBV] in its Gorenstein form,
`AlgebraicGeometry.exists_singularPointBlowupChain_isGorenstein`, and [Stacks, Tag 0BGE],
`AlgebraicGeometry.exists_singularPointBlowupChain_isNormal_isRegular`.

## Main results

* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_exists_isResolution` —
  [Stacks, Tag 0BGM].
* `AlgebraicGeometry.exists_isResolution_of_isAdicComplete` — [Stacks, Tag 0BGN].

## References

* [Stacks Project, Tag 0BGM](https://stacks.math.columbia.edu/tag/0BGM)
* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0BGM.** Let `(A, 𝔪, κ)` be a Noetherian local ring which is normal of
dimension two. If `Spec(A)` has a resolution of singularities, then `Spec(A)` has a resolution by
normalized blowups. -/
@[stacks 0BGM]
theorem hasResolutionByNormalizedBlowUps_of_exists_isResolution
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hdim : ringKrullDim A = 2)
    (hres : ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) :=
  hasResolutionByNormalizedBlowUps_of_exists_isResolution_of_gorensteinChain
    (fun B _ _ _ _ hN hd hr hc => exists_singularPointBlowupChain_isGorenstein B hN hd hr hc)
    A hdim hres

/-- **Stacks Project, Tag 0BGN.** Let `(A, 𝔪, κ)` be a Noetherian complete local ring which is a
normal domain of dimension two. Then `Spec(A)` has a resolution of singularities. -/
@[stacks 0BGN]
theorem exists_isResolution_of_isAdicComplete
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsNormalDomain A] (hdim : ringKrullDim A = 2) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f :=
  exists_isResolution_of_isAdicComplete_of_gorensteinChain
    (fun B _ _ _ _ hN hd hr hc => exists_singularPointBlowupChain_isGorenstein B hN hd hr hc)
    A hdim

end AlgebraicGeometry

end
