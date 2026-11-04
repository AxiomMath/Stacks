module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTrace
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentHomology

/-!
# Pseudo-coherence of `D⁻_Coh` on a Noetherian scheme, for the sheafy trace

Let `X` be a Noetherian scheme. An object of `D_QCoh(𝒪_X)` lying in `D⁻_Coh(𝒪_X)` is
pseudo-coherent. This is the direction of [Stacks, Tag 08E8] that the proof of
[Stacks, Tag 0GEW] uses, at `L` and at `Rf_*L`, to reduce the invertibility of the sheafy trace
map of [Stacks, Tag 0B6H],

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`,

for a proper morphism `f : X ⟶ Y` of Noetherian schemes to the bounded below pseudo-coherent
criterion of [Stacks, Tag 0GEV].

## Main results

* `Stacks.Duality.isPseudoCoherent_of_derivedCategoryBMinus_isCoherent` — the direction of
  [Stacks, Tag 08E8] used by [Stacks, Tag 0GEW].

[Stacks, Tag 0GEW] itself is
`Stacks.Duality.isIso_sheafyTrace_of_isProper_of_derivedCategoryBMinus`, in
`StacksFrontier/AlgebraicGeometry/Duality/SheafyTraceProperIso.lean`.

## References

* [Stacks Project, Tag 0GEW](https://stacks.math.columbia.edu/tag/0GEW)
* [Stacks Project, Tag 0GEV](https://stacks.math.columbia.edu/tag/0GEV)
* [Stacks Project, Tag 0B6H](https://stacks.math.columbia.edu/tag/0B6H)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  Opposite TopologicalSpace
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Duality

universe u

attribute [local instance] HasDerivedCategory.standard

/-- An object of `D_QCoh(𝒪_X)` lying in `D⁻_Coh(𝒪_X)` on a Noetherian scheme is
pseudo-coherent: this is the direction of [Stacks, Tag 08E8] that [Stacks, Tag 0GEW] uses. -/
theorem isPseudoCoherent_of_derivedCategoryBMinus_isCoherent {X : Scheme.{u}} [IsNoetherian X]
    (L : quasiCoherentDerivedCategory X)
    (hL : DerivedCategoryB.derivedCategoryBMinus
      (fun N : X.Modules => N.IsCoherent) L.obj) :
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) L.obj :=
  (isPseudoCoherent_iff_boundedAbove_coherent_homology X L).2 ⟨hL.1, hL.2⟩

end Stacks.Duality

end
