module

public import StacksFrontier.AlgebraicGeometry.AffineCover.FiniteRefinement
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingSliceUnit
public import
  StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomothetyRestrictionMonoidal

/-!
# The homothety of a dualizing complex is an isomorphism

Let `X` be a locally Noetherian scheme and `K` a dualizing complex on `X`
([Stacks, Tag 0A87]). The homothety

`h_K : 𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(K, K)`

of `Stacks.SheafOfModules.derivedSheafHomothety` is an isomorphism.

## Main results

* `Stacks.Duality.isIso_derivedSheafHomothety_of_isDualizingComplex`: the homothety of a
  dualizing complex on a locally Noetherian scheme is an isomorphism.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry Stacks.SheafOfModules

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

/-- **The homothety of a dualizing complex on a locally Noetherian scheme is an isomorphism.**

For `X` a locally Noetherian scheme and `K` a dualizing complex on `X`, the homothety
`𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(K, K)` of `Stacks.SheafOfModules.derivedSheafHomothety` is invertible. -/
theorem isIso_derivedSheafHomothety_of_isDualizingComplex {W : Scheme.{u}}
    [IsLocallyNoetherian W] (K : DerivedCategory W.Modules) (hK : IsDualizingComplex K) :
    IsIso (derivedSheafHomothety W.sheaf K) :=
  isIso_derivedSheafHomothety_of_iso_derivedSheafHom_of_coversTop W.sheaf
    (AlgebraicGeometry.coversTop_of_iSup_eq_top (fun V : W.affineOpens ↦ (V : W.Opens))
      (AlgebraicGeometry.iSup_affineOpens_eq_top W))
    K (fun V ↦ restrictDDerivedSheafHomSelfUnitIso (V : W.Opens) V.property K hK)

end Stacks.Duality

end
