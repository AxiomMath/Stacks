module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistSectionCount
public import StacksFrontier.AlgebraicGeometry.Curves.LocallyFreeDualizingDuality
import StacksCore.Tactic.StacksAttribute

/-!
# The duality of dimensions on a proper curve at an invertible module

Let `k` be a field, `X` a proper `k`-scheme of topological Krull dimension at most one and
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` the dualizing sheaf of [Stacks, Tag 0BS2]. For `ℒ` an invertible
`𝒪_X`-module this file proves the two dimension formulas displayed in [Stacks, Tag 0BS4],

`dim_k H⁰(X, ℒ) = dim_k H¹(X, ℒ^{⊗ -1} ⊗_{𝒪_X} ω_X)` and
`dim_k H¹(X, ℒ) = dim_k H⁰(X, ℒ^{⊗ -1} ⊗_{𝒪_X} ω_X)`,

the first when `X` is Cohen--Macaulay and equidimensional of dimension one, as in the source, and
the second for every proper `X` of dimension at most one.

## Main results

* `AlgebraicGeometry`
  `.finrank_cohomologyOverField_zero_eq_one_tensorPowerModuleNegOneTensorDualizing`:
  **`dim_k H⁰(X, ℒ) = dim_k H¹(X, ℒ^{⊗ -1} ⊗ ω_X)`**, the third display of
  [Stacks, Tag 0BS4], on a Cohen--Macaulay curve.
* `AlgebraicGeometry`
  `.finrank_cohomologyOverField_one_eq_zero_tensorPowerModuleNegOneTensorDualizing`:
  **`dim_k H¹(X, ℒ) = dim_k H⁰(X, ℒ^{⊗ -1} ⊗ ω_X)`**, the fourth display of
  [Stacks, Tag 0BS4].

The first two displays of the Remark, the canonical isomorphisms, are
`Stacks.Duality.LocallyFreeTwist.dualityDerivedTensorLinearEquiv` and
`Stacks.Duality.LocallyFreeTwist.dualityTensorDualizingSheafLinearEquiv` of
`StacksFrontier/AlgebraicGeometry/Curves/LocallyFreeDualizingDuality.lean`.

## The argument

*The third display* is the source's: the second display at `ℰ = ℒ` and `i = 0` reads
`Hom_k(H⁰(X, ℒ), k) ≃ₗ[k] H¹(X, ℒ^∨ ⊗ ω_X)`, a vector space and its dual have the same dimension
(`Subspace.dual_finrank_eq`), and `ℒ^∨ ≅ ℒ^{⊗ -1}` by [Stacks, Tag 0B8K].

*The fourth display.* The duality of dimensions at a vector bundle,
`AlgebraicGeometry.finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one`,
reads `dim_k H⁰(X, ℰ^∨ ⊗ ω_X) = dim_k H¹(X, ℰ)` for a finite locally free `ℰ` of constant rank.
An invertible module is finite locally free of rank one, so it applies to `ℒ` itself; all that is
left is to rewrite the dual `ℒ^∨` as the inverse `ℒ^{⊗ -1}`, which is the last clause of
[Stacks, Tag 0B8K] — `Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf` — at the
multiplication `ℒ ⊗ ℒ^{⊗ -1} ≅ 𝒪_X`, and to transport the degree-zero cohomology along the
resulting isomorphism of sheaves with `AlgebraicGeometry.finrank_cohomologyOverField_eq_of_iso`.

That isomorphism `ℒ^{⊗ -1} ≅ ℒ^∨` is written inside the proof rather than named: the opposite
identification `ℒ ≅ (ℒ^{⊗ -1})^∨` is already available as
`AlgebraicGeometry.isoDualSheafTensorPowerModuleNegOne`, and a second named declaration for the
same clause of [Stacks, Tag 0B8K] would be a duplicate of it in a different spelling.

## Hypotheses

The fourth display is proved without the Cohen--Macaulay and equidimensionality conditions under
which the Remark states it, so it is more general than the source in its setting. The strongest
form of that dimension count in the library is
`AlgebraicGeometry.finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one` of
`Curves/VanishingResults/DualizingDimensionDualityBundle.lean`, with an arbitrary finite locally
free `ℰ` of constant rank in place of `ℒ`.

## References

* [Stacks Project, Tag 0BS4](https://stacks.math.columbia.edu/tag/0BS4)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.SheafOfModules (dualSheaf)
open Stacks.SheafOfModules.Invertible (mulNegOneIso tensorPowerModule tensorProductIso)

universe u

namespace AlgebraicGeometry

/-- **`dim_k H¹(X, ℒ) = dim_k H⁰(X, ℒ^{⊗ -1} ⊗ ω_X)`** for an invertible `𝒪_X`-module `ℒ` on a
proper scheme `X` of dimension at most one over a field `k`, with
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` the dualizing sheaf of [Stacks, Tag 0BS2].

This is the last of the four formulas displayed in [Stacks, Tag 0BS4]. The proof is the duality
of dimensions at a vector bundle,
`AlgebraicGeometry.finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one`,
at `ℒ` itself — an invertible module being finite locally free of rank one — with the dual `ℒ^∨`
rewritten as the inverse `ℒ^{⊗ -1}` by the last clause of [Stacks, Tag 0B8K]. Neither the
Cohen--Macaulay nor the equidimensionality condition under which the Remark states it is
used. -/
@[stacks 0BS4 "the fourth display, dim_k H^1(X, L) = dim_k H^0(X, L^(tensor -1) tensor omega_X), \
at an invertible L and the dualizing sheaf of Tag 0BS2, for every proper X of dimension at most \
one over k; the Remark's Cohen-Macaulay and equidimensionality conditions are not needed"]
public theorem finrank_cohomologyOverField_one_eq_zero_tensorPowerModuleNegOneTensorDualizing
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Module.finrank k (cohomologyOverField k f L 1) =
      Module.finrank k (cohomologyOverField k f
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
            CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
              (CategoryTheory.forget₂ CommRingCat RingCat) X.ringCatSheaf.property⟩).obj
            (tensorPowerModule L (-1))).obj (Stacks.Duality.dualizingSheafOverField f))) 0) :=
  (finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one f hdim L 1).symm.trans
    (finrank_cohomologyOverField_eq_of_iso k f
      (tensorProductIso X.presheaf X.ringCatSheaf.property
        (Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.presheaf
          X.ringCatSheaf.property L _
          (mulNegOneIso X.presheaf X.ringCatSheaf.property L))
        (Iso.refl (Stacks.Duality.dualizingSheafOverField f))) 0).symm

/-- **`dim_k H⁰(X, ℒ) = dim_k H¹(X, ℒ^{⊗ -1} ⊗ ω_X)`** for an invertible `𝒪_X`-module `ℒ` on a
proper scheme `X` over a field `k` which is Cohen--Macaulay and equidimensional of dimension one,
with `ω_X` the dualizing sheaf of [Stacks, Tag 0BS2].

This is the third display of [Stacks, Tag 0BS4], and the source's proof: the second display at
`ℰ = ℒ` and `i = 0`, `Hom_k(H⁰(X, ℒ), k) ≃ₗ[k] H¹(X, ℒ^∨ ⊗ ω_X)`, which is
`Stacks.Duality.LocallyFreeTwist.dualityTensorDualizingSheafLinearEquiv`, together with the
equality of the dimensions of a vector space and of its dual, and the identification of the dual
`ℒ^∨` with the inverse `ℒ^{⊗ -1}` ([Stacks, Tag 0B8K]). -/
@[stacks 0BS4 "the third display, dim_k H^0(X, L) = dim_k H^1(X, L^(tensor -1) tensor omega_X), \
for X proper over k, Cohen-Macaulay and equidimensional of dimension one, at the dualizing sheaf \
of Tag 0BS2"]
public theorem finrank_cohomologyOverField_zero_eq_one_tensorPowerModuleNegOneTensorDualizing
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Module.finrank k (cohomologyOverField k f L 0) =
      Module.finrank k (cohomologyOverField k f
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
            CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
              (CategoryTheory.forget₂ CommRingCat RingCat) X.ringCatSheaf.property⟩).obj
            (tensorPowerModule L (-1))).obj (Stacks.Duality.dualizingSheafOverField f))) 1) := by
  have hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  have e := Stacks.Duality.LocallyFreeTwist.dualityTensorDualizingSheafLinearEquiv
    (X := X) L (hE := hL) f hcm hequi hdim 0
  refine ((Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f L
    0).finrank_eq.trans (Subspace.dual_finrank_eq.symm.trans e.finrank_eq)).trans ?_
  refine ((Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f _
    1).finrank_eq.symm.trans ?_)
  exact finrank_cohomologyOverField_eq_of_iso k f
    (tensorProductIso X.presheaf X.ringCatSheaf.property
      (Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.presheaf
        X.ringCatSheaf.property L _
        (mulNegOneIso X.presheaf X.ringCatSheaf.property L)).symm
      (Iso.refl (Stacks.Duality.dualizingSheafOverField f))) 1

end AlgebraicGeometry

end
