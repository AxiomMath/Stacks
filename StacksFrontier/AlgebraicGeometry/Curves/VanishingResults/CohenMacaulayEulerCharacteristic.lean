module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.CohenMacaulayDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveMorphismDualizing
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulay
public import StacksFrontier.Topology.Dimension.Equidimensional
import StacksCore.Tactic.StacksAttribute

/-!
# `χ(X, 𝒪_X) = -χ(X, ω_X)` for a Cohen--Macaulay curve

Let `k` be a field and `f : X ⟶ Spec k` a proper morphism with `X` Cohen--Macaulay and
equidimensional of dimension one, and let `ω_X = H^{-1}(ω_X^•)` be the dualizing sheaf of
[Stacks, Tag 0BS2], `ω_X^• = f^×(𝒪_{Spec k})`. This file proves the second formula of
[Stacks, Tag 0BS5],

**`χ(X, 𝒪_X) = -χ(X, ω_X)`.**

## Main results

* `AlgebraicGeometry.eulerCharacteristic_unit_eq_neg_eulerCharacteristic_dualizingSheafOverField`:
  the second formula of [Stacks, Tag 0BS5].

The first formula, `χ(X, 𝒪_X) = χ(X, ω_X^•)`, is
`eulerCharacteristic_unit_eq_eulerCharacteristicDerived_dualizingComplexOverField` of
`Curves/VanishingResults/DualizingComplexEulerCharacteristic.lean`.

## The proof

The source's: in the Cohen--Macaulay case `ω_X^• = ω_X[1]` ([Stacks, Tag 0BS3]), and with that
identification the first formula becomes the second. Concretely the isomorphism
`ω_X[1] ≅ ω_X^•`, `Stacks.Duality.dualizingSheafShiftOneIsoOfIsCohenMacaulay`, is fed to
`AlgebraicGeometry.finsum_alternating_finrank_unit_eq_neg_dualizingSheafOverField_of_iso`, which
reads off `dim_k H⁰(X, ω_X) = dim_k H¹(X, 𝒪_X)` and `dim_k H¹(X, ω_X) = dim_k H⁰(X, 𝒪_X)` from
the duality `H^i(X, ω_X^•) = Hom_k(H^{-i}(X, 𝒪_X), k)` of clause (4) of [Stacks, Tag 0BS2], both
Euler characteristics collapsing to `h⁰ - h¹` by [Stacks, Tag 02UZ].

`χ(X, ω_X)` is `AlgebraicGeometry.eulerCharacteristic`, which asks for `ω_X` to be coherent: that
is clause (2) of [Stacks, Tag 0BS2], here the coherence of the cohomology sheaves of a dualizing
complex (`Stacks.Duality.isCoherent_homology_of_isDualizingComplex`) applied to `ω_X^•`, which is
dualizing by
`Stacks.Duality.isDualizingComplex_dualizingComplexOverField_of_topologicalKrullDim_le_one`.

## References

* [Stacks Project, Tag 0BS5](https://stacks.math.columbia.edu/tag/0BS5)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- **The second formula of [Stacks, Tag 0BS5]: `χ(X, 𝒪_X) = -χ(X, ω_X)`** for a proper scheme
`X` over a field `k` which is Cohen--Macaulay and equidimensional of dimension one, with
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` the dualizing sheaf of [Stacks, Tag 0BS2].

As in the source, it is the first formula
`eulerCharacteristic_unit_eq_eulerCharacteristicDerived_dualizingComplexOverField` read through
`ω_X^• = ω_X[1]` of [Stacks, Tag 0BS3]
(`Stacks.Duality.dualizingSheafShiftOneIsoOfIsCohenMacaulay`), in the form
`AlgebraicGeometry.finsum_alternating_finrank_unit_eq_neg_dualizingSheafOverField_of_iso`. -/
@[stacks 0BS5 "second formula, chi(X, O_X) = - chi(X, omega_X), for X proper over a field, \
Cohen-Macaulay and equidimensional of dimension one, omega_X = H^(-1)(f^x(O_Spec k)) of Tag 0BS2"]
public theorem eulerCharacteristic_unit_eq_neg_eulerCharacteristic_dualizingSheafOverField
    (hcm : IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : (Stacks.Ample.unitModule X).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
    letI : (Stacks.Duality.dualizingSheafOverField f).IsCoherent :=
      Stacks.Duality.isCoherent_homology_of_isDualizingComplex
        (Stacks.Duality.isDualizingComplex_dualizingComplexOverField_of_topologicalKrullDim_le_one
          f hdim.le) (-1)
    eulerCharacteristic k f (Stacks.Ample.unitModule X) =
      -eulerCharacteristic k f (Stacks.Duality.dualizingSheafOverField f) :=
  finsum_alternating_finrank_unit_eq_neg_dualizingSheafOverField_of_iso f hdim.le
    (Stacks.Duality.dualizingSheafShiftOneIsoOfIsCohenMacaulay f hcm hequi hdim).symm

end AlgebraicGeometry

end
