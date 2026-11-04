module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullbackLocalMulRestrict
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineVeroneseNaturality

/-!
# The two constructions of the comparison `k^*(L^{⊗ n}) ≅ (k^*L)^{⊗ n}` are the same

This library carries the comparison of the iterated tensor powers with their inverse images twice,
built from two different comparisons of the *integral* tensor powers of [Stacks, Tag 01CU]:

* `Stacks.TensorPowerPullback.pullbackIntPowIso`, which
  `Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.pullPowSection` and hence
  `…restrictPowSection` are built from — the reading of a section over an open as a global
  section on the open subscheme, whose multiplicativity for the local product is
  `…restrictPowSection_localMulSections`;
* `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`, which
  `Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso` and hence `pullSection`
  are built from — the family that carries the composition laws
  `…ProjTripleFunctorLaws.pullbackCompIso_comp_pullbackNatTensorPowIso_inv` and
  `…congr_hom_app_pullSection_comp`.

`StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullbackLocalMul` records the
duplication, and nothing identified the two families, so the multiplicativity available on one
side and the composition laws available on the other could not be used together.  **This file
identifies them**, which is what lets the
[Stacks, Tag 01NK] datum of [Stacks, Tag 01O9]'s clause (3) be compared along a nested pair of
opens of the base.

## The identification is two steps, and neither is an induction

The induction was already done, in a file named for something else.
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pullPowCompare_eq_powComparePull` — the
[Stacks, Tag 01NU] square saying that the comparison `L ^⊗ n ≅ L^{⊗ n}` of [Stacks, Tag 01CU]
commutes with pullback — is exactly the statement that the two families agree once the integral
powers are spelled as the pieces of the Laurent algebra.  What was left is that the two spellings
of the comparison of the *integral* powers, `pullbackIntPowIso` and
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullback`, are the same morphism, and they
are so by `rfl`.

## Main results

* `…ProjChartRatioPullbackLocalMul.pullbackIntPowIso_comp_powCompare_inv_eq`: the two
  constructions agree, for an arbitrary morphism of schemes.
* `…ProjChartRatioPullbackLocalMul.restrictNatTensorPowIso_hom_eq`: the special case at the
  inclusion of an open, which is the comparison `restrictPowSection` is stated against.
* `…ProjChartRatioPullbackLocalMul.restrictPowSection_eq'`: **`restrictPowSection` in the
  `pullbackNatTensorPowIso` family** — the reading of a section over an open as a global section
  on the open subscheme, written against the comparison that the composition laws are stated for.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullbackNatTensorPowIso)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (laurentPullback
  pullPowCompare_eq_powComparePull)
open Stacks.NonvanishingLocusRestrict (restrictSection)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {Y Y' : Scheme.{u}} (k : Y' ⟶ Y) (M : Y.Modules)
  [Stacks.Ample.IsInvertibleModule Y M]

/-- **The two constructions of the comparison `k^*(L^{⊗ n}) ≅ (k^*L)^{⊗ n}` agree.**  Conjugating
the comparison `Stacks.TensorPowerPullback.pullbackIntPowIso` of the integral tensor powers by
`Stacks.AlgebraicGeometry.CoherentMulSections.powCompare` on both sides gives the inverse of
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso`.

The content is [Stacks, Tag 01NU]'s square `pullPowCompare_eq_powComparePull`; what this adds is
that `pullbackIntPowIso` and
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullback` are the same morphism, which
holds by `rfl`. -/
public theorem pullbackIntPowIso_comp_powCompare_inv_eq (n : ℕ) :
    (Scheme.Modules.pullback k).map (powCompare M n).hom
        ≫ (Stacks.TensorPowerPullback.pullbackIntPowIso k.toLRSHom.toShHom M (n : ℤ)).hom
        ≫ (powCompare ((Scheme.Modules.pullback k).obj M) n).inv
      = (pullbackNatTensorPowIso k M n).inv :=
  (Category.assoc _ _ _).symm.trans
    ((Iso.comp_inv_eq _).mpr (pullPowCompare_eq_powComparePull k M n).symm)

/-- **The comparison `restrictPowSection` is stated against is the one the composition laws are
stated against.**  `restrictNatTensorPowIso` at the inclusion of an open is the inverse of
`pullbackNatTensorPowIso` there. -/
public theorem restrictNatTensorPowIso_hom_eq (U : Y.Opens) (n : ℕ) :
    (restrictNatTensorPowIso M U n).hom = (pullbackNatTensorPowIso U.ι M n).inv :=
  pullbackIntPowIso_comp_powCompare_inv_eq U.ι M n

/-- **`restrictPowSection` in the `pullbackNatTensorPowIso` family.**  The reading of a section of
`M^{⊗ n}` over an open `U` as a global section of `(M|_U)^{⊗ n}` on the open subscheme is
`Stacks.NonvanishingLocusRestrict.restrictSection` carried across the inverse of
`pullbackNatTensorPowIso`.

This is `restrictPowSection_eq` with the comparison replaced, by
`restrictNatTensorPowIso_hom_eq`, and it is the form in which the reading meets the composition
law `…ProjTripleFunctorLaws.pullbackCompIso_comp_pullbackNatTensorPowIso_inv`. -/
public theorem restrictPowSection_eq' (U : Y.Opens) (n : ℕ) (x : Γ(natTensorPow M n, U)) :
    restrictPowSection M U n x
      = (pullbackNatTensorPowIso U.ι M n).inv.app ⊤
          (restrictSection U (natTensorPow M n) x) := by
  rw [restrictPowSection_eq, restrictNatTensorPowIso_hom_eq]

end Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul

end
