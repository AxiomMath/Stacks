module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullbackLocalMul
public import StacksFrontier.AlgebraicGeometry.Divisors.SectionPowerOpen

/-!
# Reading a section of `ℒ^{⊗ n}` over an open as a global section: the two comparisons agree

Let `Y` be a scheme, `M` an invertible `𝒪_Y`-module and `U` an open of `Y`.  A section `x` of
`M^{⊗ n}` over `U` gives two global sections on the open subscheme `U`:
`Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection M U n x`, a section of
`(M|_U)^{⊗ n}`, and `Stacks.NonvanishingLocusRestrict.restrictSection U (M^{⊗ n}) x`, a section of
`(M^{⊗ n})|_U`.  They agree across the comparison isomorphism of the two targets, and the
nonvanishing open of `restrictPowSection M U n x` is the preimage under `U.ι` of the nonvanishing
open of `x`.

## Main definitions

* `restrictNatTensorPowIso`: the comparison `(M^{⊗ n})|_U ≅ (M|_U)^{⊗ n}`.
* `restrictPowSectionHom`: `restrictPowSection` as an additive map.

## Main results

* `restrictPowSection_eq`: `restrictPowSection M U n x` is `restrictSection U (M^{⊗ n}) x`
  carried across `restrictNatTensorPowIso`.
* `nonvanishingOpen_restrictPowSection`: the nonvanishing open of `restrictPowSection M U n x` is
  the preimage under `U.ι` of the nonvanishing open of `x`.
* `restrictSection_add` and `restrictPowSection_add`: both sections are additive in `x`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.SectionPowerOpen (nonvanishingOpenOn)
open Stacks.NonvanishingLocusRestrict (restrictSection top_le_ι_preimage_self
  nonvanishingLocus_restrictSection)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {Y : Scheme.{u}} (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M] (U : Y.Opens)

/-! ### The comparison of the two targets -/

/-- The comparison `(M^{⊗ n})|_U ≅ (M|_U)^{⊗ n}`: the inverse image along the inclusion of `U` of
the identification `Stacks.AlgebraicGeometry.CoherentMulSections.powCompare` of the iterated
tensor powers with the integral ones, then the comparison
`Stacks.TensorPowerPullback.pullbackIntPowIso` of [Stacks, Tag 01CD], then that identification
again on the restricted module. -/
public def restrictNatTensorPowIso (n : ℕ) :
    (Scheme.Modules.pullback U.ι).obj (natTensorPow M n)
      ≅ natTensorPow ((Scheme.Modules.pullback U.ι).obj M) n :=
  (Scheme.Modules.pullback U.ι).mapIso (powCompare M n) ≪≫
    Stacks.TensorPowerPullback.pullbackIntPowIso U.ι.toLRSHom.toShHom M (n : ℤ) ≪≫
    (powCompare ((Scheme.Modules.pullback U.ι).obj M) n).symm

/-! ### The two readings agree -/

/-- The global section `restrictPowSection M U n x` of the tensor power of the restriction is the
global section `Stacks.NonvanishingLocusRestrict.restrictSection U (M^{⊗ n}) x` of the restriction
of the tensor power, carried across `restrictNatTensorPowIso`. -/
public theorem restrictPowSection_eq (n : ℕ) (x : Γ(natTensorPow M n, U)) :
    restrictPowSection M U n x
      = (restrictNatTensorPowIso M U n).hom.app ⊤ (restrictSection U (natTensorPow M n) x) := by
  have hnat : ∀ z : Γ((Scheme.Modules.pullback U.ι).obj (natTensorPow M n), U.ι ⁻¹ᵁ U),
      (restrictNatTensorPowIso M U n).hom.app ⊤
          (((Scheme.Modules.pullback U.ι).obj (natTensorPow M n)).presheaf.map
            (homOfLE (top_le_ι_preimage_self U)).op z)
        = (natTensorPow ((Scheme.Modules.pullback U.ι).obj M) n).presheaf.map
            (homOfLE (top_le_ι_preimage_self U)).op
            ((restrictNatTensorPowIso M U n).hom.app (U.ι ⁻¹ᵁ U) z) :=
    fun z => congrFun (congrArg (fun g => g.hom)
      ((restrictNatTensorPowIso M U n).hom.val.naturality
        (homOfLE (top_le_ι_preimage_self U)).op)) z
  refine Eq.trans ?_ (hnat _).symm
  unfold restrictPowSection pullPowSection
  exact congrArg _ (congrArg _ (congrArg _ (Stacks.RingedSpace.pullbackUnit_naturality
    U.ι.toLRSHom.toShHom (powCompare M n).hom (op U) x).symm))

/-! ### The nonvanishing open -/

/-- On the open subscheme `U`, the global section `restrictPowSection M U n x` of
`(M|_U)^{⊗ n}` fails to vanish exactly at the points of `U` lying over the open `U_x ⊆ Y` of
[Stacks, Tag 01CY] on which `x` does not vanish. -/
public theorem nonvanishingOpen_restrictPowSection (n : ℕ) (x : Γ(natTensorPow M n, U)) :
    nonvanishingOpen U.toScheme (natTensorPow ((Scheme.Modules.pullback U.ι).obj M) n)
        (restrictPowSection M U n x)
      = U.ι ⁻¹ᵁ nonvanishingOpenOn (natTensorPow M n) U x := by
  refine Opens.ext ?_
  show Stacks.Ample.nonvanishingLocus _ (restrictPowSection M U n x) = _
  rw [restrictPowSection_eq]
  exact (Stacks.Ample.nonvanishingLocus_congr (restrictNatTensorPowIso M U n)
      (restrictSection U (natTensorPow M n) x)).trans
    (nonvanishingLocus_restrictSection U (natTensorPow M n) x)

/-! ### Additivity -/

/-- `Stacks.NonvanishingLocusRestrict.restrictSection` is additive. -/
public theorem restrictSection_add (N : Y.Modules) (x y : Γ(N, U)) :
    restrictSection U N (x + y) = restrictSection U N x + restrictSection U N y :=
  (congrArg _ (Stacks.RingedSpace.pullbackUnit_add U.ι.toLRSHom.toShHom N (op U) x y)).trans
    (map_add _ _ _)

/-- `restrictPowSection` is additive. -/
public theorem restrictPowSection_add (n : ℕ) (x y : Γ(natTensorPow M n, U)) :
    restrictPowSection M U n (x + y)
      = restrictPowSection M U n x + restrictPowSection M U n y := by
  rw [restrictPowSection_eq, restrictPowSection_eq, restrictPowSection_eq,
    restrictSection_add U (natTensorPow M n) x y]
  exact map_add _ _ _

/-- `restrictPowSection` as an additive map. -/
public def restrictPowSectionHom (n : ℕ) :
    Γ(natTensorPow M n, U) →+ Γ(natTensorPow ((Scheme.Modules.pullback U.ι).obj M) n, ⊤) :=
  AddMonoidHom.mk' (restrictPowSection M U n) (restrictPowSection_add M U n)

/-- `restrictPowSectionHom M U n` sends `x` to `restrictPowSection M U n x`. -/
@[simp] public theorem restrictPowSectionHom_apply (n : ℕ) (x : Γ(natTensorPow M n, U)) :
    restrictPowSectionHom M U n x = restrictPowSection M U n x := rfl

end Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul

end
