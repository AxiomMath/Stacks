module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyGlue.AffineOpenVanishing
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageAffine.BasisVanishing
public import StacksFrontier.AlgebraicGeometry.RelativeMayerVietoris.Qcoh
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images along an affine morphism vanish

Let `f : X ⟶ S` be an affine morphism of schemes and `F` a quasi-coherent `𝒪_X`-module. Then
`R ᵖ f_* F = 0` for every `p > 0`. This is [Stacks, Tag 01XC], the relative form of the
vanishing of the higher cohomology of a quasi-coherent module on an affine.

The proof is the one of the source, in three steps.

* [Stacks, Tag 01E4], in the form
  `Stacks.Cohomology.HigherDirectImagePresheaf.higherDirectImage_iso_sheafify_preimageCohomology`,
  presents `R ᵖ f_* F` as the sheafification of the presheaf `V ↦ Hᵖ(f ⁻¹ᵁ V, F)`.
* Over an affine open `V` of `S` the inverse image `f ⁻¹ᵁ V` is an affine open of `X`, since `f`
  is affine, so that presheaf vanishes at `V` by [Stacks, Tag 01XB]
  (`Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`).
* The affine opens form a basis, and the sheafification of a presheaf vanishing on a basis is
  zero (`Stacks.Topology.BasisVanishing.isZero_sheafification_of_isZero_on_basis`).

Combining this with the degrees `p ≤ 0` — which are
`Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_higherDirectImage_of_neg` and
[Stacks, Tag 01LC] (`Stacks.AlgebraicGeometry.RelativeMayerVietoris.pushforward_isQuasicoherent`)
— gives the conclusion of [Stacks, Tag 01XJ] part (1) in **all** degrees for an affine morphism,
which is `isQuasicoherent_higherDirectImage_of_isAffineHom` below. For a general quasi-compact
quasi-separated morphism the degrees `p > 0` still require the relative Mayer–Vietoris long
exact sequence [Stacks, Tag 01EC].

## Main results

* `Stacks.AlgebraicGeometry.HigherDirectImageAffine.isZero_higherDirectImage_natDegree`: the
  vanishing in a degree presented as a natural number.
* `Stacks.AlgebraicGeometry.HigherDirectImageAffine.isZero_higherDirectImage_of_pos` is
  **[Stacks, Tag 01XC]**: `R ᵖ f_* F = 0` for `p > 0`, `f` affine and `F` quasi-coherent.
* `isQuasicoherent_higherDirectImage_of_isAffineHom`, in the same namespace: the conclusion of
  [Stacks, Tag 01XJ] part (1) for an affine morphism, in every degree `p : ℤ`.

## Implementation notes

[Stacks, Tag 01E4] is stated for a morphism of ringed spaces, in the spelling
`RingedSpaceModuleAdjunction.modulePushforward`, while the statement of [Stacks, Tag 01XJ] uses
`AlgebraicGeometry.Scheme.Modules.pushforward`. No bridge is needed: for `f : X ⟶ S` a morphism
of schemes, `X.ringCatSheaf = structureSheafRing X.toRingedSpace`,
`X.Modules = SheafOfModules (structureSheafRing X.toRingedSpace)` and
`Scheme.Modules.pushforward f = modulePushforward f.toShHom` all hold by `rfl`, and the proofs
below use the three identifications silently.

The three additivity and adjointness facts about `modulePushforward` and about the
presheaf-valued sections functor `Stacks.Cohomology.cohFunctor` are `local instance`s in
`StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf` and so
are not exported; they are reinstalled here, since without them the statements of [Stacks, Tag 01E4]
do not even elaborate.

`AlgebraicGeometry.IsSeparated.of_isAffineHom` is a lemma rather than an instance, so
quasi-separatedness of an affine morphism — needed for the degree-`0` input [Stacks, Tag 01LC] —
is installed with `have` at the one place that consumes it.

## References

* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology Stacks.Cohomology.HigherDirectImagePresheaf

universe u

namespace Stacks.AlgebraicGeometry.HigherDirectImageAffine

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

-- Seated from `RingedSpaceModuleAdjunction`, not restated: `modulePushforward_isRightAdjoint`
-- is a theorem there, so it is given the instance attribute where it is needed.
attribute [local instance] RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint
variable {X S : Scheme.{u}}

/-- **[Stacks, Tag 01XC] in a degree presented as a natural number.** For `f : X ⟶ S` an affine
morphism of schemes and `F` a quasi-coherent `𝒪_X`-module, `R ⁿ f_* F = 0` for `n > 0`.

The sheafification presentation of [Stacks, Tag 01E4] reduces this to the vanishing of
`Hⁿ(f ⁻¹ᵁ V, F)` for `V` in a basis of opens of `S`; the affine opens are such a basis, their
inverse images are affine opens because `f` is affine, and [Stacks, Tag 01XB] gives the
vanishing there. -/
alias isZero_higherDirectImage_natDegree :=
  Stacks.AffineHigherDirectImage.isZero_rightDerivedPlus_pushforward_nat

/-- **[Stacks, Tag 01XC].** Let `f : X ⟶ S` be an affine morphism of schemes and let `F` be a
quasi-coherent `𝒪_X`-module. Then the higher direct images `R ᵖ f_* F` vanish in every positive
degree. -/
theorem isZero_higherDirectImage_of_pos (f : X ⟶ S) [IsAffineHom f] (F : X.Modules)
    [F.IsQuasicoherent] (p : ℤ) (hp : 0 < p) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, (Int.toNat_of_nonneg hp.le).symm⟩
  exact isZero_higherDirectImage_natDegree f F n (by exact_mod_cast hp)

/-- **The conclusion of [Stacks, Tag 01XJ] part (1) for an affine morphism.** For `f : X ⟶ S` an
affine morphism of schemes and `F` a quasi-coherent `𝒪_X`-module, every higher direct image
`R ᵖ f_* F`, `p : ℤ`, is quasi-coherent.

The three degree ranges are separate inputs: negative degrees vanish for formal reasons, degree
`0` is [Stacks, Tag 01LC] — applicable because an affine morphism is quasi-compact and separated,
hence quasi-separated — and positive degrees vanish by [Stacks, Tag 01XC]. -/
@[ega "I 9.2.2" "clause a), special case",
  ega "I 9.5.1" "special case",
  sga "3 I 6.6" "special case",
  sga "3 III 0.13" "special case",
  sga "3 VIB 11.0" "special case"]
theorem isQuasicoherent_higherDirectImage_of_isAffineHom (f : X ⟶ S) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent] (p : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsQuasicoherent := by
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · exact HigherDirectImage.isQuasicoherent_higherDirectImage_of_neg f F p hp
  · have : IsSeparated f := IsSeparated.of_isAffineHom f
    exact (HigherDirectImage.isQuasicoherent_higherDirectImage_zero_iff f F).mpr
      (RelativeMayerVietoris.pushforward_isQuasicoherent f F)
  · exact HigherDirectImage.isQuasicoherent_of_isZero (R := S.ringCatSheaf)
      (isZero_higherDirectImage_of_pos f F p hp)

end Stacks.AlgebraicGeometry.HigherDirectImageAffine

end
