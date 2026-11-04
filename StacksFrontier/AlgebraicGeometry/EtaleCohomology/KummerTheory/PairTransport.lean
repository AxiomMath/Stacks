module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.BaseAssociatedModuleTensorNatural
public import StacksFrontier.AlgebraicGeometry.Picard.BaseSitesFirstCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TensorPowerOfASection

/-!
# A pair on a scheme, read on the big `τ`-site

A pair `(ℒ, α)` on a scheme `S` — an invertible `𝒪_S`-module with a trivialization of its `n`-th
tensor power — is carried to a pair on the big `τ`-site of `S` by the associated-module functor
`𝓕 ↦ 𝓕^a`: the module `ℒ^a` is invertible, and the trivialization is transported by the
comparison `(ℒ^a)^{⊗ n} ≅ (ℒ^{⊗ n})^a` followed by `α^a` and the comparison of the two structure
sheaves.

## Main definitions

* `AlgebraicGeometry.basePairSheaf`: the invertible `𝒪_τ`-module `ℒ^a`.
* `AlgebraicGeometry.basePairTriv`: the transported trivialization `(ℒ^a)^{⊗ n} ≅ 𝒪_τ`.

## Main results

* `AlgebraicGeometry.basePairSheaf_isInvertible`: `ℒ^a` is invertible.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules (IsInvertible)
open Stacks.SheafOfModules.TensorPowerTransport (isInvertible_obj powerTransportIso)
open Stacks.Cohomology.Torsors.Generators (tpow)

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (τ : SiteKind) (n : ℕ)

/-- The invertible `𝒪_τ`-module attached to a pair on `S`: the associated module of its
invertible sheaf. -/
def basePairSheaf (P : TrivializedPower S n) :
    SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O) :=
  (BigFppfOver.baseAssociatedModule B S hS τ).obj P.sheaf

/-- **The associated module of the invertible sheaf of a pair is invertible.** -/
theorem basePairSheaf_isInvertible (P : TrivializedPower S n) :
    IsInvertible (BigFppfOver.baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
      (basePairSheaf B S hS τ n P) :=
  let := P.invertible
  isInvertible_obj S.presheaf (ringSheafCond S)
    (BigFppfOver.baseRingedSite B S hS τ).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
    (BigFppfOver.baseAssociatedModule B S hS τ)
    (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ)
    (BigFppfOver.baseAssociatedModuleTensorIso' B S hS τ) P.sheaf

/-- **The transported trivialization** `(ℒ^a)^{⊗ n} ≅ 𝒪_τ`: the comparison of the tensor powers,
the associated module of the trivialization of the pair, and the comparison of the two structure
sheaves. -/
def basePairTriv (P : TrivializedPower S n) :
    letI := basePairSheaf_isInvertible B S hS τ n P
    tpow (BigFppfOver.baseRingedSite B S hS τ) (basePairSheaf B S hS τ n P) n ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O) :=
  letI := P.invertible
  letI := basePairSheaf_isInvertible B S hS τ n P
  ((powerTransportIso S.presheaf (ringSheafCond S)
        (BigFppfOver.baseRingedSite B S hS τ).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
        (BigFppfOver.baseAssociatedModule B S hS τ)
        (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ)
        (BigFppfOver.baseAssociatedModuleTensorIso' B S hS τ) P.sheaf n).symm ≪≫
      (BigFppfOver.baseAssociatedModule B S hS τ).mapIso P.trivialization) ≪≫
    BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ

end AlgebraicGeometry

end
