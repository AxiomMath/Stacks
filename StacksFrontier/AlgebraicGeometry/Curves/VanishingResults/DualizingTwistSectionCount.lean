module

public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Devissage
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingDimensionDualityBundle
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingRiemannRoch
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The section count of a twist of the dualizing sheaf of a proper curve

In Situation [Stacks, Tag 0B5D] — a field `k` and a proper one-dimensional `k`-scheme `X` with
`H⁰(X, 𝒪_X) = k` — let `ω_X` be the dualizing sheaf of `X` and `ℒ` an invertible `𝒪_X`-module.
This file evaluates the count of global sections of the quotient in a presentation

`0 ⟶ ω_X ⟶ ω_X ⊗ ℒ ⟶ 𝒬 ⟶ 0`

whose quotient has zero-dimensional support: under the two vanishing hypotheses
`H⁰(X, ℒ^{⊗ -1}) = 0` and `H¹(X, ω_X ⊗ ℒ) = 0`, that count is exactly `deg(ℒ)`.

## Main definitions

The elided prefix throughout is `AlgebraicGeometry`.

* `isoDualSheafTensorPowerModuleNegOne`: an invertible module is the dual of its inverse,
  `ℒ ≅ (ℒ^{⊗ -1})^∨`.
* `tensorSheafDualSheafTensorPowerModuleNegOneIso`: the resulting identification
  `(ℒ^{⊗ -1})^∨ ⊗ ℳ ≅ ℳ ⊗ ℒ`.

## Main results

* `CohenMacaulayCurveSituation.finrank_cohomologyOverField_zero_eq_invertibleCurveDegree`:
  **`dim_k H⁰(X, 𝒬) = deg(ℒ)`** for a short exact sequence `0 ⟶ ω_X ⟶ ω_X ⊗ ℒ ⟶ 𝒬 ⟶ 0` of
  coherent modules whose quotient has zero-dimensional support.
* `CohenMacaulayCurveSituation.finrank_cohomologyOverField_zero_cokernel_eq_invertibleCurveDegree`:
  the same count for the cokernel of a monomorphism `ω_X ⟶ ω_X ⊗ ℒ`, which is the shape in which
  the sequence is produced.
* `finrank_cohomologyOverField_zero_tensorSheaf_dualizing_eq_one_tensorPowerModule`:
  **`dim_k H⁰(X, ω_X ⊗ ℒ) = dim_k H¹(X, ℒ^{⊗ -1})`**, the duality of dimensions of
  [Stacks, Tag 0BS6] clause (3) read at the invertible module `ℒ^{⊗ -1}`.
* `invertibleCurveDegree_tensorPowerModule_neg_one_of_topologicalKrullDim_le_one`:
  **`deg(ℒ^{⊗ -1}) = -deg(ℒ)`**, with no `AlgebraicGeometry.IsCurve` hypothesis.
* `CohenMacaulayCurveSituation`
  `.eulerCharacteristic_tensorSheaf_dualizing_sub_eq_invertibleCurveDegree`:
  **`χ(X, ω_X ⊗ ℒ) - χ(X, ω_X) = deg(ℒ)`**, which is the whole of the computation below; the
  section count is this difference.
* `finrank_cohomologyOverField_zero_eq_zero_of_subsingleton_sections`: `H⁰(X, ℳ)` has dimension
  zero when `ℳ` has no nonzero global section.

## The argument

Write `e = χ(X, 𝒪_X)`, `𝒩 = ℒ^{⊗ -1}` and `ℱ = ω_X ⊗ ℒ`.

1. `dim_k H⁰(X, 𝒬) = χ(X, ℱ) - χ(X, ω_X)`, which is
   `AlgebraicGeometry.CohenMacaulayCurveSituation`
   `.finrank_cohomologyOverField_zero_eq_eulerCharacteristic_sub`.
2. Both Euler characteristics below collapse to `h⁰ - h¹` by [Stacks, Tag 02UZ] on the
   one-dimensional `X`, through `AlgebraicGeometry.eulerCharacteristic_eq_sub_of_isZero`. With
   `H¹(X, ℱ) = 0` this gives `χ(X, ℱ) = dim_k H⁰(X, ℱ)`, and with `H⁰(X, 𝒩) = 0` it gives
   `χ(X, 𝒩) = -dim_k H¹(X, 𝒩)`.
3. `dim_k H⁰(X, ℱ) = dim_k H¹(X, 𝒩)`. This is the duality of dimensions at the vector bundle
   `𝒩`, `AlgebraicGeometry`
   `.finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one`, whose left-hand
   side `𝒩^∨ ⊗ ω_X` is identified with `ℱ` below.
4. `deg(𝒩) = -deg(ℒ)`, and `deg` of an invertible module is `χ` of it minus `e`
   (`AlgebraicGeometry.invertibleCurveDegree_eq_eulerCharacteristic_sub`), so
   `dim_k H¹(X, 𝒩) = -χ(X, 𝒩) = deg(ℒ) - e`.
5. `χ(X, ω_X) = -e` is `AlgebraicGeometry.CohenMacaulayCurveSituation`
   `.finsum_alternating_finrank_unit_eq_neg_dualizingSheaf`.

Together: `dim_k H⁰(X, 𝒬) = χ(X, ℱ) - χ(X, ω_X) = (deg(ℒ) - e) + e = deg(ℒ)`.

## Implementation notes

**The identification `𝒩^∨ ⊗ ω_X ≅ ω_X ⊗ ℒ`.** The dual of `𝒩 = ℒ^{⊗ -1}` is `ℒ`, because
`ℒ` is a tensor inverse of `𝒩` and a tensor inverse is the dual by the last clause of
[Stacks, Tag 0B8K], which is `Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf`. The
tensor inverse datum is the multiplication `ℒ ⊗ ℒ^{⊗ -1} ≅ 𝒪_X`
(`Stacks.SheafOfModules.Invertible.mulNegOneIso`) composed with the braiding
`Stacks.SheafOfModules.tensorSheafBraiding`, which also supplies the final exchange of the two
factors of the tensor product.

**Why `deg(ℒ^{⊗ -1}) = -deg(ℒ)` is reproved here.**
`AlgebraicGeometry.invertibleCurveDegree_tensorSheaf_tensorPowerModule_neg_one` is the library
two-variable form, but it carries an `AlgebraicGeometry.IsCurve` instance that Situation
[Stacks, Tag 0B5D] does not supply, because it invokes the `IsCurve` form of [Stacks, Tag 0AYX].
The proof below is the same, with the unconditional form
`AlgebraicGeometry.curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one` in its place;
the `_of_topologicalKrullDim_le_one` suffix follows that pair.

**The short exact sequence is given by its terms and maps**, together with equations identifying
the first two terms with `ω_X` and `ω_X ⊗ ℒ`, rather than by a
`CategoryTheory.ShortComplex` whose components are those two modules. The tensor product sheaf
carries its own spelling of the category of `𝒪_X`-modules, so a morphism written directly out of
it is not a morphism of `AlgebraicGeometry.Scheme.Modules`; taking the terms as modules on `X`
and the identifications as hypotheses keeps every morphism at the spelling a consumer has.

## References

* [Stacks Project, Tag 0B5B](https://stacks.math.columbia.edu/tag/0B5B)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules (dualSheaf tensorSheafBraiding)
open Stacks.SheafOfModules.Invertible (mulNegOneIso tensorPowerModule tensorProductIso)

universe u

namespace AlgebraicGeometry

/-! ### The dual of the inverse of an invertible module -/

/-- **An invertible module is the dual of its inverse**: `ℒ ≅ (ℒ^{⊗ -1})^∨`.

The multiplication `ℒ^{⊗ -1} ⊗ ℒ ≅ 𝒪_X` exhibits `ℒ` as a tensor inverse of `ℒ^{⊗ -1}`, and a
tensor inverse is the dual sheaf by the last clause of [Stacks, Tag 0B8K]. -/
@[sga "6 VIII 3.5" "Sheaf-level clause"]
public def isoDualSheafTensorPowerModuleNegOne (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    L ≅ dualSheaf X.presheaf X.ringCatSheaf.property (tensorPowerModule L (-1)) :=
  Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.presheaf
    X.ringCatSheaf.property (tensorPowerModule L (-1)) L
    (tensorSheafBraiding X.presheaf X.ringCatSheaf.property (tensorPowerModule L (-1)) L ≪≫
      mulNegOneIso X.presheaf X.ringCatSheaf.property L)

/-- **`(ℒ^{⊗ -1})^∨ ⊗ ℳ ≅ ℳ ⊗ ℒ`** for an invertible `ℒ` and an arbitrary `𝒪_X`-module `ℳ`:
the dual of `ℒ^{⊗ -1}` is `ℒ` by `AlgebraicGeometry.isoDualSheafTensorPowerModuleNegOne`, and the
braiding of the tensor product sheaf exchanges the two factors. -/
public def tensorSheafDualSheafTensorPowerModuleNegOneIso (X : Scheme.{u}) (L M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
            (X.ringCatSheaf.property)⟩).obj
        ((dualSheaf X.presheaf X.ringCatSheaf.property (tensorPowerModule L (-1))))).obj (M)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
            (X.ringCatSheaf.property)⟩).obj (M)).obj (L)) :=
  tensorProductIso X.presheaf X.ringCatSheaf.property
      (isoDualSheafTensorPowerModuleNegOne X L).symm (Iso.refl M) ≪≫
    tensorSheafBraiding X.presheaf X.ringCatSheaf.property L M

/-! ### The duality of dimensions at the inverse of an invertible module -/

/-- **`dim_k H⁰(X, ω_X ⊗ ℒ) = dim_k H¹(X, ℒ^{⊗ -1})`** for an invertible `𝒪_X`-module `ℒ` on a
proper scheme `X` of dimension at most one over a field `k`, with
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` the dualizing sheaf of [Stacks, Tag 0BS2].

This is the duality of dimensions of [Stacks, Tag 0BS6] clause (3) at `i = 1`, available as
`AlgebraicGeometry.finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one`,
read at the vector bundle `ℒ^{⊗ -1}` — which is finite locally free of rank one — and with its
twist `(ℒ^{⊗ -1})^∨ ⊗ ω_X` identified with `ω_X ⊗ ℒ` by
`AlgebraicGeometry.tensorSheafDualSheafTensorPowerModuleNegOneIso`. -/
public theorem finrank_cohomologyOverField_zero_tensorSheaf_dualizing_eq_one_tensorPowerModule
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Module.finrank k (cohomologyOverField k f
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
              Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
                (X.ringCatSheaf.property)⟩).obj
            ((Stacks.Duality.dualizingSheafOverField f))).obj (L))) 0) =
      Module.finrank k (cohomologyOverField k f (tensorPowerModule L (-1)) 1) :=
  Eq.trans
    (finrank_cohomologyOverField_eq_of_iso k f
      (tensorSheafDualSheafTensorPowerModuleNegOneIso X L
        (Stacks.Duality.dualizingSheafOverField f)) 0).symm
    (finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one f hdim
      (tensorPowerModule L (-1)) 1)

/-! ### The degree of the inverse of an invertible module -/

/-- **`deg(ℒ^{⊗ -1}) = -deg(ℒ)`** for an invertible module `ℒ` on a proper scheme of dimension at
most one over a field, with no `AlgebraicGeometry.IsCurve` hypothesis. -/
public theorem invertibleCurveDegree_tensorPowerModule_neg_one_of_topologicalKrullDim_le_one
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    invertibleCurveDegree k f hdim (tensorPowerModule L (-1)) =
      -invertibleCurveDegree k f hdim L := by
  have hT : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj
          (tensorPowerModule L (-1)))) :=
    isInvertible_tensorSheaf_tensorPowerModule_neg_one L L
  have hadd := curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one k f hdim L
    (tensorPowerModule L (-1)) 1 1
  have hzero : invertibleCurveDegree k f hdim
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj
          (tensorPowerModule L (-1)))) = 0 :=
    invertibleCurveDegree_eq_zero_of_iso_unit k f hdim _
      (mulNegOneIso X.presheaf X.ringCatSheaf.property L)
  rw [invertibleCurveDegree_eq_curveDegree_one k f hdim
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj
        (tensorPowerModule L (-1))))] at hzero
  rw [invertibleCurveDegree_eq_curveDegree_one k f hdim (tensorPowerModule L (-1)),
    invertibleCurveDegree_eq_curveDegree_one k f hdim L]
  simp only [one_mul, Nat.cast_one] at hadd hzero ⊢
  omega

/-! ### The vanishing of the global sections of the inverse -/

/-- **`H⁰(X, ℳ) = 0` when `ℳ` has no nonzero global section.** The two are the same `k`-vector
space by `AlgebraicGeometry.cohomologyOverFieldZeroLinearEquivGlobalSectionsOver`, and a
subsingleton module has dimension zero. -/
public theorem finrank_cohomologyOverField_zero_eq_zero_of_subsingleton_sections
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (M : X.Modules) (hM : Subsingleton Γ(M, (⊤ : X.Opens))) :
    Module.finrank k (cohomologyOverField k f M 0) = 0 :=
  have : Subsingleton ((globalSectionsOver f).obj M) := hM
  have : Subsingleton (cohomologyOverField k f M 0) :=
    (cohomologyOverFieldZeroLinearEquivGlobalSectionsOver f M).toEquiv.subsingleton
  Module.finrank_zero_of_subsingleton

namespace CohenMacaulayCurveSituation

/-! ### The Euler characteristic of the twist -/

/-- **`χ(X, ω_X ⊗ ℒ) - χ(X, ω_X) = deg(ℒ)`** in Situation [Stacks, Tag 0B5D], for an invertible
`ℒ` with `H⁰(X, ℒ^{⊗ -1}) = 0` and `H¹(X, ω_X ⊗ ℒ) = 0`.

Both Euler characteristics below collapse to `h⁰ - h¹` by [Stacks, Tag 02UZ], so
`χ(X, ω_X ⊗ ℒ) = dim_k H⁰(X, ω_X ⊗ ℒ)` by the second hypothesis; that dimension is
`dim_k H¹(X, ℒ^{⊗ -1})` by the duality of dimensions
(`AlgebraicGeometry`
`.finrank_cohomologyOverField_zero_tensorSheaf_dualizing_eq_one_tensorPowerModule`), and
`χ(X, ℒ^{⊗ -1}) = -dim_k H¹(X, ℒ^{⊗ -1})` by the first hypothesis. The degree of an
invertible module is its Euler characteristic minus that of `𝒪_X`, and
`deg(ℒ^{⊗ -1}) = -deg(ℒ)`, so `dim_k H¹(X, ℒ^{⊗ -1}) = deg(ℒ) - χ(X, 𝒪_X)`; finally
`χ(X, ω_X) = -χ(X, 𝒪_X)`. -/
public theorem eulerCharacteristic_tensorSheaf_dualizing_sub_eq_invertibleCurveDegree
    {S : CohenMacaulayCurveSituation.{u}} (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    [(Stacks.Duality.dualizingSheafOverField S.f).IsCoherent]
    (F : S.X.Modules) [F.IsCoherent]
    (hF : F = (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
          (S.X.ringCatSheaf.property)⟩).obj
      ((Stacks.Duality.dualizingSheafOverField S.f))).obj (L)))
    (hinv : Subsingleton Γ(tensorPowerModule L (-1), (⊤ : S.X.Opens)))
    (hvan : IsZero (cohomologyOverField S.k S.f F 1)) :
    eulerCharacteristic S.k S.f F -
        eulerCharacteristic S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) =
      invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L := by
  subst hF
  have hvanish : ∀ (M : S.X.Modules) (m : ℕ), 2 ≤ m →
      IsZero (cohomologyOverField S.k S.f M m) := fun M m hm =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le S.k S.f M (d := 1)
      (le_of_eq S.dimension_one) (by omega)
  have hunit : (SheafOfModules.unit S.X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k S.f
  have hNcoh : (tensorPowerModule L (-1)).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank S.k S.f
      (tensorPowerModule L (-1)) 1
  have htwist := eulerCharacteristic_eq_sub_of_isZero S.k S.f
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
            (S.X.ringCatSheaf.property)⟩).obj
        ((Stacks.Duality.dualizingSheafOverField S.f))).obj (L)))
      (fun m hm => hvanish _ m hm)
  have htwistone : Module.finrank S.k (cohomologyOverField S.k S.f
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
              (S.X.ringCatSheaf.property)⟩).obj
          ((Stacks.Duality.dualizingSheafOverField S.f))).obj (L))) 1) = 0 :=
    have := ModuleCat.subsingleton_of_isZero hvan
    Module.finrank_zero_of_subsingleton
  have hduality :=
    finrank_cohomologyOverField_zero_tensorSheaf_dualizing_eq_one_tensorPowerModule S.k S.f
      (le_of_eq S.dimension_one) L
  have hinverse := eulerCharacteristic_eq_sub_of_isZero S.k S.f (tensorPowerModule L (-1))
    (fun m hm => hvanish _ m hm)
  have hinvzero : Module.finrank S.k
      (cohomologyOverField S.k S.f (tensorPowerModule L (-1)) 0) = 0 :=
    finrank_cohomologyOverField_zero_eq_zero_of_subsingleton_sections S.k S.f _ hinv
  have hneg := invertibleCurveDegree_tensorPowerModule_neg_one_of_topologicalKrullDim_le_one
    S.k S.f (le_of_eq S.dimension_one) L
  have hdeg : invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one)
        (tensorPowerModule L (-1)) =
      eulerCharacteristic S.k S.f (tensorPowerModule L (-1)) -
        eulerCharacteristic S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) :=
    invertibleCurveDegree_eq_eulerCharacteristic_sub S.k S.f (le_of_eq S.dimension_one) _
  have hdual : eulerCharacteristic S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) =
      -eulerCharacteristic S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) :=
    finsum_alternating_finrank_unit_eq_neg_dualizingSheaf S
  omega

/-! ### The section count -/

/-- **`dim_k H⁰(X, 𝒬) = deg(ℒ)`** in Situation [Stacks, Tag 0B5D], for a short exact sequence
`0 ⟶ ω_X ⟶ ω_X ⊗ ℒ ⟶ 𝒬 ⟶ 0` of coherent `𝒪_X`-modules whose quotient `𝒬` has
zero-dimensional support, an invertible `ℒ` with `H⁰(X, ℒ^{⊗ -1}) = 0` and
`H¹(X, ω_X ⊗ ℒ) = 0`.

This is the count `dim_k H⁰(X, 𝒬) = deg(ℒ)` that the field
`AlgebraicGeometry.CohenMacaulayCurveSituation.VanishingSectionData.finrank_cohomology_zero`
asks for. By
`AlgebraicGeometry.CohenMacaulayCurveSituation`
`.finrank_cohomologyOverField_zero_eq_eulerCharacteristic_sub` the count is
`χ(X, ω_X ⊗ ℒ) - χ(X, ω_X)`, which
`AlgebraicGeometry.CohenMacaulayCurveSituation`
`.eulerCharacteristic_tensorSheaf_dualizing_sub_eq_invertibleCurveDegree` evaluates as
`deg(ℒ)`.

The three terms of the sequence are taken as modules on `X` together with equations identifying
the first two with `ω_X` and with `ω_X ⊗ ℒ`; see the module documentation for why. -/
public theorem finrank_cohomologyOverField_zero_eq_invertibleCurveDegree
    {S : CohenMacaulayCurveSituation.{u}} (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (W F Q : S.X.Modules) [W.IsCoherent] [F.IsCoherent] [Q.IsCoherent]
    (i : W ⟶ F) (p : F ⟶ Q) (hzero : i ≫ p = 0)
    (hT : (ShortComplex.mk i p hzero).ShortExact)
    (hsupp : topologicalKrullDim (SheafOfModules.supp Q) ≤ 0)
    (hW : W = Stacks.Duality.dualizingSheafOverField S.f)
    (hF : F = (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
          (S.X.ringCatSheaf.property)⟩).obj
      ((Stacks.Duality.dualizingSheafOverField S.f))).obj (L)))
    (hinv : Subsingleton Γ(tensorPowerModule L (-1), (⊤ : S.X.Opens)))
    (hvan : IsZero (cohomologyOverField S.k S.f F 1)) :
    (Module.finrank S.k (cohomologyOverField S.k S.f Q 0) : ℤ) =
      invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L := by
  subst hW
  exact (finrank_cohomologyOverField_zero_eq_eulerCharacteristic_sub hT hsupp).trans
    (eulerCharacteristic_tensorSheaf_dualizing_sub_eq_invertibleCurveDegree L F hF hinv hvan)

/-- **`dim_k H⁰(X, coker α) = deg(ℒ)`** in Situation [Stacks, Tag 0B5D], for a monomorphism
`α : ω_X ⟶ ω_X ⊗ ℒ` with cokernel of zero-dimensional support, an invertible `ℒ` with
`H⁰(X, ℒ^{⊗ -1}) = 0` and `H¹(X, ω_X ⊗ ℒ) = 0`.

This is
`AlgebraicGeometry.CohenMacaulayCurveSituation`
`.finrank_cohomologyOverField_zero_eq_invertibleCurveDegree` at the short exact sequence a
monomorphism and its cokernel form (`CategoryTheory.ShortComplex.shortExact_mk_cokernel_π`). -/
public theorem finrank_cohomologyOverField_zero_cokernel_eq_invertibleCurveDegree
    {S : CohenMacaulayCurveSituation.{u}} (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    [(Stacks.Duality.dualizingSheafOverField S.f).IsCoherent] (F : S.X.Modules) [F.IsCoherent]
    (hF : F = (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
          (S.X.ringCatSheaf.property)⟩).obj
      ((Stacks.Duality.dualizingSheafOverField S.f))).obj (L)))
    (α : Stacks.Duality.dualizingSheafOverField S.f ⟶ F) [Mono α] [(cokernel α).IsCoherent]
    (hsupp : topologicalKrullDim (SheafOfModules.supp (cokernel α)) ≤ 0)
    (hinv : Subsingleton Γ(tensorPowerModule L (-1), (⊤ : S.X.Opens)))
    (hvan : IsZero (cohomologyOverField S.k S.f F 1)) :
    (Module.finrank S.k (cohomologyOverField S.k S.f (cokernel α) 0) : ℤ) =
      invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L :=
  finrank_cohomologyOverField_zero_eq_invertibleCurveDegree L _ F (cokernel α) α
    (cokernel.π α) (cokernel.condition α) (ShortComplex.shortExact_mk_cokernel_π α) hsupp rfl
    hF hinv hvan

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
