module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsCoefficientProjection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.BaseChangeOverFieldTheorem
import StacksCore.Tactic.StacksAttribute

/-!
# The tensor base change isomorphism over a field

Let `K` be a field and `n ≥ 1` an integer invertible in `K`. Consider a commutative diagram
```
X <-p-- X' <-h-- Y
|       |f'      |e
v       v        v
Spec K <- S' <-g- T
```
of schemes with `X' = X ×_{Spec K} S'`, `Y = X' ×_{S'} T` and `g` quasi-compact and
quasi-separated. [Stacks, Tag 0F1J] asserts that the canonical map

`p⁻¹E ⊗^L_{ℤ/nℤ} (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹p⁻¹E ⊗^L_{ℤ/nℤ} e⁻¹F)`

is an isomorphism for `E ∈ D⁺(X_étale, ℤ/nℤ)` of Tor amplitude in `[a, ∞]` and
`F ∈ D⁺(T_étale, ℤ/nℤ)`.

The source's proof reduces this to [Stacks, Tag 0F1I], applied to `X` and to the schemes finite
over the affine opens of `X`, which is possible because `X` over `K` is arbitrary in
Tag 0F1I. The reduction is `isIso_tensorBaseChangeMap_zmod_of_derivedBaseChangeHolds` in
the namespace `Stacks.EtaleCohomology.EtaleCoefficients`, and Tag 0F1I for sheaves annihilated by
`n` is `Stacks.EtaleCohomology.BaseChangeOverField.derivedBaseChangeHolds_of_isUnit`.

## Main results

* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_of_isUnit` —
  [Stacks, Tag 0F1J].

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 0F1I](https://stacks.math.columbia.edu/tag/0F1I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- forced by `Stacks.EtaleCohomology.EtaleCoefficients.
-- isIso_tensorBaseChangeMap_zmod_of_derivedBaseChangeHolds`
-- (Kunneth/EtaleCoefficientsCoefficientProjection.lean:518), stated for the standard model of the
-- derived category, through `derivedPullback`.
attribute [local instance] HasDerivedCategory.standard

-- The imports bring `SheafOfModules.hasDerivedCategory`
-- (`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean:155`), the locally small model, which
-- would otherwise be found before `HasDerivedCategory.standard`.

open Stacks.EtaleCohomology.BaseChangeOverField in
/-- **[Stacks, Tag 0F1J].** Let `K` be a field and `n ≥ 1` an integer invertible in `K`. Consider
a commutative diagram
```
X <-p-- X' <-h-- Y
|       |f'      |e
v       v        v
Spec K <- S' <-g- T
```
of schemes with `X' = X ×_{Spec K} S'` and `Y = X' ×_{S'} T` and `g` quasi-compact and
quasi-separated. The canonical map

`p⁻¹E ⊗^L_{ℤ/nℤ} (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹p⁻¹E ⊗^L_{ℤ/nℤ} e⁻¹F)`

is an isomorphism if `E ∈ D⁺(X_étale, ℤ/nℤ)` has Tor amplitude in `[a, ∞]` for some `a ∈ ℤ` and
`F ∈ D⁺(T_étale, ℤ/nℤ)`.

This is `isIso_tensorBaseChangeMap_zmod_of_derivedBaseChangeHolds`, with derived base change over
`X` and over the schemes finite over the affine opens of `X` given by [Stacks, Tag 0F1I]
(`derivedBaseChangeHolds_of_isUnit`: `X` over `K` is arbitrary there). The lower bound on `E`
(`_hE`, `E ∈ D⁺`) is part of the source's statement; the proof does not need it. -/
@[stacks 0F1J]
theorem isIso_tensorBaseChangeMap_of_isUnit (K : Type u) [Field K] (n : ℕ) [NeZero n]
    (hn : IsUnit (n : K)) {X X' Y S' T : Scheme.{u}} (πX : X ⟶ Spec (.of K))
    (πS : S' ⟶ Spec (.of K)) (p : X' ⟶ X) (f' : X' ⟶ S') (hX' : IsPullback p f' πX πS)
    (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (hY : IsPullback h e f' g) [QuasiCompact g]
    [QuasiSeparated g] (E : DerivedModules (ULift.{u + 1} (ZMod n)) X) (_hE : ∃ b : ℤ, E.IsGE b)
    (a : ℤ) (hEa : HasTorAmplitudeGE (ULift.{u + 1} (ZMod n)) E a)
    (F : DerivedModules (ULift.{u + 1} (ZMod n)) T) (hF : ∃ b : ℤ, F.IsGE b) :
    IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f' g h e hY.w
      ((pullback (ULift.{u + 1} (ZMod n)) p).obj E) F) := by
  have hn' : IsUnit (((n : ℤ) : K)) := by exact_mod_cast hn
  obtain ⟨b, hFb⟩ := hF
  exact isIso_tensorBaseChangeMap_zmod_of_derivedBaseChangeHolds πX πS p f' hX' g h e hY n
    (derivedBaseChangeHolds_of_isUnit K n hn' πX)
    (fun ιU _ _ π _ => derivedBaseChangeHolds_of_isUnit K n hn' (π ≫ ιU ≫ πX)) E a hEa F b hFb

end Stacks.EtaleCohomology.EtaleCoefficients

end
