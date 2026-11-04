module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreLineRegular
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedModificationComparison
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationChernQ
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionStructureSheaf

/-!
# Stacks 0FEG and 0FEH: the localized Chern classes of the structure sheaf of a regular immersion

Let `i : Z ⟶ X` be a regular closed immersion of codimension `r ≥ 1` of schemes locally of finite
type over the base of chapter 42, with `X` quasi-compact or with quasi-compact irreducible
components, and let `𝒩 = 𝒞_{Z/X}^∨` be its normal sheaf. Then

  `c_t(Z ⟶ X, i_*𝒪_Z) = 0` for `t = 1, …, r - 1`  and
  `c_r(Z ⟶ X, i_*𝒪_Z) = (-1)^{r-1}(r-1)! c(Z ⟶ X, 𝒩)`  in `A^r(Z ⟶ X)`.

## The proof

Let `b : W ⟶ 𝐏¹_X` be the blowup in `∞(Z)` (Stacks 0FBG), `i' : 𝐏¹_Z ⟶ W` the closed immersion of
Stacks 0FE9 and `Q = i'_*𝒪_{𝐏¹_Z}`, with `T = X'` the strict transform in `W_∞`.

* `i'` is a regular immersion of codimension `r`
  (`Stacks.Chow.isRegularClosedImmersionOfCodim_lineToBlowupAtInfinity`), so `Q` is perfect with
  defined Chern classes; `Q|_{b⁻¹(𝐀¹_X)}` is the pullback of `i_*𝒪_Z`
  (`Stacks.Chow.derivedPullbackAffineChartLineIso`), `Q|_{X'}` is zero and `X'` contains every
  point of `W_∞` over `X ∖ Z`
  (`Stacks.Chow.isZero_derivedPullback_strictTransform_lineToBlowupAtInfinity`,
  `Stacks.Chow.mem_range_strictTransformToFibreAtInfinity`). So Stacks 0FE8
  (`Stacks.Chow.LocalizedSituation.modificationChernClass_eq_localizedChern`) gives
  `c_t(Z ⟶ X, i_*𝒪_Z) = c'_t(Q)`, the class of Stacks 0F9K.
* `c'_t(Q) = 0` for `0 < t < r` and `c'_r(Q) = (-1)^{r-1}(r-1)! c(Z ⟶ X, 𝒩)`: `Q|_E` is the
  pushforward of `𝒪_Z` along the zero section of the exceptional divisor `E ≅ 𝐏(𝒞_{Z/X} ⊕ 𝒪_Z)`,
  and Stacks 0FEF applies to `E ⟶ Z`
  (`Stacks.Chow.modificationChernClass_lineToBlowupAtInfinity_eq_zero`,
  `Stacks.Chow.modificationChernClass_lineToBlowupAtInfinity_eq_regularNormalGysinClass`).

## Main results

* `Stacks.Chow.isRegularImmersionChernFormula_regularImmersionStructureSheafSituation` —
  **Stacks 0FEG**.
* `Stacks.Chow.isRegularImmersionChernFormula_of_compactSpace` — the case of a quasi-compact `X`.
* `Stacks.Chow.regularImmersionStructureSheafSituation_capFundamentalClass` — **Stacks 0FEH**:
  parts (1)–(4), from Lemma 0FEG and Stacks 0FBM, 0FBA
  (`Stacks.Chow.LocalizedSituation.capFundamentalClass_of_isRegularImmersionChernFormula`).
  The source's `dim_δ(X) = n` enters only as `dim_δ(X) ≤ n`.

## References

* [Stacks Project, Tag 0FEG](https://stacks.math.columbia.edu/tag/0FEG)
* [Stacks Project, Tag 0FEH](https://stacks.math.columbia.edu/tag/0FEH)
* [Stacks Project, Tag 0FE8](https://stacks.math.columbia.edu/tag/0FE8)
* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open scoped TensorProduct

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i] {r : ℕ} (hreg : IsRegularClosedImmersionOfCodim i r)
  (hX : CompactSpace X ∨ ∀ T ∈ irreducibleComponents X, IsCompact T)

/-- **`c_t(Z ⟶ X, i_*𝒪_Z) = c'_t(Q)`**: for `t ≥ 1` the localized Chern class of `i_*𝒪_Z` is the
class of Stacks 0F9K of `Q = i'_*𝒪_{𝐏¹_Z}` on the blowup at infinity, with `T = X'`, by
Stacks 0FE8. -/
theorem localizedChernClassOfIsZero_regularImmersionStructureSheafSituation {t : ℕ}
    (ht : 0 < t) :
    LocalizedSituation.localizedChernClassOfIsZero
        (isZeroOnComplement_regularImmersionStructureSheafSituation C sX i hreg hX 0) ht =
      modificationChernClass C sX (blowupAtInfinityToProjectiveLineProduct i.ker sX)
        (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX) i
        (strictTransformToFibreAtInfinity sX i)
        (hasDefinedChernClasses_pushforward_lineToBlowupAtInfinity C sX i hreg hX) t
        (mem_range_strictTransformToFibreAtInfinity sX i)
        (exists_isFiniteLocallyFreeOfRankLT_of_isZero _
          (isZero_derivedPullback_strictTransform_lineToBlowupAtInfinity sX i) ht) := by
  have := perfect_of_isRegularImmersion i hreg.isRegularImmersion
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  rw [← localizedChern_pushforwardStructureSheafSituation C sX i hX ht]
  exact (LocalizedSituation.modificationChernClass_eq_localizedChern
    (pushforwardStructureSheafSituation C sX i hX t)
    (blowupAtInfinityToProjectiveLineProduct i.ker sX)
    (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX)
    (strictTransformToFibreAtInfinity sX i)
    (isPerfect_pushforward_lineToBlowupAtInfinity i hreg)
    (localizedChernFiniteness_blowupAtInfinity C sX i hX _)
    ⟨derivedPullbackAffineChartLineIso sX i⟩
    (mem_range_strictTransformToFibreAtInfinity sX i) _
    (isFiniteLocallyFreeOfRankLTOnComplement_pushforwardStructureSheafSituation C sX i hX ht)).symm

/-- Let `i : Z ⟶ X` be a regular closed immersion of codimension `r ≥ 1` of schemes locally of
finite type over the base of chapter 42, with `X` quasi-compact or with quasi-compact irreducible
components, and `𝒩 = 𝒞_{Z/X}^∨` its normal sheaf. Then `c_t(Z ⟶ X, i_*𝒪_Z) = 0` for
`t = 1, …, r - 1` and `c_r(Z ⟶ X, i_*𝒪_Z) = (-1)^{r-1}(r-1)! c(Z ⟶ X, 𝒩)` in `A^r(Z ⟶ X)`, the
localized Chern classes being those of Definition 0FB5
(`Stacks.Chow.LocalizedSituation.IsRegularImmersionChernFormula` for the situation
`Stacks.Chow.regularImmersionStructureSheafSituation` of `i_*𝒪_Z`). The codimension is positive, as
the factor `(r-1)!` of the source presupposes. -/
@[stacks 0FEG "the whole lemma: c_t(Z → X, i_*O_Z) = 0 for 0 < t < r and \
c_r(Z → X, i_*O_Z) = (-1)^{r-1}(r-1)! c(Z → X, N), for X quasi-compact or with quasi-compact \
irreducible components and r ≥ 1 (presupposed by (r-1)!)"]
theorem isRegularImmersionChernFormula_regularImmersionStructureSheafSituation (hr : 0 < r) :
    (regularImmersionStructureSheafSituation C sX i hreg hX 0).IsRegularImmersionChernFormula
      (isZeroOnComplement_regularImmersionStructureSheafSituation C sX i hreg hX 0) hreg hr := by
  refine ⟨fun t ht htr => ?_, ?_⟩
  · rw [localizedChernClassOfIsZero_regularImmersionStructureSheafSituation C sX i hreg hX ht]
    exact modificationChernClass_lineToBlowupAtInfinity_eq_zero C sX i hreg _ t ht htr _ _
  · rw [localizedChernClassOfIsZero_regularImmersionStructureSheafSituation C sX i hreg hX hr]
    exact modificationChernClass_lineToBlowupAtInfinity_eq_regularNormalGysinClass C sX i hreg
      (by omega) _ _

/-- **Stacks 0FEG for a quasi-compact `X`**: for every regular closed immersion `i : Z ⟶ Y` of
codimension `r ≥ 1` into a quasi-compact scheme `Y` locally of finite type over the base, the
conclusion of Lemma 0FEG holds for `i_*𝒪_Z`. -/
theorem isRegularImmersionChernFormula_of_compactSpace :
    ∀ {Z Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [CompactSpace Y] (i : Z ⟶ Y)
      [IsClosedImmersion i] {r : ℕ} (hreg : IsRegularClosedImmersionOfCodim i r) (hr : 0 < r),
      (regularImmersionStructureSheafSituation C sY i hreg (Or.inl ‹_›)
          0).IsRegularImmersionChernFormula
        (isZeroOnComplement_regularImmersionStructureSheafSituation C sY i hreg (Or.inl ‹_›) 0)
        hreg hr :=
  fun sY _ _ i _ _ hreg hr =>
    isRegularImmersionChernFormula_regularImmersionStructureSheafSituation C sY i hreg _ hr

/-- Let `i : Z ⟶ X` be a regular closed immersion of codimension `r ≥ 1` of schemes locally of
finite type over the base, `X` quasi-compact or with quasi-compact irreducible components, and
`dim_δ(X) ≤ n` (the source's `dim_δ(X) = n`). Then

1. `c_t(Z ⟶ X, i_*𝒪_Z) ∩ [X]_n = 0` for `1 ≤ t < r`,
2. `c_r(Z ⟶ X, i_*𝒪_Z) ∩ [X]_n = (-1)^{r-1}(r-1)! [Z]_{n-r}`,
3. `ch_t(Z ⟶ X, i_*𝒪_Z) ∩ [X]_n = 0` for `0 ≤ t < r`, and
4. `ch_r(Z ⟶ X, i_*𝒪_Z) ∩ [X]_n = [Z]_{n-r}`,

with `c_t(Z ⟶ X, i_*𝒪_Z)` the class of Stacks 0FB2 for the situation in degree `t`. -/
@[stacks 0FEH "all four parts, for X quasi-compact or with quasi-compact irreducible components, \
r ≥ 1 and dim_δ(X) ≤ n (the source's dim_δ(X) = n)"]
theorem regularImmersionStructureSheafSituation_capFundamentalClass (hr : 0 < r) (n : ℤ)
    (hXn : schemeDeltaDimension C sX ≤ (n : EInt)) :
    (∀ (t : ℕ) (ht : 0 < t), t < r →
      capFundamentalClassAt C (gysinSystemOfInvertible C) (i ≫ sX) sX i rfl t n
        ((regularImmersionStructureSheafSituation C sX i hreg hX t).localizedChern
          (isFiniteLocallyFreeOfRankLTOnComplement_regularImmersionStructureSheafSituation C sX
            i hreg hX ht)) = 0) ∧
    capFundamentalClassAt C (gysinSystemOfInvertible C) (i ≫ sX) sX i rfl r n
        ((regularImmersionStructureSheafSituation C sX i hreg hX r).localizedChern
          (isFiniteLocallyFreeOfRankLTOnComplement_regularImmersionStructureSheafSituation C sX
            i hreg hX hr)) =
      ((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) • fundamentalChowClass C (i ≫ sX) (n - r) ∧
    (∀ t : ℕ, t < r →
      (capFundamentalClassAt C (gysinSystemOfInvertible C) (i ≫ sX) sX i rfl t
          n).toIntLinearMap.lTensor ℚ
        ((regularImmersionStructureSheafSituation C sX i hreg hX 0).localizedChernChar
          (isZeroOnComplement_regularImmersionStructureSheafSituation C sX i hreg hX 0) t) = 0) ∧
    (capFundamentalClassAt C (gysinSystemOfInvertible C) (i ≫ sX) sX i rfl r
        n).toIntLinearMap.lTensor ℚ
        ((regularImmersionStructureSheafSituation C sX i hreg hX 0).localizedChernChar
          (isZeroOnComplement_regularImmersionStructureSheafSituation C sX i hreg hX 0) r) =
      (1 : ℚ) ⊗ₜ[ℤ] fundamentalChowClass C (i ≫ sX) (n - r) :=
  LocalizedSituation.capFundamentalClass_of_isRegularImmersionChernFormula
    (regularImmersionStructureSheafSituation C sX i hreg hX 0)
    (isZeroOnComplement_regularImmersionStructureSheafSituation C sX i hreg hX 0) hreg hr
    (isRegularImmersionChernFormula_regularImmersionStructureSheafSituation C sX i hreg hX hr) n hXn

end Stacks.Chow

end
