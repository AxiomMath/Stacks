module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchContainedChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchPreimageCycle
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowPrimeCycleTransverse
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DivisorComponentChernCap

/-!
# Tag 0F98, the case `W ⊆ D`: both sides reduced to the zero-section step

In the situation of [Stacks, Tag 0F97] let `W ⊆ Y` be an integral closed subscheme of
δ-dimension `k+1` contained in the divisor `D = Z(s)`. This file proves the case `W ⊆ D` of
[Stacks, Tag 0F98] up to its last sentence.

The source's computation is

  `i₁^*p^*[W] = i₁^*[p^{-1}W] = i₁^*([W₁] + [W₂]) = c₁(p₁^*ℒ₁) ∩ [W₁] + [W₁ ∩ W₂]_k`
  `           = p₁^*(c₁(ℒ₁) ∩ [W]) + [W₁ ∩ W₂]_k`

against

  `p₁^*i^*[W] = p₁^*(c₁(ℒ₁) ∩ [W]) + p₁^*(c₁(ℒ₂) ∩ [W])`,

and the last sentence identifies `[W₁ ∩ W₂]_k` with `p₁^*(c₁(ℒ₂) ∩ [W])`, since `W₁ ∩ W₂` is the
zero section of the line bundle `W₁ → W` (Lemma 42.32.4).

## Main results

* `leftRule_cycle_eq_add_of_le`: the left-hand side at cycle level,
  `i₁^*p^*[W] = c₁(p₁^*ℒ₁) ∩ [W₁] + [W₁ ∩ W₂]`, as an equality.
* `rightRule_cycle_sub_flatPullback_isRationallyEquivalentToZeroWithin_of_le`: the right-hand
  side, `p₁^*i^*[W]` against `p₁^*(c₁(ℒ₁|_D) ∩ [W|_D]) + p₁^*(c₁(ℒ₂|_D) ∩ [W|_D])`.
* `gysinRuleBranch₁_cycle_sub_flatPullback_isRationallyEquivalentToZeroWithin_of_le`: the first
  summands match, `c₁(p₁^*ℒ₁) ∩ [W₁]` against `p₁^*(c₁(ℒ₁|_D) ∩ [W|_D])`; this is the localized
  form of Stacks 02SS.

The two rational equivalences are witnessed inside the preimage of `W` in `D₁`. The δ-dimension
hypotheses on the branches are stated at `k+1+1`, the degree the Gysin rule of `i₁` asks of a
component.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.TensorZeroScheme

variable (C : Stacks.Chow.ChowSituation.{u}) (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (k : ℤ) (W : Y.IdealSheafData)

/-! ### The two presentations of the branch inside `D₁` -/

include h₁ h₂ in
/-- The restriction of `p^{-1}(W)` to `D₁` is the inverse image along `p₁` of the restriction of
`W` to `D`. -/
theorem comap_comap_proj_branch₁_eq :
    (W.comap R.normalize.p).comap R.normalize.D₁.subschemeι =
      (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).comap R.normalize.p₁ := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    R.normalize.comm₁]

/-! ### The left-hand side -/

include h₁ h₂ in
/-- **`i₁^*p^*[W] = c₁(p₁^*ℒ₁) ∩ [W₁] + [W₁ ∩ W₂]`**, at cycle level, for `W` an integral closed
subscheme of `Y` of δ-dimension `k+1` contained in `D`, where `W₁ = D₁ ⊔ p^{-1}(W)` and
`W₂ = D₂ ⊔ p^{-1}(W)` and `D₁` does not contain `W₂`. -/
theorem leftRule_cycle_eq_add_of_le (hWint : IsIntegral W.subscheme)
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    (hW₁int : IsIntegral (R.normalize.D₁ ⊔ W.comap R.normalize.p).subscheme)
    (hW₁dim : Stacks.Chow.schemeDeltaDimension C
      ((R.normalize.D₁ ⊔ W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY) =
        ((k + 1 + 1 : ℤ) : EInt))
    (hW₂int : IsIntegral (R.normalize.D₂ ⊔ W.comap R.normalize.p).subscheme)
    (hW₂dim : Stacks.Chow.schemeDeltaDimension C
      ((R.normalize.D₂ ⊔ W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY) =
        ((k + 1 + 1 : ℤ) : EInt))
    (hnle : ¬ R.normalize.D₁ ≤ R.normalize.D₂ ⊔ W.comap R.normalize.p) :
    (leftRule C Y L₁ L₂ s R sY k).cycle W hWint hDim =
      (gysinRuleBranch₁ C Y L₁ L₂ s R sY k).cycle
          (R.normalize.D₁ ⊔ W.comap R.normalize.p) hW₁int hW₁dim +
        Stacks.Chow.cycleAssociatedToClosedSubscheme C
          (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
          (((R.normalize.D₂ ⊔ W.comap R.normalize.p).comap
            R.normalize.D₁.subschemeι).subschemeι) (k + 1) := by
  let : AlgebraicGeometry.SheafOfModules.IsInvertible
      R.normalize.total.sheaf.obj
      R.normalize.total.ringCatSheaf.property
      ((Scheme.Modules.pullback R.normalize.p).obj L₁) :=
    Stacks.Divisors.pullback_isInvertible _ _
  have hflat : Stacks.Chow.flatPullback C (R.normalize.p ≫ sY) sY R.normalize.p rfl 1
        R.normalize.p_relativeDimension (k + 1)
        (Stacks.Chow.cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1)) =
      Stacks.Chow.cycleAssociatedToClosedSubscheme C (R.normalize.p ≫ sY)
        (W.comap R.normalize.p).subschemeι (k + 1 + 1) :=
    Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_comap_of_le C
      (R.normalize.p ≫ sY) sY R.normalize.p rfl 1 R.normalize.p_relativeDimension
      W (k + 1) (le_of_eq hDim)
  have hsplit := cycleAssociatedToClosedSubscheme_comap_proj_eq_add_of_le L₁ L₂ s R W C sY k hDim
    hW (k + 1 + 1) (by lia)
  show (gysinRuleBranch₁ C Y L₁ L₂ s R sY k).extendCycleGroup _ = _
  rw [hflat, hsplit, map_add,
    (gysinRuleBranch₁ C Y L₁ L₂ s R sY k).extendCycleGroup_cycleAssociatedToClosedSubscheme
      _ hW₁int hW₁dim,
    (gysinRuleBranch₁ C Y L₁ L₂ s R sY k).extendCycleGroup_cycleAssociatedToClosedSubscheme
      _ hW₂int hW₂dim]
  congr 1
  exact Stacks.Chow.gysinComponentCycle_of_not_le C (R.normalize.p ≫ sY) (k + 1)
    ((Scheme.Modules.pullback R.normalize.p).obj L₁) R.normalize.s₁
    (Stacks.Chow.firstChernComponentClass C (R.normalize.p ≫ sY) (k + 1)
      ((Scheme.Modules.pullback R.normalize.p).obj L₁))
    (R.normalize.D₂ ⊔ W.comap R.normalize.p) hW₂int hW₂dim hnle

/-! ### The right-hand side -/

include h₁ h₂ in
/-- **`p₁^*i^*[W]` against `p₁^*(c₁(ℒ₁|_D) ∩ [W|_D]) + p₁^*(c₁(ℒ₂|_D) ∩ [W|_D])`.** The two differ
by a cycle rationally equivalent to zero on `D₁` witnessed inside the preimage of `W`. -/
theorem rightRule_cycle_sub_flatPullback_isRationallyEquivalentToZeroWithin_of_le
    (hWint : IsIntegral W.subscheme)
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    (hWDint : IsIntegral (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subscheme)
    (hWDdim : Stacks.Chow.schemeDeltaDimension C
      ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι ≫
        (zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt)) :
    Stacks.Chow.IsRationallyEquivalentToZeroWithin C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
      ((rightRule C Y L₁ L₂ s R sY k).cycle W hWint hDim -
        (Stacks.Chow.flatPullback C (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
            ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
            (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
            ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
            (Stacks.Chow.firstChernComponentCycle C
              ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
              (Stacks.Chow.firstChernComponentCycleRule C
                ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
                ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₁))
              (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim) +
          Stacks.Chow.flatPullback C (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
            ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
            (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
            ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
            (Stacks.Chow.firstChernComponentCycle C
              ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
              (Stacks.Chow.firstChernComponentCycleRule C
                ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
                ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂))
              (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim)))
      ((R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y)) := by
  have h := Stacks.Chow.flatPullback_isRationallyEquivalentToZeroWithin C
    (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
    ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
    (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
    ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
    (gysinRuleZeroIdeal_cycle_sub_firstChernComponentCycle_isRationallyEquivalentToZeroWithin
      C Y L₁ L₂ s sY k W hW hWint hDim hWDint hWDdim)
  rw [map_sub, map_add] at h
  have hcyc : (rightRule C Y L₁ L₂ s R sY k).cycle W hWint hDim =
      Stacks.Chow.flatPullback C (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
        ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
        (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
        ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
        ((gysinRuleZeroIdeal C Y L₁ L₂ s sY k).cycle W hWint hDim) := by
    show Stacks.Chow.flatPullback C
        (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
        ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
        (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
        ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
        ((gysinRuleZeroIdeal C Y L₁ L₂ s sY k).extendCycleGroup _) = _
    rw [(gysinRuleZeroIdeal C Y L₁ L₂ s sY k).extendCycleGroup_cycleAssociatedToClosedSubscheme
      W hWint hDim]
  rw [hcyc]
  exact h.mono (le_of_eq (preimage_branch₁_proj Y L₁ L₂ s R (W.support : Set Y)).symm)

/-! ### The first summands match: the localized form of Stacks 02SS -/

include h₁ h₂ in
/-- **`c₁(p₁^*ℒ₁) ∩ [W₁]` against `p₁^*(c₁(ℒ₁|_D) ∩ [W|_D])`.** The Gysin cycle of the branch `W₁`
and the flat pullback along `p₁` of the component cycle of `ℒ₁|_D` at `W|_D` differ by a cycle
rationally equivalent to zero on `D₁` witnessed inside the preimage of `W`. -/
theorem gysinRuleBranch₁_cycle_sub_flatPullback_isRationallyEquivalentToZeroWithin_of_le
    (hW₁int : IsIntegral (R.normalize.D₁ ⊔ W.comap R.normalize.p).subscheme)
    (hW₁dim : Stacks.Chow.schemeDeltaDimension C
      ((R.normalize.D₁ ⊔ W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY) =
        ((k + 1 + 1 : ℤ) : EInt))
    (hWDint : IsIntegral (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subscheme)
    (hWDdim : Stacks.Chow.schemeDeltaDimension C
      ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι ≫
        (zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hVint : IsIntegral
      ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).comap R.normalize.p₁).subscheme)
    (hVdim : Stacks.Chow.schemeDeltaDimension C
      (((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).comap R.normalize.p₁).subschemeι ≫
        R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) = ((k + 1 + 1 : ℤ) : EInt)) :
    Stacks.Chow.IsRationallyEquivalentToZeroWithin C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
      ((gysinRuleBranch₁ C Y L₁ L₂ s R sY k).cycle
          (R.normalize.D₁ ⊔ W.comap R.normalize.p) hW₁int hW₁dim -
        Stacks.Chow.flatPullback C (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
          ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
          (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
          ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
          (Stacks.Chow.firstChernComponentCycle C ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
            (Stacks.Chow.firstChernComponentCycleRule C
              ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
              ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₁))
            (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim))
      ((R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y)) := by
  have hcar : R.normalize.p₁.base ⁻¹'
        ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).support :
          Set (zeroIdeal Y L₁ L₂ s).subscheme) =
      (R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y) := by
    rw [preimage_branch₁_proj, Scheme.IdealSheafData.support_comap,
      TopologicalSpace.Closeds.coe_preimage]
  have hA := gysinRuleBranch₁_cycle_sub_firstChernComponentCycle_isRationallyEquivalentToZeroWithin
    C Y L₁ L₂ s R sY k W hW₁int hW₁dim
    ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).comap R.normalize.p₁)
    (comap_comap_proj_branch₁_eq Y L₁ L₂ s R W) hVint hVdim
  have hB : Stacks.Chow.IsRationallyEquivalentToZeroWithin C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
      (Stacks.Chow.firstChernComponentCycle C
          (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
          (Stacks.Chow.firstChernComponentCycleRule C
            (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
            ((Scheme.Modules.pullback R.normalize.p₁).obj
              ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₁)))
          ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).comap R.normalize.p₁) hVint hVdim -
        Stacks.Chow.flatPullback C (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
          ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
          (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
          ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
          (Stacks.Chow.firstChernComponentCycle C ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
            (Stacks.Chow.firstChernComponentCycleRule C
              ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
              ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₁))
            (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim))
      ((R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y)) := by
    have h :=
      firstChernCapRule_extendCycleGroup_sub_flatPullback_isRationallyEquivalentToZeroWithin_of_base
      C ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁ 1
      ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
      ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₁)
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY)
      (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim
    have hE : (Stacks.Chow.firstChernCapRule C
          (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
          (Stacks.Chow.firstChernComponentCycleRule C
            (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
            ((Scheme.Modules.pullback R.normalize.p₁).obj
              ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj
                L₁)))).extendCycleGroup
          (Stacks.Chow.flatPullback C
            (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
            ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
            (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
            ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) (k + 1)
            (Stacks.Chow.cycleAssociatedToClosedSubscheme C
              ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)
              (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι (k + 1))) =
        Stacks.Chow.firstChernComponentCycle C
          (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
          (Stacks.Chow.firstChernComponentCycleRule C
            (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
            ((Scheme.Modules.pullback R.normalize.p₁).obj
              ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₁)))
          ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).comap R.normalize.p₁)
          hVint hVdim := by
      rw [Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_comap_of_le C
        (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
        ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
        (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
        ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize))
        (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) (k + 1)
        (le_of_eq hWDdim)]
      exact (Stacks.Chow.firstChernCapRule C
        (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
        (Stacks.Chow.firstChernComponentCycleRule C
          (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
          ((Scheme.Modules.pullback R.normalize.p₁).obj
            ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj
              L₁)))).extendCycleGroup_cycleAssociatedToClosedSubscheme _ hVint hVdim
    erw [hE] at h
    exact h.mono (le_of_eq hcar)
  have hsum := Stacks.Chow.isRationallyEquivalentToZeroWithin_add C
    (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1) hA hB
  convert hsum using 1
  abel

end Stacks.Chow.TensorZeroScheme

end
