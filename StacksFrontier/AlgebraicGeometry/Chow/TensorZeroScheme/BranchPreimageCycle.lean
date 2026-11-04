module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchComapCartier
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchCover
public import StacksFrontier.AlgebraicGeometry.Chow.UnionFundamentalCycle

/-!
# `[p^{-1}W] = [W₁] + [W₂]` over a closed subscheme of `D`

In the situation of [Stacks, Tag 0F97] let `W ⊆ Y` be an integral closed subscheme of
δ-dimension `k+1` contained in the divisor `D = Z(s)`, that is `zeroIdeal Y L₁ L₂ s ≤ W` in the
order on ideal sheaves. The case `W ⊆ D` of [Stacks, Tag 0F98] opens with

  "`p^{-1}(W) = W₁ ∪ W₂` (scheme theoretically) where `W_i = p_i^{-1}(W)` … Then
  `[p^{-1}(W)]_{k+1} = [W₁] + [W₂]` as `W_i` are integral closed subschemes of `L` of
  δ-dimension `k+1`."

This file proves that cycle identity. As ideal sheaves on `L` the two branches over `W` are
`W_i = D_i ⊔ p^{-1}(W)`; their scheme-theoretic union is `p^{-1}(W)`, and every point of their
intersection `(D₁ ∩ D₂) ∩ p^{-1}(W)` has relative dimension at most `k+1`, because `D₁ ∩ D₂ ⟶ D`
is an isomorphism by condition (6) of [Stacks, Tag 0F97].

## Main results

* `Stacks.Chow.TensorZeroScheme.inf_sup_comap_proj_of_le` — **`p^{-1}(W) = W₁ ∪ W₂` as closed
  subschemes of `L`**, for `W` a closed subscheme of `D`.
* `Stacks.Chow.TensorZeroScheme.relativeDimension_le_of_mem_support_sup_sup` — a point of
  `W₁ ∩ W₂` has relative dimension at most `k+1`.
* `Stacks.Chow.TensorZeroScheme.cycleAssociatedToClosedSubscheme_comap_proj_eq_add_of_le` —
  **`[p^{-1}W]_d = [W₁]_d + [W₂]_d` for every `d > k+1`**, which at `d = k+2` is the step of the
  proof of [Stacks, Tag 0F98] quoted above.

## References

* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.TensorZeroScheme


variable {Y : Scheme.{u}} (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)
  (W : Y.IdealSheafData)

/-! ### The two branches over `W`, as closed subschemes of `L` -/

include h₁ h₂ in
/-- **`p^{-1}(W) = W₁ ∪ W₂` as closed subschemes of `L`**, for `W` a closed subscheme of the
divisor `D = Z(s)`. The two branches over `W` are `W_i = D_i ∩ p^{-1}(W)`, which as ideal sheaves
on `L` are `D_i ⊔ p^{-1}(W)`; their scheme-theoretic union is their meet, and it is `p^{-1}(W)`. -/
theorem inf_sup_comap_proj_of_le (hW : zeroIdeal Y L₁ L₂ s ≤ W) :
    (R.normalize.D₁ ⊔ W.comap R.normalize.p) ⊓
        (R.normalize.D₂ ⊔ W.comap R.normalize.p) =
      W.comap R.normalize.p := by
  set Wp := W.comap R.normalize.p
  refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  have hbranches : R.normalize.D₁.comap Wp.subschemeι ⊓
      R.normalize.D₂.comap Wp.subschemeι = ⊥ := by
    rw [← comap_branch₁_decompositionComap L₁ L₂ s R W,
      ← comap_branch₂_decompositionComap L₁ L₂ s R W]
    exact Decomposition.inf_eq_bot_of_zeroIdeal_le L₁ L₂ s W hW (decompositionComap L₁ L₂ s R W)
  have hbot : (⊥ : Wp.subscheme.IdealSheafData).map Wp.subschemeι = Wp :=
    (Scheme.IdealSheafData.map_bot _).trans (Scheme.IdealSheafData.ker_subschemeι Wp)
  have hself : Wp.comap Wp.subschemeι = ⊥ :=
    le_bot_iff.1 (Scheme.IdealSheafData.le_map_iff_comap_le.1 hbot.ge)
  refine (Scheme.IdealSheafData.le_map_iff_comap_le.2 ?_).trans hbot.le
  calc ((R.normalize.D₁ ⊔ Wp) ⊓ (R.normalize.D₂ ⊔ Wp)).comap Wp.subschemeι
      ≤ (R.normalize.D₁ ⊔ Wp).comap Wp.subschemeι ⊓ (R.normalize.D₂ ⊔ Wp).comap Wp.subschemeι :=
        le_inf (Scheme.IdealSheafData.comap_mono _ inf_le_left)
          (Scheme.IdealSheafData.comap_mono _ inf_le_right)
    _ = ⊥ := by
        rw [Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.comap_sup, hself, sup_bot_eq,
          sup_bot_eq, hbranches]

/-! ### The δ-dimension of the intersection of the two branches -/

include h₁ h₂ in
/-- The intersection of the two branches over `W`, as an ideal sheaf on `L`: the scheme-theoretic
intersection `(D₁ ∩ D₂) ∩ p^{-1}(W)`. -/
theorem sup_sup_comap_proj_eq :
    (R.normalize.D₁ ⊔ W.comap R.normalize.p) ⊔
        (R.normalize.D₂ ⊔ W.comap R.normalize.p) =
      (R.normalize.D₁ ⊔ R.normalize.D₂) ⊔ W.comap R.normalize.p :=
  sup_sup_sup_comm _ _ _ _ |>.trans (by rw [sup_idem])

variable (C : Stacks.Chow.ChowSituation.{u}) (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (k : ℤ)

include h₁ h₂ in
/-- **A point of `W₁ ∩ W₂` has relative dimension at most `k+1`**, for `W` a closed subscheme of
`Y` of δ-dimension `k+1`; here `W₁ ∩ W₂` is the closed subscheme `(D₁ ∩ D₂) ∩ p^{-1}(W)` of `L`. -/
theorem relativeDimension_le_of_mem_support_sup_sup
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    {x : R.normalize.total}
    (hx : x ∈ (((R.normalize.D₁ ⊔ R.normalize.D₂) ⊔
      W.comap R.normalize.p).support : Set R.normalize.total)) :
    Stacks.Chow.relativeDimension C.dimensionFunction (R.normalize.p ≫ sY) x ≤ k + 1 := by
  rw [Scheme.IdealSheafData.support_sup, TopologicalSpace.Closeds.coe_inf,
    Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage] at hx
  obtain ⟨hxI, hxW⟩ := hx
  obtain ⟨z, rfl⟩ := (Scheme.IdealSheafData.range_subschemeι _).ge hxI
  obtain ⟨w, hw⟩ := (Scheme.IdealSheafData.range_subschemeι _).ge hxW
  have hbase : R.normalize.p.base ((R.normalize.D₁ ⊔ R.normalize.D₂).subschemeι.base z) =
      (zeroIdeal Y L₁ L₂ s).subschemeι.base ((R.normalize.intersectionProj).base z) := by
    simpa using congrArg (fun f : (R.normalize.D₁ ⊔ R.normalize.D₂).subscheme ⟶ Y ↦ f.base z)
      R.normalize.sup_subschemeι_comp_p
  have h₁ := Stacks.Chow.relativeDimension_comp_closedImmersion C.dimensionFunction
    (R.normalize.D₁ ⊔ R.normalize.D₂).subschemeι (R.normalize.p ≫ sY) z
  have h₂ := Stacks.Chow.relativeDimension_comp_closedImmersion C.dimensionFunction
    R.normalize.intersectionProj ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) z
  have h₃ := Stacks.Chow.relativeDimension_comp_closedImmersion C.dimensionFunction
    (zeroIdeal Y L₁ L₂ s).subschemeι sY (R.normalize.intersectionProj.base z)
  rw [← h₁, ← Category.assoc, R.normalize.sup_subschemeι_comp_p, Category.assoc, h₂, h₃, ← hbase,
    ← hw]
  exact Stacks.Chow.relativeDimension_le_of_schemeDeltaDimension_le C sY W.subschemeι
    (le_of_eq hDim) w

/-! ### The cycle identity -/

include h₁ h₂ in
/-- **`[p^{-1}W]_d = [W₁]_d + [W₂]_d`**, for `W` an integral closed subscheme of `Y` of
δ-dimension `k+1` contained in the divisor `D = Z(s)` and any degree `d > k+1`.

At `d = k+2` this is the step
"`p^{-1}(W) = W₁ ∪ W₂` (scheme theoretically) … then `[p^{-1}(W)]_{k+1} = [W₁] + [W₂]`"
of the case `W ⊆ D` of [Stacks, Tag 0F98]. -/
theorem cycleAssociatedToClosedSubscheme_comap_proj_eq_add_of_le
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hW : zeroIdeal Y L₁ L₂ s ≤ W) (d : ℤ) (hd : k + 1 < d) :
    Stacks.Chow.cycleAssociatedToClosedSubscheme C (R.normalize.p ≫ sY)
          (W.comap R.normalize.p).subschemeι d =
        Stacks.Chow.cycleAssociatedToClosedSubscheme C (R.normalize.p ≫ sY)
            (R.normalize.D₁ ⊔ W.comap R.normalize.p).subschemeι d +
          Stacks.Chow.cycleAssociatedToClosedSubscheme C (R.normalize.p ≫ sY)
            (R.normalize.D₂ ⊔ W.comap R.normalize.p).subschemeι d := by
  have hdim : ∀ x ∈ (((R.normalize.D₁ ⊔ W.comap R.normalize.p) ⊔
      (R.normalize.D₂ ⊔ W.comap R.normalize.p)).support :
        Set R.normalize.total),
      Stacks.Chow.relativeDimension C.dimensionFunction (R.normalize.p ≫ sY) x ≠ d := by
    intro x hx hcon
    rw [sup_sup_comap_proj_eq L₁ L₂ s R W] at hx
    have hle := relativeDimension_le_of_mem_support_sup_sup L₁ L₂ s R W C sY k hDim hx
    lia
  have hsplit := Stacks.Chow.cycleAssociatedToClosedSubscheme_inf C (R.normalize.p ≫ sY)
    (R.normalize.D₁ ⊔ W.comap R.normalize.p)
    (R.normalize.D₂ ⊔ W.comap R.normalize.p) d hdim
  rwa [inf_sup_comap_proj_of_le L₁ L₂ s R W hW] at hsplit

end Stacks.Chow.TensorZeroScheme

end
