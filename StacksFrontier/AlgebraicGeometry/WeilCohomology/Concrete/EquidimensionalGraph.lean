module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphComposition

/-!
# Graphs and the diagonal between equidimensional schemes

Let `k` be a field and let `X`, `Y` be smooth separated schemes over `k` of constant relative
dimensions `d` and `e`. Then the correspondences of Section 0FFZ are
`Corrʳ(X, Y) = CH_{e-r}(X × Y) ⊗ ℚ` (`Stacks.WeilCohomology.corrEquivCorrespondence`). The graph
correspondence `[Γ_f] ∈ Corr⁰(X, Y)` of Stacks 0FG1 is defined block by block on the parts of
constant dimension, and so is the diagonal correspondence `[Δ_X]`, the identity of the category of
correspondences. This file shows that under this identification both become the classes of the
closed subschemes themselves:

* `[Γ_f]` is the class of the graph `(f, 𝟙) : Y ⟶ X ×_k Y`;
* `[Δ_X]` is the class of the diagonal `X ⟶ X ×_k X`.

## Main results

* `Stacks.WeilCohomology.corrEquivCorrespondence_graphCorr`: the graph correspondence is the
  class of the graph.
* `Stacks.WeilCohomology.corrEquivCorrespondence_diagonalCorr`: the diagonal correspondence is
  the class of the diagonal.

## References

* [Stacks Project, Tag 0FG1](https://stacks.math.columbia.edu/tag/0FG1)
* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY] {d e : ℕ}

attribute [local instance] isClosedImmersion_graphMorphism

omit [IsSeparated sY] in
/-- **The graph correspondence between equidimensional schemes is the class of the graph.** For
`X`, `Y` of constant relative dimensions `d`, `e` and `f : Y ⟶ X` over `k`, the identification
`Corr⁰(X, Y) = CH_e(X × Y) ⊗ ℚ` carries `[Γ_f]` to the class of `(f, 𝟙) : Y ⟶ X ×_k Y`. Only the
block `(d, e)` of `[Γ_f]` is nonzero, and on it `Γ_f ∩ (X_d × Y_e)` is the whole graph. -/
theorem corrEquivCorrespondence_graphCorr [QuasiCompact sY] (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (f : Y ⟶ X) (hf : f ≫ sX = sY) :
    corrEquivCorrespondence k sX sY hX hY 0 (graphCorr k sX sY f hf) =
      graphCorrespondence sX sY f hf e := by
  have := isIso_dimPart_self_ι sX hX
  have := isIso_dimPart_self_ι sY hY
  rw [graphCorr_eq_sum k sX sY f hf (D := {d}) (E := {e})
      (fun d' ⟨y, hy⟩ ↦ Finset.mem_singleton.2 (eq_of_mem_dimPart sX hX hy))
      (fun e' ⟨y, hy⟩ ↦ Finset.mem_singleton.2 (eq_of_mem_dimPart sY hY hy)),
    Finset.sum_singleton, Finset.sum_singleton, corrEquivCorrespondence_lof_lof, graphBlock,
    correspondenceEquivOfIso_tmul, graphCorrespondence]
  congr 1
  set U := ((dimPart sY e).ι ≫ f) ⁻¹ᵁ dimPart sX d with hU
  have hUtop : U = ⊤ := by
    rw [hU, dimPart_self_eq_top sX hX]; rfl
  have : IsIso U.ι := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [Scheme.Opens.opensRange_ι, hUtop]
  have hcomp : (asIso (U.ι ≫ (dimPart sY e).ι)).hom ≫ graphMorphism sX sY f hf =
      graphPiece k sX sY f hf d e ≫ prodHom sX sY (partBase sX d) (partBase sY e)
        (dimPart sX d).ι (dimPart sY e).ι rfl rfl := by
    apply Limits.pullback.hom_ext
    · rw [asIso_hom, Category.assoc, graphMorphism_fst]
      simp only [Category.assoc, Limits.pullback.lift_fst, graphPiece_fst_assoc]
      rw [morphismRestrict_ι]
    · rw [asIso_hom, Category.assoc, graphMorphism_snd, Category.comp_id]
      simp only [Category.assoc, Limits.pullback.lift_snd, graphPiece_snd_assoc]
      rfl
  have : IsClosedImmersion (graphPiece k sX sY f hf d e ≫ prodHom sX sY (partBase sX d)
      (partBase sY e) (dimPart sX d).ι (dimPart sY e).ι rfl rfl) := by
    rw [← hcomp]; infer_instance
  rw [chowPushforwardOfIso, ← QuotientAddGroup.mk'_apply, properChowPushforward_mk,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
    QuotientAddGroup.mk'_apply,
    cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ (asIso (U.ι ≫ (dimPart sY e).ι)) hcomp]

/-- **The diagonal correspondence of an equidimensional scheme is the class of the diagonal.**
For `X` of constant relative dimension `d`, the identification `Corr⁰(X, X) = CH_d(X × X) ⊗ ℚ`
carries `[Δ_X]`, the identity of the category of correspondences, to the class of the diagonal
`(𝟙, 𝟙) : X ⟶ X ×_k X`. -/
theorem corrEquivCorrespondence_diagonalCorr [QuasiCompact sX] (hX : RelativeDimension sX d) :
    corrEquivCorrespondence k sX sX hX hX 0 (diagonalCorr k sX) =
      graphCorrespondence sX sX (𝟙 X) (Category.id_comp sX) d := by
  rw [← graphCorr_id, corrEquivCorrespondence_graphCorr]

end Stacks.WeilCohomology

end
