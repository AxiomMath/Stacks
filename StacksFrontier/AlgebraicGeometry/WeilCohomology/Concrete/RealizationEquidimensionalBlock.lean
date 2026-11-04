module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.PartTransportCodim
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationFunctorTestClass
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The action of a correspondence between equidimensional schemes

Let `W` be data (D0)–(D3) satisfying (A), (B), (C), and let `X` and `Y` be nonempty and
equidimensional of dimensions `d` and `e`. A correspondence `c ∈ Corr⁰(X, Y)` lives on the single
block `(d, e)`, a class `α` on `X_d × Y_e`, and the action `a ↦ pr₂,*(γ(c) ∪ pr₁^*a)` of
Stacks 0FHL was defined through the parts `X_d ⊂ X`, `Y_e ⊂ Y`. This file shows that it is the
action `a ↦ pr₂,*(γ(c) ∪ pr₁^*a)` computed on `X × Y` itself, for the class of the transport of `α`
to `X × Y` (`Stacks.WeilCohomology.WeilData.corrMap_lof_lof_tmul`). This is the form in which the
proof of Stacks 0FHM compares it with the realization of `c`.

## References

* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow MonoidalCategory

universe u w

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {W : WeilData k F}
  (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)

/-- The part `part X d` of a nonempty equidimensional scheme `X` of dimension `d` is nonempty. -/
private theorem nonempty_part_of_isNonemptyEquidimensional
    {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ} (hX : IsNonemptyEquidimensional X d) :
    Nonempty (part X d).obj.left := by
  obtain ⟨x⟩ := hX.nonempty
  exact nonempty_part_iff.2 ⟨x, by rw [dimPart_self_eq_top _ hX.relativeDimension]; trivial⟩

/-- **The action of a correspondence between equidimensional schemes**: for `X`, `Y` nonempty and
equidimensional of dimensions `d`, `e` and the correspondence `q ⊗ α` on the block `(d, e)`, the
action `a ↦ pr₂,*(γ(c) ∪ pr₁^*a)` of Stacks 0FHL is `q` times the action on `X × Y` of the cycle
class of the transport of `α` to `X × Y`, read in codimension `d`. -/
theorem corrMap_lof_lof_tmul {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (n : ℤ) (q : ℚ)
    (α : chowGroup (fieldChowSituation k)
      (prodBase (partBase X.obj.hom d) (partBase Y.obj.hom e)) ((e : ℤ) - 0))
    (a : W.grade X n) :
    haveI := isIso_dimPart_self_ι X.obj.hom hX.relativeDimension
    haveI := isIso_dimPart_self_ι Y.obj.hom hY.relativeDimension
    (corrMap hA hB hC X Y 0 n (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α))) a :
        W.H Y) =
      (q : F) • (W.blockAct hA.perfectPairing hX hY (W.cycleClassRing (prod X Y) d
        (chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - 0) d
          (chowPushforwardOfIso (fieldChowSituation k)
            (prodBase (partBase X.obj.hom d) (partBase Y.obj.hom e))
            (prodBase X.obj.hom Y.obj.hom)
            (prodHom X.obj.hom Y.obj.hom (partBase X.obj.hom d) (partBase Y.obj.hom e)
              (dimPart X.obj.hom d).ι (dimPart Y.obj.hom e).ι rfl rfl)
            (prodHom_comp_prodBase _ _ _ _ _ _ _ _) ((e : ℤ) - 0) α))) n a : W.H Y) := by
  have := isIso_dimPart_self_ι X.obj.hom hX.relativeDimension
  have := isIso_dimPart_self_ι Y.obj.hom hY.relativeDimension
  set T := chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - 0) d
      (chowPushforwardOfIso (fieldChowSituation k)
        (prodBase (partBase X.obj.hom d) (partBase Y.obj.hom e)) (prodBase X.obj.hom Y.obj.hom)
        (prodHom X.obj.hom Y.obj.hom (partBase X.obj.hom d) (partBase Y.obj.hom e)
          (dimPart X.obj.hom d).ι (dimPart Y.obj.hom e).ι rfl rfl)
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) ((e : ℤ) - 0) α)
  have hXd := nonempty_part_of_isNonemptyEquidimensional hX
  have hYe := nonempty_part_of_isNonemptyEquidimensional hY
  have := isIso_partι_hom_left X hX.relativeDimension
  have := isIso_partι_hom_left Y hY.relativeDimension
  have hXd' := isNonemptyEquidimensional_part X hXd
  have hYe' := isNonemptyEquidimensional_part Y hYe
  have hcc : W.corrClass (part X d) (part Y e) e 0 d (blockEquiv X Y d e 0 (q ⊗ₜ[ℤ] α)) =
      (q : F) • W.pull (prodMap (partι X d) (partι Y e)) (W.cycleClassRing (prod X Y) d
        T) := by
    change (q : F) • W.cycleClassRing (prod (part X d) (part Y e)) d
      (chowGroupToCodimension (prod (part X d) (part Y e)).obj.hom ((e : ℤ) - 0) d α) = _
    congr 1
    have h₁ := cycleClassRing_codimensionGysin hC.pullback (partι X d ⊗ₘ partι Y e) d
      T
    exact (congrArg (W.cycleClassRing (prod (part X d) (part Y e)) d)
      (codimensionGysin_chowGroupToCodimension_partTransport hX.relativeDimension
        hY.relativeDimension ((e : ℤ) - 0) d α)).symm.trans h₁
  rw [corrMap_lof_lof, blockMap_of_nonempty hA hB hC n hXd hYe]
  simp only [LinearMap.comp_apply, coe_extendDeg]
  rw [hcc, blockAct_smul, LinearMap.smul_apply, SetLike.val_smul, map_smul,
    blockAct_pull_of_isIso hA hB hC (partι X d) (partι Y e) hX hXd' hY hYe', coe_pullDeg]
  congr 1
  have h : ∀ b : W.H Y, extendByZero hA hB hC (partι Y e) (W.pull (partι Y e) b) = b := fun b ↦ by
    have h' := sum_extendByZero_pull (hA := hA) (hB := hB) (hC := hC) ({e} : Finset ℕ)
      (fun e ↦ partι Y e) (fun y ↦ ⟨e, Finset.mem_singleton_self e, by
        rw [range_partι, dimPart_self_eq_top _ hY.relativeDimension]; trivial⟩)
      (fun s hs t ht hst ↦
        absurd ((Finset.mem_singleton.1 hs).trans (Finset.mem_singleton.1 ht).symm) hst) b
    rwa [Finset.sum_singleton] at h'
  exact h _

end Stacks.WeilCohomology.WeilData

end
