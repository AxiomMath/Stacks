module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingConverse
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingDvr
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingForward
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingInverse
public import StacksCore.Tactic.StacksAttribute

/-!
# Weightings and relative zero-cycles

Let `S` be a locally Noetherian scheme and let `f : X ⟶ S` be a locally quasi-finite morphism of
schemes. The three clauses of Stacks Tag 0H5P:

* the function `w_α` attached to a relative `0`-cycle `α ∈ z(X/S, 0)` is a weighting of `f`;
* if `X` is quasi-compact, then for every weighting `w` of `f` there is an integer `n > 0` with
  `n·w = w_α` for some `α ∈ z(X/S, 0)`;
* if moreover `S` is a scheme over `𝔽_p`, the integer `n` may be taken to be a power of `p`.

## Main results

* `Stacks.Chow.isWeighting_relativeCycleWeight` — clause (1).
* `Stacks.Chow.exists_relativeCycle_nsmul_eq_relativeCycleWeight` — clause (2).
* `Stacks.Chow.exists_relativeCycle_primePow_nsmul_eq_relativeCycleWeight` — clause (3).

## Implementation notes

`α ∈ z(X/S, 0)` is membership in the subgroup `Stacks.Chow.relativeCycles f 0`, so the three
statements quantify over that subgroup exactly as the source does. Being a scheme over `𝔽_p` is a
morphism to the spectrum of a universe-lifted `ZMod p`; the only use made of it is that every
residue field of `S` then has exponential characteristic `p`.

Clause (1) does not assume `X` quasi-compact: the weighting condition is checked on a finite open
piece of a base change to the spectrum of a discrete valuation ring, and such a piece is
quasi-compact even when `X` is not.

## References

* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyQuasiFinite f]

/-- **Stacks Project, Tag 0H5P**, clause (1). Let `S` be a locally Noetherian scheme and let
`f : X ⟶ S` be a locally quasi-finite morphism of schemes. For `α ∈ z(X/S, 0)` the map
`w_α : X → ℤ` is a weighting of `f`. -/
@[stacks 0H5P "clause (1): the map attached to a relative zero-cycle is a weighting"]
theorem isWeighting_relativeCycleWeight (α : relativeCycles f 0) :
    IsWeighting f (relativeCycleWeight f α.1) := by
  refine isWeighting_relativeCycleWeight_of_dvr_case f α.1
    ((mem_relativeCycles f 0 α.1).1 α.2) (fun R _ _ _ c ↦ ?_) (fun R _ _ _ W p _ _ _ γ hγ ↦ ?_)
  · exact relativeCycleWeight_baseChangeFamily f c α.1
  · exact isWeighting_relativeCycleWeight_of_isDiscreteValuationRing p γ hγ

/-- A family of cycles whose weight is `n·w` for a weighting `w` is a relative zero-cycle. -/
private theorem exists_relativeCycle_of_weight_eq_nsmul [CompactSpace X] (w : X → ℤ)
    (hw : IsWeighting f w) (n : ℕ)
    (c : FamilyOfCycles f 0) (hc : ∀ x, relativeCycleWeight f c x = n * w x) :
    ∃ α : relativeCycles f 0, ∀ x, (n : ℤ) * w x = relativeCycleWeight f α.1 x :=
  ⟨⟨c, (mem_relativeCycles f 0 _).2 (isRelativeCycle_of_relativeCycleWeight_eq_nsmul f w hw n c hc
    (fun _ _ _ _ d ↦ relativeCycleWeight_baseChangeFamily f d _) fun _ _ _ _ d γ hγ ↦
      isWeighting_relativeCycleWeight_of_isDiscreteValuationRing (pullback.snd f d) γ hγ)⟩,
    fun x ↦ (hc x).symm⟩

/-- **Stacks Project, Tag 0H5P**, clause (2). Let `S` be a locally Noetherian scheme, let
`f : X ⟶ S` be a locally quasi-finite morphism of schemes and let `X` be quasi-compact. Given a
weighting `w : X → ℤ` of `f` there is an integer `n > 0` with `n·w = w_α` for some
`α ∈ z(X/S, 0)`. -/
@[stacks 0H5P "clause (2): every weighting is a positive integer multiple of one attached to a \
relative zero-cycle, for a quasi-compact source"]
theorem exists_relativeCycle_nsmul_eq_relativeCycleWeight [CompactSpace X] (w : X → ℤ)
    (hw : IsWeighting f w) :
    ∃ (n : ℕ) (α : relativeCycles f 0), 0 < n ∧
      ∀ x : X, (n : ℤ) * w x = relativeCycleWeight f α.1 x := by
  obtain ⟨n, hnpos, hfin, hdvd⟩ := AlgebraicGeometry.exists_pos_forall_finInsepDegree_dvd f
  obtain ⟨α, hα⟩ := exists_relativeCycle_of_weight_eq_nsmul f w hw n _
    (relativeCycleWeight_cycleOfWeighting f w n hfin hdvd)
  exact ⟨n, α, hnpos, hα⟩

/-- **Stacks Project, Tag 0H5P**, clause (3). In the situation of clause (2), if `S` is a scheme
over `𝔽_p` for a prime `p`, then the integer `n` may be chosen to be a power of `p`. -/
@[stacks 0H5P "clause (3): over a scheme of characteristic p the multiple may be taken to be a \
power of p"]
theorem exists_relativeCycle_primePow_nsmul_eq_relativeCycleWeight [CompactSpace X] (p : ℕ)
    [Fact p.Prime] (σ : S ⟶ Spec (CommRingCat.of (ULift.{u} (ZMod p)))) (w : X → ℤ)
    (hw : IsWeighting f w) :
    ∃ (e : ℕ) (α : relativeCycles f 0), 0 < p ^ e ∧
      ∀ x : X, ((p ^ e : ℕ) : ℤ) * w x = relativeCycleWeight f α.1 x := by
  obtain ⟨e, hfin, hdvd⟩ := AlgebraicGeometry.exists_primePow_forall_finInsepDegree_dvd f p
    (AlgebraicGeometry.expChar_residueField_of_over_zmod p σ)
  obtain ⟨α, hα⟩ := exists_relativeCycle_of_weight_eq_nsmul f w hw (p ^ e) _
    (relativeCycleWeight_cycleOfWeighting f w (p ^ e) hfin hdvd)
  exact ⟨e, α, pow_pos (Fact.out : p.Prime).pos e, hα⟩

end Stacks.Chow

end
