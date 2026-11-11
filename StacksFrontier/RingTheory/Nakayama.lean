module

public import Mathlib.RingTheory.Nakayama
public import StacksCore.Tactic.StacksAttribute

/-!
# Nakayama's lemma: generators lift (Stacks 00DV (8))

If `M` is a finite `R`-module, `I ≤ jacobson ⊥`, and elements of `M` generate `M ⧸ I • ⊤`, then
those same elements generate `M`. This is the Jacobson counterpart of part (12),
`Submodule.span_eq_top_of_span_image_mkQ_eq_top_of_isNilpotent`, and follows from part (4),
`Submodule.le_of_le_smul_of_le_jacobson_bot`, at `N := span R s`, `N' := ⊤`.

## Main results

* `Submodule.span_eq_top_of_span_image_mkQ_eq_top_of_le_jacobson_bot`: a set `s ⊆ M` whose image
  spans `M ⧸ I • ⊤` spans `M`.
* `Submodule.span_range_eq_top_of_span_range_mkQ_eq_top_of_le_jacobson_bot`: the same for a finite
  family `x : Fin n → M`, the tag's literal `x₁, …, xₙ`.

## References

* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Stacks 00DV (8)**: if `M` is finite, `I ≤ rad(R)`, and the image of `s` spans `M ⧸ I • ⊤`,
then `s` spans `M`.

The hypothesis "`s` generates `M/IM`" is taken literally, as `s` spanning the quotient
`M ⧸ I • ⊤`. Finiteness of `s` is not used, so `s` is an arbitrary set; the tag's
`x₁, …, xₙ` is `s := Set.range x`, see
`Submodule.span_range_eq_top_of_span_range_mkQ_eq_top_of_le_jacobson_bot`. -/
@[stacks 00DV "(8): elements of a finite module `M` generating `M/IM`, with `I ⊆ rad(R)`,
  generate `M`; stated for an arbitrary set `s`."]
theorem Submodule.span_eq_top_of_span_image_mkQ_eq_top_of_le_jacobson_bot
    [Module.Finite R M] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) (s : Set M)
    (hs : Submodule.span R
      (Submodule.Quotient.mk '' s : Set (M ⧸ I • (⊤ : Submodule R M))) = ⊤) :
    Submodule.span R s = ⊤ := by
  have hs' : Submodule.span R s ⊔ I • ⊤ = ⊤ := by
    rwa [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span]
  exact eq_top_iff.2 <|
    Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp ‹_›) hI hs'.ge

/-- **Stacks 00DV (8)**, for a finite family: if `M` is finite, `I ≤ rad(R)`, and the images of
`x₁, …, xₙ` generate `M ⧸ I • ⊤`, then `x₁, …, xₙ` generate `M`. -/
@[stacks 00DV "(8): the tag's literal form, for a family `x : Fin n → M`."]
theorem Submodule.span_range_eq_top_of_span_range_mkQ_eq_top_of_le_jacobson_bot
    [Module.Finite R M] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) {n : ℕ} (x : Fin n → M)
    (hx : Submodule.span R
      (Set.range fun i ↦ (Submodule.Quotient.mk (x i) : M ⧸ I • (⊤ : Submodule R M))) = ⊤) :
    Submodule.span R (Set.range x) = ⊤ :=
  Submodule.span_eq_top_of_span_image_mkQ_eq_top_of_le_jacobson_bot I hI _ <| by
    rwa [← Set.range_comp]
