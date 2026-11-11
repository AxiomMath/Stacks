module

public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.CompleteLocalRing.MinimalRegularPresentation
public import StacksFrontier.RingTheory.MvPowerSeries.KrullDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# Power series rings over a field or a Cohen ring, and quotients of regular local rings

This file collects the consequences of the Cohen structure theorem recorded in Stacks 032C
(Remark 10.160.9).

## Main results

* `MvPowerSeries.isRegularLocalRing_and_ringKrullDim_of_field`: `k[[X_1, …, X_d]]` over a field
  `k` is a Noetherian complete local regular ring of dimension `d`.
* `MvPowerSeries.isRegularLocalRing_and_ringKrullDim_of_isCohenRing`: `Λ[[X_1, …, X_d]]` over a
  Cohen ring `Λ` is a Noetherian complete local regular ring of dimension `d + 1`.
* `IsLocalRing.exists_isRegularLocalRing_surjective`: a Noetherian complete local ring is a
  quotient of a regular local ring.
* `cohen_structure_consequences`: the four assertions of Stacks 032C together, the last one being
  that a Noetherian complete local ring is universally catenary
  (`isUniversallyCatenary_of_isPrecomplete_maximalIdeal`).

## Implementation notes

The Krull dimension is `ringKrullDim_fin_eq_add`, the dimension of a power series ring over a
Noetherian local ring, together with `ringKrullDim_eq_zero_of_field` and
`IsDiscreteValuationRing.ringKrullDim_eq_one` (a Cohen ring is a discrete valuation ring).
Completeness is `Stacks.CompleteLocalRing.RegularSubring.isAdicComplete_maximalIdeal_mvPowerSeries`
and regularity `MvPowerSeries.isRegularLocalRing`, both applied to the regular complete local
base ring.

## References

* [Stacks Project, Tag 032C](https://stacks.math.columbia.edu/tag/032C)
* [Stacks Project, Tag 032A](https://stacks.math.columbia.edu/tag/032A)
-/

@[expose] public section

universe u

open IsLocalRing

namespace MvPowerSeries

/-- **Power series over a field.** For a field `k`, the power series ring `k[[X_1, …, X_d]]` is a
Noetherian complete local regular ring of dimension `d`. Locality is part of
`IsRegularLocalRing`. -/
theorem isRegularLocalRing_and_ringKrullDim_of_field (k : Type u) [Field k] (d : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin d) k) ∧
      IsAdicComplete (maximalIdeal (MvPowerSeries (Fin d) k)) (MvPowerSeries (Fin d) k) ∧
        IsRegularLocalRing (MvPowerSeries (Fin d) k) ∧
          ringKrullDim (MvPowerSeries (Fin d) k) = d := by
  have : IsAdicComplete (maximalIdeal k) k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  have hreg : IsRegularLocalRing (MvPowerSeries (Fin d) k) := MvPowerSeries.isRegularLocalRing k d
  refine ⟨hreg.toIsNoetherian,
    Stacks.CompleteLocalRing.RegularSubring.isAdicComplete_maximalIdeal_mvPowerSeries k d, hreg,
    ?_⟩
  rw [ringKrullDim_fin_eq_add, ringKrullDim_eq_zero_of_field, zero_add]

/-- **Power series over a Cohen ring.** For a Cohen ring `Λ`, the power series ring
`Λ[[X_1, …, X_d]]` is a Noetherian complete local regular ring of dimension `d + 1`. Locality is
part of `IsRegularLocalRing`. -/
theorem isRegularLocalRing_and_ringKrullDim_of_isCohenRing (Λ : Type u) [CommRing Λ] [IsDomain Λ]
    [IsCohenRing Λ] (d : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin d) Λ) ∧
      IsAdicComplete (maximalIdeal (MvPowerSeries (Fin d) Λ)) (MvPowerSeries (Fin d) Λ) ∧
        IsRegularLocalRing (MvPowerSeries (Fin d) Λ) ∧
          ringKrullDim (MvPowerSeries (Fin d) Λ) = (d + 1 : ℕ) := by
  have hreg : IsRegularLocalRing (MvPowerSeries (Fin d) Λ) := MvPowerSeries.isRegularLocalRing Λ d
  refine ⟨hreg.toIsNoetherian,
    Stacks.CompleteLocalRing.RegularSubring.isAdicComplete_maximalIdeal_mvPowerSeries Λ d, hreg,
    ?_⟩
  rw [ringKrullDim_fin_eq_add, IsDiscreteValuationRing.ringKrullDim_eq_one, add_comm]
  push_cast
  rfl

end MvPowerSeries

/-- **A Noetherian complete local ring is a quotient of a regular local ring.** This is the
consequence of the Cohen structure theorem recorded in Stacks 032C; the sharper form, with the
regular local ring of the same embedding dimension, is
`IsLocalRing.exists_isRegularLocalRing_surjective_spanFinrank_maximalIdeal_eq`. -/
theorem IsLocalRing.exists_isRegularLocalRing_surjective (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] :
    ∃ (S : Type u) (_ : CommRing S), IsRegularLocalRing S ∧
      ∃ f : S →+* R, Function.Surjective f := by
  obtain ⟨S, _, hS, f, hf, -⟩ :=
    IsLocalRing.exists_isRegularLocalRing_surjective_spanFinrank_maximalIdeal_eq R
  exact ⟨S, inferInstance, hS, f, hf⟩

/-- **Stacks Project, Tag 032C.** If `k` is a field then the power series ring
`k[[X_1, …, X_d]]` is a Noetherian complete local regular ring of dimension `d`. If `Λ` is a Cohen
ring then `Λ[[X_1, …, X_d]]` is a complete local Noetherian regular ring of dimension `d + 1`.
Hence any Noetherian complete local ring is a quotient of a regular local ring, and in particular
a Noetherian complete local ring is universally catenary.

The four assertions are `MvPowerSeries.isRegularLocalRing_and_ringKrullDim_of_field`,
`MvPowerSeries.isRegularLocalRing_and_ringKrullDim_of_isCohenRing`,
`IsLocalRing.exists_isRegularLocalRing_surjective` and
`isUniversallyCatenary_of_isPrecomplete_maximalIdeal`. Locality of the power series rings is part
of `IsRegularLocalRing`, and completeness of a local ring is completeness for its maximal ideal. -/
@[stacks 032C]
theorem cohen_structure_consequences :
    (∀ (k : Type u) [Field k] (d : ℕ),
      IsNoetherianRing (MvPowerSeries (Fin d) k) ∧
        IsAdicComplete (maximalIdeal (MvPowerSeries (Fin d) k)) (MvPowerSeries (Fin d) k) ∧
          IsRegularLocalRing (MvPowerSeries (Fin d) k) ∧
            ringKrullDim (MvPowerSeries (Fin d) k) = d) ∧
    (∀ (Λ : Type u) [CommRing Λ] [IsDomain Λ] [IsCohenRing Λ] (d : ℕ),
      IsNoetherianRing (MvPowerSeries (Fin d) Λ) ∧
        IsAdicComplete (maximalIdeal (MvPowerSeries (Fin d) Λ)) (MvPowerSeries (Fin d) Λ) ∧
          IsRegularLocalRing (MvPowerSeries (Fin d) Λ) ∧
            ringKrullDim (MvPowerSeries (Fin d) Λ) = (d + 1 : ℕ)) ∧
    (∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
      [IsAdicComplete (maximalIdeal R) R],
      ∃ (S : Type u) (_ : CommRing S), IsRegularLocalRing S ∧
        ∃ f : S →+* R, Function.Surjective f) ∧
    (∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
      [IsAdicComplete (maximalIdeal R) R], Ring.IsUniversallyCatenary R) :=
  ⟨MvPowerSeries.isRegularLocalRing_and_ringKrullDim_of_field,
    MvPowerSeries.isRegularLocalRing_and_ringKrullDim_of_isCohenRing,
    IsLocalRing.exists_isRegularLocalRing_surjective,
    fun R _ _ _ _ => isUniversallyCatenary_of_isPrecomplete_maximalIdeal R⟩

end
