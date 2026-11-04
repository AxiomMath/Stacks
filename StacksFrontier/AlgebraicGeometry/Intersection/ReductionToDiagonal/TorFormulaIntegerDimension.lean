module

public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaWhole
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.Whole
public import StacksFrontier.Topology.Dimension.Krull
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0B0W with an integer expected dimension

Let `X` be a nonsingular variety over an algebraically closed field — the chapter's convention,
Tag 0AZ8 — of dimension `dX`, and let `ℱ`, `𝒢` be coherent `𝒪_X`-modules with

`dim (Supp ℱ) ≤ r`,  `dim (Supp 𝒢) ≤ s`,  `dim (Supp ℱ ∩ Supp 𝒢) ≤ r + s - dX`.

Then `[ℱ]_r` and `[𝒢]_s` intersect properly and
`[ℱ]_r · [𝒢]_s = ∑ₚ (-1)ᵖ [Torₚ^{𝒪_X}(ℱ, 𝒢)]_{r + s - dX}`.

The expected dimension `r + s - dX` is an integer and may be negative. In that case the third
bound says that `Supp ℱ ∩ Supp 𝒢` is empty (a nonempty space has dimension at least `0`), the
two cycles intersect properly vacuously, and both sides of the formula are `0`, because there
are no cycles of negative dimension on a scheme over a field.

## Main results

* `Stacks.Intersection.ReductionToDiagonal.torFormula_integerDimension` — **Tag 0B0W**, both
  clauses, in every case of `r + s - dX ∈ ℤ`.
* `Stacks.Intersection.ReductionToDiagonal.torFormula_eq_zero_of_add_lt` — when `r + s < dX`
  the two supports are disjoint and both sides of the formula vanish.

## Implementation notes

`WithBot ℕ∞` has no subtraction, so the bound `dim (Supp ℱ ∩ Supp 𝒢) ≤ r + s - dX` is spelled
`dim (Supp ℱ ∩ Supp 𝒢) + dX ≤ r + s`, the spelling of proper intersection in Tag 0AZQ. The two
are the same: for a nonempty intersection both say that its dimension is a natural number at
most the integer `r + s - dX`, and for an empty one (dimension `⊥ = -∞`) both hold. The
equality of cycles is `Stacks.Intersection.ReductionToDiagonal.torFormula_coherent`, which is
stated for an arbitrary integer dimension, and the properness clause is
`Stacks.Intersection.ReductionToDiagonal.intersectProperly_coherentSheafCycle`, whose hypothesis
is this bound.

## References

* [Stacks Project, Lemma 43.19.4 (Tag 0B0W)](https://stacks.math.columbia.edu/tag/0B0W)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.TorFormula
open Stacks.Chow

namespace Stacks.Intersection.ReductionToDiagonal

universe u

/-! ### The bound `dim T + d ≤ r + s` read pointwise -/

/-- A nonempty space `T` with `dim T + d ≤ N` has dimension at most a natural number `m` with
`m + d ≤ N`. -/
theorem exists_nat_topologicalKrullDim_le_of_add_le {T : Type*} [TopologicalSpace T]
    [Nonempty T] {d N : ℕ}
    (h : topologicalKrullDim T + (d : WithBot ℕ∞) ≤ (N : WithBot ℕ∞)) :
    ∃ m : ℕ, topologicalKrullDim T ≤ (m : WithBot ℕ∞) ∧ m + d ≤ N := by
  have hbot : topologicalKrullDim T ≠ ⊥ := fun h0 =>
    not_isEmpty_of_nonempty T ((topologicalKrullDim_eq_bot_iff_isEmpty T).1 h0)
  set a := topologicalKrullDim T
  clear_value a
  lift a to ℕ∞ using hbot with b
  have h' : b + (d : ℕ∞) ≤ (N : ℕ∞) := by exact_mod_cast h
  have hb : b ≠ ⊤ := by
    rintro rfl
    rw [top_add, top_le_iff] at h'
    exact ENat.natCast_ne_top N h'
  lift b to ℕ using hb with m
  exact ⟨m, le_rfl, by exact_mod_cast h'⟩

/-- **The integer dimension bound, pointwise.** If a closed subset `T` of a scheme locally of
finite type over a field satisfies `dim T + d ≤ r + s`, every point of `T` has relative dimension
at most the integer `r + s - d`. For `r + s < d` this says that `T` is empty. -/
theorem relativeDimension_le_of_topologicalKrullDim_add_le (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {T : Set X}
    (hT : IsClosed T) {d r s : ℕ}
    (h : topologicalKrullDim T + (d : WithBot ℕ∞) ≤ (r : WithBot ℕ∞) + (s : WithBot ℕ∞))
    {x : X} (hx : x ∈ T) :
    relativeDimension (fieldChowSituation k).dimensionFunction f x ≤ (r : ℤ) + s - d := by
  have : Nonempty T := ⟨⟨x, hx⟩⟩
  obtain ⟨m, hm, hmd⟩ := exists_nat_topologicalKrullDim_le_of_add_le (T := T) (N := r + s)
    (by exact_mod_cast h)
  have hx' := relativeDimension_le_of_topologicalKrullDim_le (fieldChowSituation k)
    (fun _ _ => rfl) f hT hm hx
  omega

/-- If `r + s < d`, a set `T` with `dim T + d ≤ r + s` is empty. -/
theorem eq_empty_of_topologicalKrullDim_add_le_of_lt {Y : Type*} [TopologicalSpace Y]
    {T : Set Y} {d r s : ℕ}
    (h : topologicalKrullDim T + (d : WithBot ℕ∞) ≤ (r : WithBot ℕ∞) + (s : WithBot ℕ∞))
    (hlt : r + s < d) : T = ∅ := by
  by_contra hne
  have : Nonempty T := (Set.nonempty_iff_ne_empty.2 hne).to_subtype
  obtain ⟨m, -, hmd⟩ := exists_nat_topologicalKrullDim_le_of_add_le (T := T) (N := r + s)
    (by exact_mod_cast h)
  omega

/-! ### Tag 0B0W -/

/-- **Tag 0B0W in an integer dimension `n` with `r + s = dX + n`.** This is
`torFormula_integerDimension` with the expected dimension `r + s - dX` named `n`, the form in
which it is applied after a change of dimensions, e.g. after flat pullback. -/
theorem torFormula_of_add_eq (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] (hX : IsRegular X)
    (F G : X.Modules) (hFc : _root_.SheafOfModules.IsCoherent F)
    (hGc : _root_.SheafOfModules.IsCoherent G) (r s dX : ℕ) (n : ℤ)
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞)) (hrs : (r : ℤ) + s = dX + n)
    (hFr : topologicalKrullDim (SheafOfModules.supp F : Set X) ≤ (r : WithBot ℕ∞))
    (hGs : topologicalKrullDim (SheafOfModules.supp G : Set X) ≤ (s : WithBot ℕ∞))
    (hFG : topologicalKrullDim (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set X) +
      (dX : WithBot ℕ∞) ≤ (r : WithBot ℕ∞) + (s : WithBot ℕ∞)) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    letI := hFc
    letI := hGc
    letI := isFiniteType_of_isCoherent F
    letI := isFiniteType_of_isCoherent G
    have hFr' := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k f F r hFr
    have hGs' := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k f G s hGs
    have hn : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp G,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n :=
      fun _ hw => (relativeDimension_le_of_topologicalKrullDim_add_le k f
        ((SheafOfModules.isClosed_supp F).inter (SheafOfModules.isClosed_supp G)) hFG hw).trans
          (by omega)
    AlgebraicCycle.IntersectProperly
        (coherentSheafCycle (fieldChowSituation k) f F (r : ℤ) hFr')
        (coherentSheafCycle (fieldChowSituation k) f G (s : ℤ) hGs') ∧
      torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n
          (coherentSheafCycle (fieldChowSituation k) f F (r : ℤ) hFr')
          (coherentSheafCycle (fieldChowSituation k) f G (s : ℤ) hGs')
        = intersectionProductCycle (fieldChowSituation k) f hX F G hFc hGc n
            (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX F G hFc
              hGc n hn) := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have := hFc
  have := hGc
  have := isFiniteType_of_isCoherent F
  have := isFiniteType_of_isCoherent G
  intro hFr' hGs' hn
  refine ⟨intersectProperly_coherentSheafCycle k f F G r s _ _ (by rwa [hdX]), ?_⟩
  exact torFormula_coherent k f hX (r : ℤ) (s : ℤ) n dX hdX hrs
    F hFc
    (fun w hw => relativeDimension_le_of_topologicalKrullDim_le (fieldChowSituation k)
      (fun _ _ => rfl) f (SheafOfModules.isClosed_supp F) hFr hw)
    G hGc
    (fun w hw => relativeDimension_le_of_topologicalKrullDim_le (fieldChowSituation k)
      (fun _ _ => rfl) f (SheafOfModules.isClosed_supp G) hGs hw) hn

/-- **Stacks Project, Tag 0B0W**, with the expected dimension an integer. Let `X` be a
nonsingular variety over an algebraically closed field — the chapter's convention, Tag 0AZ8 —
of dimension `dX`, and let `ℱ`, `𝒢` be coherent `𝒪_X`-modules with `dim (Supp ℱ) ≤ r`,
`dim (Supp 𝒢) ≤ s` and `dim (Supp ℱ ∩ Supp 𝒢) ≤ r + s - dX`. Then the cycles `[ℱ]_r` and
`[𝒢]_s` intersect properly and

`[ℱ]_r · [𝒢]_s = ∑ₚ (-1)ᵖ [Torₚ^{𝒪_X}(ℱ, 𝒢)]_{r + s - dX}`.

Here `r + s - dX` is the integer `(r : ℤ) + s - dX`, and all of its values are covered, the
negative ones included. `WithBot ℕ∞` has no subtraction, so the third bound is written
`dim (Supp ℱ ∩ Supp 𝒢) + dX ≤ r + s`; when `r + s < dX` it says that the supports are
disjoint, and then both sides are `0` (`torFormula_eq_zero_of_add_lt`). The intersection
product of cycles is the one of Tag 0B08 and the right-hand side is the alternating sum of
Tag 0AZR. -/
@[stacks 0B0W "the whole lemma, in every case of the integer expected dimension \
`r + s - dim X`, the case `r + s < dim X` included: the properness of `[ℱ]_r` and `[𝒢]_s` and \
the Tor formula `[ℱ]_r · [𝒢]_s = ∑ₚ (-1)ᵖ [Torₚ^{𝒪_X}(ℱ, 𝒢)]_{r + s - dim X}`, for a \
nonsingular variety over an algebraically closed field — the chapter's own convention, Tag \
0AZ8 — under the source's own three dimension bounds, read as bounds on the topological \
dimension of the two supports and of their intersection. `WithBot ℕ∞` has no subtraction, so \
`dim (Supp ℱ ∩ Supp 𝒢) ≤ r + s - dim X` is spelled `dim (Supp ℱ ∩ Supp 𝒢) + dim X ≤ r + s`, \
as proper intersection is in Tag 0AZQ; both products are taken in the integer dimension \
`(r : ℤ) + s - dim X`. The left-hand side is the intersection product of Tag 0B08 and the \
right-hand side the alternating sum of Tag 0AZR."]
theorem torFormula_integerDimension (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] (hX : IsRegular X)
    (F G : X.Modules) (hFc : _root_.SheafOfModules.IsCoherent F)
    (hGc : _root_.SheafOfModules.IsCoherent G) (r s dX : ℕ)
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hFr : topologicalKrullDim (SheafOfModules.supp F : Set X) ≤ (r : WithBot ℕ∞))
    (hGs : topologicalKrullDim (SheafOfModules.supp G : Set X) ≤ (s : WithBot ℕ∞))
    (hFG : topologicalKrullDim (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set X) +
      (dX : WithBot ℕ∞) ≤ (r : WithBot ℕ∞) + (s : WithBot ℕ∞)) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    letI := hFc
    letI := hGc
    letI := isFiniteType_of_isCoherent F
    letI := isFiniteType_of_isCoherent G
    have hFr' := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k f F r hFr
    have hGs' := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k f G s hGs
    have hn : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp G,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ (r : ℤ) + s - dX :=
      fun _ hw => relativeDimension_le_of_topologicalKrullDim_add_le k f
        ((SheafOfModules.isClosed_supp F).inter (SheafOfModules.isClosed_supp G)) hFG hw
    AlgebraicCycle.IntersectProperly
        (coherentSheafCycle (fieldChowSituation k) f F (r : ℤ) hFr')
        (coherentSheafCycle (fieldChowSituation k) f G (s : ℤ) hGs') ∧
      torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX ((r : ℤ) + s - dX)
          (coherentSheafCycle (fieldChowSituation k) f F (r : ℤ) hFr')
          (coherentSheafCycle (fieldChowSituation k) f G (s : ℤ) hGs')
        = intersectionProductCycle (fieldChowSituation k) f hX F G hFc hGc ((r : ℤ) + s - dX)
            (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX F G hFc
              hGc ((r : ℤ) + s - dX) hn) :=
  torFormula_of_add_eq k f hX F G hFc hGc r s dX ((r : ℤ) + s - dX) hdX (by ring) hFr hGs hFG

/-- **The case `r + s < dim X` of Tag 0B0W.** Under the hypotheses of
`torFormula_integerDimension`, if `r + s < dX` then the supports of `ℱ` and `𝒢` are disjoint and
both sides of the Tor formula are the zero cycle: there are no cycles of negative dimension on a
scheme over a field. -/
theorem torFormula_eq_zero_of_add_lt (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] (hX : IsRegular X)
    (F G : X.Modules) (hFc : _root_.SheafOfModules.IsCoherent F)
    (hGc : _root_.SheafOfModules.IsCoherent G) (r s dX : ℕ)
    (hFr : topologicalKrullDim (SheafOfModules.supp F : Set X) ≤ (r : WithBot ℕ∞))
    (hGs : topologicalKrullDim (SheafOfModules.supp G : Set X) ≤ (s : WithBot ℕ∞))
    (hFG : topologicalKrullDim (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set X) +
      (dX : WithBot ℕ∞) ≤ (r : WithBot ℕ∞) + (s : WithBot ℕ∞)) (hlt : r + s < dX) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    letI := hFc
    letI := hGc
    letI := isFiniteType_of_isCoherent F
    letI := isFiniteType_of_isCoherent G
    have hFr' := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k f F r hFr
    have hGs' := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k f G s hGs
    have hn : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp G,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ (r : ℤ) + s - dX :=
      fun _ hw => relativeDimension_le_of_topologicalKrullDim_add_le k f
        ((SheafOfModules.isClosed_supp F).inter (SheafOfModules.isClosed_supp G)) hFG hw
    (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set X) = ∅ ∧
      torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX ((r : ℤ) + s - dX)
          (coherentSheafCycle (fieldChowSituation k) f F (r : ℤ) hFr')
          (coherentSheafCycle (fieldChowSituation k) f G (s : ℤ) hGs') = 0 ∧
      intersectionProductCycle (fieldChowSituation k) f hX F G hFc hGc ((r : ℤ) + s - dX)
          (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX F G hFc
            hGc ((r : ℤ) + s - dX) hn) = 0 := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have := hFc
  have := hGc
  have := isFiniteType_of_isCoherent F
  have := isFiniteType_of_isCoherent G
  intro hFr' hGs' hn
  have hneg : (r : ℤ) + s - dX < 0 := by omega
  refine ⟨eq_empty_of_topologicalKrullDim_add_le_of_lt hFG hlt, ?_, ?_⟩
  · exact eq_zero_of_mem_cyclesOfDimension_of_neg k f hneg
      (torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation k) f hX
        ((r : ℤ) + s - dX)
        (coherentSheafCycle (fieldChowSituation k) f F (r : ℤ) hFr')
        (coherentSheafCycle (fieldChowSituation k) f G (s : ℤ) hGs'))
  · exact eq_zero_of_mem_cyclesOfDimension_of_neg k f hneg
      (intersectionProductCycle_mem_cyclesOfDimension (fieldChowSituation k) f hX F G hFc hGc
        ((r : ℤ) + s - dX)
        (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX F G hFc
          hGc ((r : ℤ) + s - dX) hn))

end Stacks.Intersection.ReductionToDiagonal

end
