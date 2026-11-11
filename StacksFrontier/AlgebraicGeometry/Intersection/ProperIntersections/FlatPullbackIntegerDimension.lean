module

public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackWhole
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaIntegerDimension
import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback and intersection products, with an integer expected dimension

Stacks 0B0Y and 0B0Z for a flat morphism `f : X ⟶ Y` of nonsingular varieties over an
algebraically closed field — the chapter's convention, Tag 0AZ8 — with `dim X = dim Y + e`,
stated with the expected dimension `r + s - dim Y` an integer, so that the case
`r + s < dim Y` is covered.

* Tag 0B0Y: for coherent `ℱ`, `𝒢` on `Y` with `dim Supp ℱ ≤ r`, `dim Supp 𝒢 ≤ s` and
  `dim (Supp ℱ ∩ Supp 𝒢) ≤ r + s - dim Y`, the cycles `[f^*ℱ]_{r+e}` and `[f^*𝒢]_{s+e}` intersect
  properly and `f^*([ℱ]_r · [𝒢]_s) = [f^*ℱ]_{r+e} · [f^*𝒢]_{s+e}`.
* Tag 0B0Z: for an `r`-cycle `α` and an `s`-cycle `β` on `Y` intersecting properly, `f^*α` and
  `f^*β` intersect properly and `f^*(α · β) = f^*α · f^*β`.

When `r + s < dim Y` the hypotheses force the supports (in 0B0Y), resp. any component of `α` and
any component of `β` (in 0B0Z), to be disjoint, and both sides of each identity are `0`: the
product downstairs lives in negative dimension, where there are no cycles on a scheme over a
field. The vanishing of both sides is
`flatPullback_coherentSheafCycleProduct_eq_zero_of_add_lt` and
`flatPullback_torFormulaCycleIntersectionProduct_eq_zero_of_add_lt`.

## Main results

* `Stacks.Intersection.CycleFlatPullback.flatPullback_coherentSheafCycleProduct_integerDimension`
  — **Tag 0B0Y**, in every case of the integer `r + s - dim Y`.
* `Stacks.Intersection.CycleFlatPullback.`
  `flatPullback_torFormulaCycleIntersectionProduct_eq_integerDimension` — **Tag 0B0Z**,
  in every case of the integer `r + s - dim Y`.

## Implementation notes

The proofs are those of `flatPullback_coherentSheafCycleProduct` and
`flatPullback_torFormulaCycleIntersectionProduct_eq`, run with an integer dimension `n` and with
Tag 0B0W in the form `Stacks.Intersection.ReductionToDiagonal.torFormula_of_add_eq`, whose
intersection bound `dim (Supp ℱ ∩ Supp 𝒢) + dim X ≤ r + s` makes sense for every integer
`r + s - dim X` (`WithBot ℕ∞` has no subtraction). That bound passes to the pulled-back sheaves:
for an empty intersection because the pulled-back supports are the preimages, and for a nonempty
one by `topologicalKrullDim_supp_inter_pullback_le`.

## References

* [Stacks Project, Lemma 43.21.1 (Tag 0B0Y)](https://stacks.math.columbia.edu/tag/0B0Y)
* [Stacks Project, Lemma 43.21.2 (Tag 0B0Z)](https://stacks.math.columbia.edu/tag/0B0Z)
* [Stacks Project, Lemma 43.19.4 (Tag 0B0W)](https://stacks.math.columbia.edu/tag/0B0W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula
open Stacks.Intersection.ReductionToDiagonal (torFormula_of_add_eq
  relativeDimension_le_of_topologicalKrullDim_add_le exists_nat_topologicalKrullDim_le_of_add_le
  eq_empty_of_topologicalKrullDim_add_le_of_lt eq_zero_of_mem_cyclesOfDimension_of_neg)

universe u

namespace Stacks.Intersection.CycleFlatPullback

/-! ### The intersection bound after flat pullback -/

/-- **The integer intersection bound after flat pullback.** If the supports of `ℱ` and `𝒢` on
`Y` satisfy `dim (Supp ℱ ∩ Supp 𝒢) + dim Y ≤ r + s`, the supports of `f^*ℱ` and `f^*𝒢` satisfy
`dim (Supp f^*ℱ ∩ Supp f^*𝒢) + (dim Y + e) ≤ (r + e) + (s + e)`. -/
theorem topologicalKrullDim_supp_inter_pullback_add_le (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX]
    [IsVariety K sY] (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (F G : Y.Modules) [F.IsFiniteType] [G.IsFiniteType] {dY r s : ℕ}
    (hFG : topologicalKrullDim (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y) +
      (dY : WithBot ℕ∞) ≤ (r : WithBot ℕ∞) + (s : WithBot ℕ∞)) :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback f).obj F) ∩
        SheafOfModules.supp ((Scheme.Modules.pullback f).obj G) : Set X) +
        ((dY + e : ℕ) : WithBot ℕ∞) ≤
      ((r + e : ℕ) : WithBot ℕ∞) + ((s + e : ℕ) : WithBot ℕ∞) := by
  by_cases hS : (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y) = ∅
  · have hX : (SheafOfModules.supp ((Scheme.Modules.pullback f).obj F) ∩
        SheafOfModules.supp ((Scheme.Modules.pullback f).obj G) : Set X) = ∅ := by
      rw [Stacks.Modules.supp_pullback f F, Stacks.Modules.supp_pullback f G,
        ← Set.preimage_inter, hS, Set.preimage_empty]
    rw [hX, (topologicalKrullDim_eq_bot_iff_isEmpty _).2 inferInstance, WithBot.bot_add]
    exact bot_le
  · have : Nonempty (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y) :=
      (Set.nonempty_iff_ne_empty.2 hS).to_subtype
    obtain ⟨m, hm, hmd⟩ := exists_nat_topologicalKrullDim_le_of_add_le
      (T := (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y)) (N := r + s)
      (by push_cast; exact hFG)
    calc _ ≤ ((m + e : ℕ) : WithBot ℕ∞) + ((dY + e : ℕ) : WithBot ℕ∞) :=
          add_le_add_left
            (topologicalKrullDim_supp_inter_pullback_le K sX sY f hbase e he F G m hm) _
      _ = (((m + e) + (dY + e) : ℕ) : WithBot ℕ∞) := by push_cast; rfl
      _ ≤ (((r + e) + (s + e) : ℕ) : WithBot ℕ∞) :=
          (Nat.cast_le (α := WithBot ℕ∞)).mpr (by omega)
      _ = _ := by push_cast; rfl

/-- The flat pullback of a Tor-formula product in a negative dimension `d` is the zero cycle. -/
private theorem flatPullback_torFormulaCycleIntersectionProduct_eq_zero_of_neg (K : Type u)
    [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K))
    (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX)
    (e : ℕ) (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) (d : ℤ)
    (hd : d < 0) (a b : AlgebraicCycle Y ℤ) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    (flatPullback (fieldChowSituation K) sX sY f hbase e
        (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) d
        ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY d a b,
          torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sY hY
            d a b⟩).1 = 0 := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  rw [show (⟨_, torFormulaCycleIntersectionProduct_mem_cyclesOfDimension
      (fieldChowSituation K) sY hY d a b⟩ : CycleGroup (fieldChowSituation K) sY d) = 0 from
    Subtype.ext (eq_zero_of_mem_cyclesOfDimension_of_neg K sY hd
      (torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sY hY
        _ _ _)), map_zero]
  rfl

/-! ### Stacks 0B0Y -/

/-- **Tag 0B0Y in an integer dimension `n` with `r + s = dim Y + n`.** This is
`flatPullback_coherentSheafCycleProduct_integerDimension` with the expected dimension
`r + s - dim Y` named `n`. -/
theorem flatPullback_coherentSheafCycleProduct_of_add_eq (K : Type u) [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    [IsVariety K sX] [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X)
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX)
    (F G : Y.Modules) (hFc : _root_.SheafOfModules.IsCoherent F)
    (hGc : _root_.SheafOfModules.IsCoherent G) (r s dY e : ℕ) (n : ℤ)
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (hrs : (r : ℤ) + s = dY + n)
    (hFr : topologicalKrullDim (SheafOfModules.supp F : Set Y) ≤ (r : WithBot ℕ∞))
    (hGs : topologicalKrullDim (SheafOfModules.supp G : Set Y) ≤ (s : WithBot ℕ∞))
    (hFG : topologicalKrullDim (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y) +
      (dY : WithBot ℕ∞) ≤ (r : WithBot ℕ∞) + (s : WithBot ℕ∞)) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_isRegular hY
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    letI := hFc
    letI := hGc
    letI := isFiniteType_of_isCoherent F
    letI := isFiniteType_of_isCoherent G
    letI := AlgebraicGeometry.isCoherent_pullback f F
    letI := AlgebraicGeometry.isCoherent_pullback f G
    have hFrY := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY F r hFr
    have hGsY := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY G s hGs
    have hFrX := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sX
      ((Scheme.Modules.pullback f).obj F) (r + e)
      (topologicalKrullDim_supp_pullback_le K sX sY f hbase e he F r hFr)
    have hGsX := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sX
      ((Scheme.Modules.pullback f).obj G) (s + e)
      (topologicalKrullDim_supp_pullback_le K sX sY f hbase e he G s hGs)
    AlgebraicCycle.IntersectProperly
        (coherentSheafCycle (fieldChowSituation K) sX ((Scheme.Modules.pullback f).obj F)
          ((r + e : ℕ) : ℤ) hFrX)
        (coherentSheafCycle (fieldChowSituation K) sX ((Scheme.Modules.pullback f).obj G)
          ((s + e : ℕ) : ℤ) hGsX) ∧
      (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) n
          ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY n
              (coherentSheafCycle (fieldChowSituation K) sY F (r : ℤ) hFrY)
              (coherentSheafCycle (fieldChowSituation K) sY G (s : ℤ) hGsY),
            torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sY hY
              n _ _⟩).1 =
        torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n + (e : ℤ))
          (coherentSheafCycle (fieldChowSituation K) sX ((Scheme.Modules.pullback f).obj F)
            ((r + e : ℕ) : ℤ) hFrX)
          (coherentSheafCycle (fieldChowSituation K) sX ((Scheme.Modules.pullback f).obj G)
            ((s + e : ℕ) : ℤ) hGsX) := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  let : IsLocallyNoetherian Y := isLocallyNoetherian_of_isRegular hY
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have := hFc
  have := hGc
  have := isFiniteType_of_isCoherent F
  have := isFiniteType_of_isCoherent G
  have := AlgebraicGeometry.isCoherent_pullback f F
  have := AlgebraicGeometry.isCoherent_pullback f G
  have hFrXtop := topologicalKrullDim_supp_pullback_le K sX sY f hbase e he F r hFr
  have hGsXtop := topologicalKrullDim_supp_pullback_le K sX sY f hbase e he G s hGs
  have hFGXtop := topologicalKrullDim_supp_inter_pullback_add_le K sX sY f hbase e he F G hFG
  have hdX : topologicalKrullDim X = ((dY + e : ℕ) : WithBot ℕ∞) := by
    rw [he, hdY]; push_cast; rfl
  have hrs' : ((r + e : ℕ) : ℤ) + ((s + e : ℕ) : ℤ) = ((dY + e : ℕ) : ℤ) + (n + (e : ℤ)) := by
    push_cast; omega
  obtain ⟨hpropX, hidX⟩ := torFormula_of_add_eq K sX hX
    ((Scheme.Modules.pullback f).obj F) ((Scheme.Modules.pullback f).obj G)
    (AlgebraicGeometry.isCoherent_pullback f F) (AlgebraicGeometry.isCoherent_pullback f G)
    (r + e) (s + e) (dY + e) (n + (e : ℤ)) hdX hrs' hFrXtop hGsXtop hFGXtop
  obtain ⟨-, hidY⟩ := torFormula_of_add_eq K sY hY F G hFc hGc r s dY n hdY hrs hFr hGs hFG
  refine ⟨hpropX, ?_⟩
  have harg : (⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY n
          (coherentSheafCycle (fieldChowSituation K) sY F (r : ℤ) _)
          (coherentSheafCycle (fieldChowSituation K) sY G (s : ℤ) _),
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sY hY
          n _ _⟩ : CycleGroup (fieldChowSituation K) sY n) =
      intersectionProductCycleGroup (fieldChowSituation K) sY hY F G hFc hGc n _ :=
    Subtype.ext hidY
  rw [harg,
    Stacks.Intersection.FlatPullback.flatPullback_intersectionProductCycleGroup_eq_pullbackSheaves
      K sX sY hX hY f hbase e he F G hFc hGc n _, hidX]
  rfl

/-- **Stacks Project, Tag 0B0Y**, with the expected dimension an integer. Let `f : X ⟶ Y` be a
flat morphism of nonsingular varieties over an algebraically closed field `K` — the chapter's
convention, Tag 0AZ8 — and set `e = dim X - dim Y`. Let `ℱ` and `𝒢` be coherent sheaves on `Y`
with `dim Supp ℱ ≤ r`, `dim Supp 𝒢 ≤ s` and `dim(Supp ℱ ∩ Supp 𝒢) ≤ r + s - dim Y`. Then the
cycles `[f^*ℱ]_{r+e}` and `[f^*𝒢]_{s+e}` intersect properly and

`f^*([ℱ]_r · [𝒢]_s) = [f^*ℱ]_{r+e} · [f^*𝒢]_{s+e}`.

The products are taken in the integer dimensions `r + s - dim Y` downstairs and
`r + s - dim Y + e` upstairs, every value included, the negative ones too. `WithBot ℕ∞` has no
subtraction, so the third bound is written `dim(Supp ℱ ∩ Supp 𝒢) + dim Y ≤ r + s`; when
`r + s < dim Y` it says that the supports are disjoint, and both sides are then `0`
(`flatPullback_coherentSheafCycleProduct_eq_zero_of_add_lt`). -/
@[stacks 0B0Y "the whole lemma, in every case of the integer expected dimension \
`r + s - dim Y`, the case `r + s < dim Y` included: both that `[f^*ℱ]_{r+e}` and \
`[f^*𝒢]_{s+e}` intersect properly and the identity \
`f^*([ℱ]_r · [𝒢]_s) = [f^*ℱ]_{r+e} · [f^*𝒢]_{s+e}`, for a flat morphism of nonsingular \
varieties over an algebraically closed field — the chapter's own convention, Tag 0AZ8 — under \
the source's own three dimension bounds on `Supp ℱ`, `Supp 𝒢` and their intersection. \
`WithBot ℕ∞` has no subtraction, so `dim(Supp ℱ ∩ Supp 𝒢) ≤ r + s - dim Y` is spelled \
`dim(Supp ℱ ∩ Supp 𝒢) + dim Y ≤ r + s`, as proper intersection is in Tag 0AZQ, and the \
products are taken in the integer dimensions `(r : ℤ) + s - dim Y` and `(r : ℤ) + s - dim Y + e`. \
Both products are the Section 43.17 product of cycles \
`AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct` (Tag 0B08). The proof is the \
source's: Tag 0B0W downstairs and upstairs, Tag 0AZF on each Tor summand, and the comparison \
`f^*Torᵢ(ℱ, 𝒢) ≅ Torᵢ(f^*ℱ, f^*𝒢)` from Tag 079U and the exactness of `f^*`, which is \
`AlgebraicGeometry.TorFormula.pullbackTorSheafIso`, proved in this library, so the statement carries no \
hypothesis beyond the source's."]
theorem flatPullback_coherentSheafCycleProduct_integerDimension (K : Type u) [Field K]
    [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    [IsVariety K sX] [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X)
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX)
    (F G : Y.Modules) (hFc : _root_.SheafOfModules.IsCoherent F)
    (hGc : _root_.SheafOfModules.IsCoherent G) (r s dY e : ℕ)
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (hFr : topologicalKrullDim (SheafOfModules.supp F : Set Y) ≤ (r : WithBot ℕ∞))
    (hGs : topologicalKrullDim (SheafOfModules.supp G : Set Y) ≤ (s : WithBot ℕ∞))
    (hFG : topologicalKrullDim (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y) +
      (dY : WithBot ℕ∞) ≤ (r : WithBot ℕ∞) + (s : WithBot ℕ∞)) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_isRegular hY
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    letI := hFc
    letI := hGc
    letI := isFiniteType_of_isCoherent F
    letI := isFiniteType_of_isCoherent G
    letI := AlgebraicGeometry.isCoherent_pullback f F
    letI := AlgebraicGeometry.isCoherent_pullback f G
    have hFrY := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY F r hFr
    have hGsY := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY G s hGs
    have hFrX := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sX
      ((Scheme.Modules.pullback f).obj F) (r + e)
      (topologicalKrullDim_supp_pullback_le K sX sY f hbase e he F r hFr)
    have hGsX := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sX
      ((Scheme.Modules.pullback f).obj G) (s + e)
      (topologicalKrullDim_supp_pullback_le K sX sY f hbase e he G s hGs)
    AlgebraicCycle.IntersectProperly
        (coherentSheafCycle (fieldChowSituation K) sX ((Scheme.Modules.pullback f).obj F)
          ((r + e : ℕ) : ℤ) hFrX)
        (coherentSheafCycle (fieldChowSituation K) sX ((Scheme.Modules.pullback f).obj G)
          ((s + e : ℕ) : ℤ) hGsX) ∧
      (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) ((r : ℤ) + s - dY)
          ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY ((r : ℤ) + s - dY)
              (coherentSheafCycle (fieldChowSituation K) sY F (r : ℤ) hFrY)
              (coherentSheafCycle (fieldChowSituation K) sY G (s : ℤ) hGsY),
            torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sY hY
              ((r : ℤ) + s - dY) _ _⟩).1 =
        torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s - dY + e)
          (coherentSheafCycle (fieldChowSituation K) sX ((Scheme.Modules.pullback f).obj F)
            ((r + e : ℕ) : ℤ) hFrX)
          (coherentSheafCycle (fieldChowSituation K) sX ((Scheme.Modules.pullback f).obj G)
            ((s + e : ℕ) : ℤ) hGsX) :=
  flatPullback_coherentSheafCycleProduct_of_add_eq K sX sY hX hY f hbase F G hFc hGc r s dY e _
    hdY he (by ring) hFr hGs hFG

/-- **The case `r + s < dim Y` of Tag 0B0Y.** Under the hypotheses of
`flatPullback_coherentSheafCycleProduct_integerDimension`, if `r + s < dim Y` then the supports
of `ℱ` and `𝒢` are disjoint, and both sides of `f^*([ℱ]_r · [𝒢]_s) = [f^*ℱ]_{r+e} · [f^*𝒢]_{s+e}`
are the zero cycle. -/
theorem flatPullback_coherentSheafCycleProduct_eq_zero_of_add_lt (K : Type u) [Field K]
    [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    [IsVariety K sX] [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X)
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX)
    (F G : Y.Modules) (hFc : _root_.SheafOfModules.IsCoherent F)
    (hGc : _root_.SheafOfModules.IsCoherent G) (r s dY e : ℕ)
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (hFr : topologicalKrullDim (SheafOfModules.supp F : Set Y) ≤ (r : WithBot ℕ∞))
    (hGs : topologicalKrullDim (SheafOfModules.supp G : Set Y) ≤ (s : WithBot ℕ∞))
    (hFG : topologicalKrullDim (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y) +
      (dY : WithBot ℕ∞) ≤ (r : WithBot ℕ∞) + (s : WithBot ℕ∞)) (hlt : r + s < dY) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_isRegular hY
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    letI := hFc
    letI := hGc
    letI := isFiniteType_of_isCoherent F
    letI := isFiniteType_of_isCoherent G
    letI := AlgebraicGeometry.isCoherent_pullback f F
    letI := AlgebraicGeometry.isCoherent_pullback f G
    have hFrY := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY F r hFr
    have hGsY := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY G s hGs
    have hFrX := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sX
      ((Scheme.Modules.pullback f).obj F) (r + e)
      (topologicalKrullDim_supp_pullback_le K sX sY f hbase e he F r hFr)
    have hGsX := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sX
      ((Scheme.Modules.pullback f).obj G) (s + e)
      (topologicalKrullDim_supp_pullback_le K sX sY f hbase e he G s hGs)
    (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y) = ∅ ∧
      (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) ((r : ℤ) + s - dY)
          ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY ((r : ℤ) + s - dY)
              (coherentSheafCycle (fieldChowSituation K) sY F (r : ℤ) hFrY)
              (coherentSheafCycle (fieldChowSituation K) sY G (s : ℤ) hGsY),
            torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sY hY
              ((r : ℤ) + s - dY) _ _⟩).1 = 0 ∧
        torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s - dY + e)
          (coherentSheafCycle (fieldChowSituation K) sX ((Scheme.Modules.pullback f).obj F)
            ((r + e : ℕ) : ℤ) hFrX)
          (coherentSheafCycle (fieldChowSituation K) sX ((Scheme.Modules.pullback f).obj G)
            ((s + e : ℕ) : ℤ) hGsX) = 0 := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  let : IsLocallyNoetherian Y := isLocallyNoetherian_of_isRegular hY
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have := hFc
  have := hGc
  have := isFiniteType_of_isCoherent F
  have := isFiniteType_of_isCoherent G
  have := AlgebraicGeometry.isCoherent_pullback f F
  have := AlgebraicGeometry.isCoherent_pullback f G
  have hLHS := flatPullback_torFormulaCycleIntersectionProduct_eq_zero_of_neg K sX sY hY f hbase
    e he ((r : ℤ) + s - dY) (by omega)
    (coherentSheafCycle (fieldChowSituation K) sY F (r : ℤ)
      (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY F r hFr))
    (coherentSheafCycle (fieldChowSituation K) sY G (s : ℤ)
      (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY G s hGs))
  obtain ⟨-, hid⟩ := flatPullback_coherentSheafCycleProduct_integerDimension K sX sY hX hY f
    hbase F G hFc hGc r s dY e hdY he hFr hGs hFG
  exact ⟨eq_empty_of_topologicalKrullDim_add_le_of_lt hFG hlt, hLHS, hid ▸ hLHS⟩

/-! ### Stacks 0B0Z -/

/-- **The flat pullback of the product of two prime cycles, in an integer dimension.** For `v`,
`w` points of `Y` whose closures have delta-dimensions `r` and `s` and intersect properly, and
`n` an integer with `r + s = dim Y + n`, the Section 43.17 product of the flat pullbacks
`f^*[V_v]` and `f^*[W_w]` is the pulled-back summand `[f^*𝒪_{V_v}]_{r+e} · [f^*𝒪_{W_w}]_{s+e}`.
This is `torFormulaCycleIntersectionProduct_flatPullback_primeCycle` for an integer `n`. -/
theorem torFormulaCycleIntersectionProduct_flatPullback_primeCycle_of_add_eq (K : Type u)
    [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K))
    (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X)
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX)
    (e dY r s : ℕ) (n : ℤ) (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (hrs : (r : ℤ) + s = dY + n) (v w : Y)
    (hv : relativeDimension (fieldChowSituation K).dimensionFunction sY v = (r : ℤ))
    (hw : relativeDimension (fieldChowSituation K).dimensionFunction sY w = (s : ℤ))
    (hprop : AlgebraicGeometry.IntersectProperly
      (⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩ : IrreducibleCloseds Y)
      ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n + (e : ℤ))
        (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (r : ℤ)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
            (integralComponentAt v).subschemeι (r : ℤ))).1
        (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (s : ℤ)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
            (integralComponentAt w).subschemeι (s : ℤ))).1 =
      flatPullbackSubvarietyProductTotal K sX sY hX hY f hbase e he n v w := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := isCoherent_structureSheafAt v
  have := isCoherent_structureSheafAt w
  have := isFiniteType_of_isCoherent (structureSheafAt v)
  have := isFiniteType_of_isCoherent (structureSheafAt w)
  have := AlgebraicGeometry.isCoherent_pullback f (structureSheafAt v)
  have := AlgebraicGeometry.isCoherent_pullback f (structureSheafAt w)
  have hdimv : topologicalKrullDim (closure ({v} : Set Y)) = (r : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_singleton_eq K sY v, hv]; simp
  have hdimw : topologicalKrullDim (closure ({w} : Set Y)) = (s : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_singleton_eq K sY w, hw]; simp
  have hFrtop : topologicalKrullDim (SheafOfModules.supp (structureSheafAt v) : Set Y) ≤
      (r : WithBot ℕ∞) := by rw [supp_structureSheafAt v, hdimv]
  have hGstop : topologicalKrullDim (SheafOfModules.supp (structureSheafAt w) : Set Y) ≤
      (s : WithBot ℕ∞) := by rw [supp_structureSheafAt w, hdimw]
  have hFGtop : topologicalKrullDim (SheafOfModules.supp (structureSheafAt v) ∩
      SheafOfModules.supp (structureSheafAt w) : Set Y) + (dY : WithBot ℕ∞) ≤
        (r : WithBot ℕ∞) + (s : WithBot ℕ∞) := by
    rw [supp_structureSheafAt v, supp_structureSheafAt w, ← hdY, ← hdimv, ← hdimw]
    exact (AlgebraicGeometry.intersectProperly_iff _ _).1 hprop
  have hbd : TorSupportBound (fieldChowSituation K) sY hY n v w :=
    torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation K) sY hY
      (structureSheafAt v) (structureSheafAt w) (isCoherent_structureSheafAt v)
      (isCoherent_structureSheafAt w) n fun z hz =>
        (relativeDimension_le_of_topologicalKrullDim_add_le K sY
          ((SheafOfModules.isClosed_supp _).inter (SheafOfModules.isClosed_supp _)) hFGtop
          hz).trans (by omega)
  have hdX : topologicalKrullDim X = ((dY + e : ℕ) : WithBot ℕ∞) := by
    rw [he, hdY]; push_cast; rfl
  have hrs' : ((r + e : ℕ) : ℤ) + ((s + e : ℕ) : ℤ) = ((dY + e : ℕ) : ℤ) + (n + (e : ℤ)) := by
    push_cast; omega
  obtain ⟨-, hidX⟩ := torFormula_of_add_eq K sX hX
    ((Scheme.Modules.pullback f).obj (structureSheafAt v))
    ((Scheme.Modules.pullback f).obj (structureSheafAt w))
    (AlgebraicGeometry.isCoherent_pullback f (structureSheafAt v))
    (AlgebraicGeometry.isCoherent_pullback f (structureSheafAt w))
    (r + e) (s + e) (dY + e) (n + (e : ℤ)) hdX hrs'
    (topologicalKrullDim_supp_pullback_le K sX sY f hbase e he (structureSheafAt v) r hFrtop)
    (topologicalKrullDim_supp_pullback_le K sX sY f hbase e he (structureSheafAt w) s hGstop)
    (topologicalKrullDim_supp_inter_pullback_add_le K sX sY f hbase e he (structureSheafAt v)
      (structureSheafAt w) hFGtop)
  have hpv := congrArg Subtype.val (flatPullback_primeCycle K sX sY f hbase e he v (r : ℤ)
    (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq (fieldChowSituation K) sY
      v hv)
    (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY
      (structureSheafAt v) r hFrtop))
  have hpw := congrArg Subtype.val (flatPullback_primeCycle K sX sY f hbase e he w (s : ℤ)
    (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq (fieldChowSituation K) sY
      w hw)
    (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY
      (structureSheafAt w) s hGstop))
  rw [hpv, hpw,
    flatPullbackSubvarietyProductTotal_eq_of_bound K sX sY hX hY f hbase e he n v w hbd]
  exact hidX

/-- **Tag 0B0Z in an integer dimension `n` with `r + s = dim Y + n`.** This is
`flatPullback_torFormulaCycleIntersectionProduct_eq_integerDimension` with the expected
dimension `r + s - dim Y` named `n`. -/
theorem flatPullback_torFormulaCycleIntersectionProduct_eq_of_add_eq
    (K : Type u) [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K))
    (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X)
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX)
    (e dY r s : ℕ) (n : ℤ)
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (hrs : (r : ℤ) + s = dY + n)
    (α : CycleGroup (fieldChowSituation K) sY (r : ℤ))
    (β : CycleGroup (fieldChowSituation K) sY (s : ℤ))
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    AlgebraicCycle.IntersectProperly
        (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (r : ℤ) α).1
        (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (s : ℤ) β).1 ∧
      (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) n
          ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY n α.1 β.1,
            torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sY hY
              n α.1 β.1⟩).1 =
        torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n + (e : ℤ))
          (flatPullback (fieldChowSituation K) sX sY f hbase e
            (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (r : ℤ) α).1
          (flatPullback (fieldChowSituation K) sX sY f hbase e
            (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (s : ℤ) β).1 := by
  classical
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  refine ⟨intersectProperly_flatPullback K sX sY f hbase e he r s α β hαβ, ?_⟩
  set hrel := relativeDimension_of_flat_of_isVariety K sX sY f hbase e he with hrelDef
  set P : ∀ d : ℤ, Y → CycleGroup (fieldChowSituation K) sY d := fun d v =>
    cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
      (integralComponentAt v).subschemeι d with hPdef
  have hα : (Function.support α.1).Finite := finite_support_of_compactSpace α.1
  have hβ : (Function.support β.1).Finite := finite_support_of_compactSpace β.1
  -- a cycle's flat pullback, as a finite sum of cycles of pulled-back structure sheaves
  have hpull : ∀ (d : ℤ) (γ : CycleGroup (fieldChowSituation K) sY d)
      (hγ : (Function.support γ.1).Finite),
      (flatPullback (fieldChowSituation K) sX sY f hbase e hrel d γ).1 =
        ∑ v ∈ hγ.toFinset, γ.1 v •
          (flatPullback (fieldChowSituation K) sX sY f hbase e hrel d (P d v)).1 := by
    intro d γ hγ
    have h1 : flatPullback (fieldChowSituation K) sX sY f hbase e hrel d γ =
        ∑ v ∈ hγ.toFinset, γ.1 v •
          flatPullback (fieldChowSituation K) sX sY f hbase e hrel d (P d v) := by
      conv_lhs => rw [cycle_eq_sum_zsmul_primeCycles γ hγ]
      rw [map_sum]
      exact Finset.sum_congr rfl fun v _ => map_zsmul _ _ _
    rw [h1]
    simp
  -- the pairwise identity at each pair of components
  have hpair : ∀ v ∈ hα.toFinset, ∀ w ∈ hβ.toFinset,
      torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n + (e : ℤ))
          (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (r : ℤ) (P r v)).1
          (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (s : ℤ) (P s w)).1 =
        flatPullbackSubvarietyProductTotal K sX sY hX hY f hbase e he n v w :=
    fun v hv w hw => torFormulaCycleIntersectionProduct_flatPullback_primeCycle_of_add_eq K sX sY hX
      hY f hbase e dY r s n hdY he hrs v w
      ((mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) sY (r : ℤ) α.1).1 α.2 v
        (hα.mem_toFinset.1 hv))
      ((mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) sY (s : ℤ) β.1).1 β.2 w
        (hβ.mem_toFinset.1 hw))
      (hαβ _ _ (by rw [genericPoint_closure_singleton]; exact hα.mem_toFinset.1 hv)
        (by rw [genericPoint_closure_singleton]; exact hβ.mem_toFinset.1 hw))
  -- the right-hand side, expanded by bilinearity
  have hRHS : torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n + (e : ℤ))
        (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (r : ℤ) α).1
        (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (s : ℤ) β).1 =
      ∑ v ∈ hα.toFinset, ∑ w ∈ hβ.toFinset, (α.1 v * β.1 w) •
        flatPullbackSubvarietyProductTotal K sX sY hX hY f hbase e he n v w := by
    change cycleIntersectionProduct (torFormulaSubvarietyProductTotal (fieldChowSituation K) sX hX
        (n + (e : ℤ))) _ _ = _
    rw [hpull _ α hα, hpull _ β hβ, cycleIntersectionProduct_sum_left]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [cycleIntersectionProduct_zsmul_left _ _ (finite_support_of_compactSpace _)
      (finite_support_of_compactSpace _), cycleIntersectionProduct_sum_right, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [cycleIntersectionProduct_zsmul_right _ _ (finite_support_of_compactSpace _)
      (finite_support_of_compactSpace _), smul_smul]
    exact congrArg (fun z => (α.1 v * β.1 w) • z) (hpair v hv w hw)
  -- the left-hand side, from the double sum over pairs downstairs
  have hsub : Function.support (fun q : Y × Y => (α.1 q.1 * β.1 q.2) •
      flatPullbackSubvarietyProductTotal K sX sY hX hY f hbase e he n q.1 q.2) ⊆
      ↑(hα.toFinset ×ˢ hβ.toFinset) := by
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨hα.mem_toFinset.2 ?_, hβ.mem_toFinset.2 ?_⟩)
    · exact fun h0 => hq (by rw [h0, zero_mul, zero_smul])
    · exact fun h0 => hq (by rw [h0, mul_zero, zero_smul])
  rw [hRHS, flatPullback_torFormulaCycleIntersectionProduct K sX sY hX hY f hbase e he n
    α.1 β.1, finsum_eq_sum_of_support_subset _ hsub, Finset.sum_product]

/-- **Stacks Project, Tag 0B0Z**, with the expected dimension an integer. Let `f : X ⟶ Y` be a
flat morphism of nonsingular varieties over an algebraically closed field `K` — the chapter's
convention, Tag 0AZ8 — with `dim X = dim Y + e`. Let `α` be an `r`-cycle and `β` an `s`-cycle on
`Y` which intersect properly. Then `f^*α` and `f^*β` intersect properly and

`f^*(α · β) = f^*α · f^*β`.

The products are taken in the integer dimensions `r + s - dim Y` downstairs and
`r + s - dim Y + e` upstairs, every value included. When `r + s < dim Y`, proper intersection
forces every component of `α` to be disjoint from every component of `β`, and both sides are
then `0` (`flatPullback_torFormulaCycleIntersectionProduct_eq_zero_of_add_lt`). -/
@[stacks 0B0Z "the whole lemma, in every case of the integer expected dimension \
`r + s - dim Y`, the case `r + s < dim Y` included: both that `f^*α` and `f^*β` intersect \
properly and the identity `f^*(α · β) = f^*α · f^*β`, for an `r`-cycle `α` and an `s`-cycle `β` \
intersecting properly on `Y` and a flat morphism `f : X ⟶ Y` of nonsingular varieties over an \
algebraically closed field — the chapter's own convention, Tag 0AZ8 — with `dim X = dim Y + e`. \
The products are the Section 43.17 product of cycles of Tag 0B08, taken in the integer \
dimensions `(r : ℤ) + s - dim Y` downstairs and `(r : ℤ) + s - dim Y + e` upstairs."]
theorem flatPullback_torFormulaCycleIntersectionProduct_eq_integerDimension
    (K : Type u) [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K))
    (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X)
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX)
    (e dY r s : ℕ)
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (α : CycleGroup (fieldChowSituation K) sY (r : ℤ))
    (β : CycleGroup (fieldChowSituation K) sY (s : ℤ))
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    AlgebraicCycle.IntersectProperly
        (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (r : ℤ) α).1
        (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (s : ℤ) β).1 ∧
      (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) ((r : ℤ) + s - dY)
          ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY ((r : ℤ) + s - dY)
              α.1 β.1,
            torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sY hY
              ((r : ℤ) + s - dY) α.1 β.1⟩).1 =
        torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s - dY + e)
          (flatPullback (fieldChowSituation K) sX sY f hbase e
            (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (r : ℤ) α).1
          (flatPullback (fieldChowSituation K) sX sY f hbase e
            (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (s : ℤ) β).1 :=
  flatPullback_torFormulaCycleIntersectionProduct_eq_of_add_eq K sX sY hX hY f hbase e dY r s _
    hdY he (by ring) α β hαβ

/-- **The case `r + s < dim Y` of Tag 0B0Z.** Under the hypotheses of
`flatPullback_torFormulaCycleIntersectionProduct_eq_integerDimension`, if `r + s < dim Y` then
both sides of `f^*(α · β) = f^*α · f^*β` are the zero cycle. -/
theorem flatPullback_torFormulaCycleIntersectionProduct_eq_zero_of_add_lt
    (K : Type u) [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K))
    (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X)
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX)
    (e dY r s : ℕ)
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (α : CycleGroup (fieldChowSituation K) sY (r : ℤ))
    (β : CycleGroup (fieldChowSituation K) sY (s : ℤ))
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1) (hlt : r + s < dY) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    (flatPullback (fieldChowSituation K) sX sY f hbase e
        (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) ((r : ℤ) + s - dY)
        ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY ((r : ℤ) + s - dY)
            α.1 β.1,
          torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sY hY
            ((r : ℤ) + s - dY) α.1 β.1⟩).1 = 0 ∧
      torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s - dY + e)
          (flatPullback (fieldChowSituation K) sX sY f hbase e
            (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (r : ℤ) α).1
          (flatPullback (fieldChowSituation K) sX sY f hbase e
            (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (s : ℤ) β).1 = 0 := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hLHS := flatPullback_torFormulaCycleIntersectionProduct_eq_zero_of_neg K sX sY hY f hbase
    e he ((r : ℤ) + s - dY) (by omega) α.1 β.1
  obtain ⟨-, hid⟩ := flatPullback_torFormulaCycleIntersectionProduct_eq_integerDimension K sX
    sY hX hY f hbase e dY r s hdY he α β hαβ
  exact ⟨hLHS, hid ▸ hLHS⟩

end Stacks.Intersection.CycleFlatPullback

end

