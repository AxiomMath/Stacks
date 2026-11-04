module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.FlatPullbackVariety
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleComposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.ProperIntersection
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension

/-!
# Flat pullback of properly intersecting cycles

Let `f : X ⟶ Y` be a flat morphism of varieties over a field with `dim X = dim Y + e`, let `α`
be an `r`-cycle and `β` an `s`-cycle on `Y`, and assume that `α` and `β` intersect properly.
Then the pulled-back cycles `f^*α` and `f^*β`, which are an `(r + e)`-cycle and an
`(s + e)`-cycle on `X`, intersect properly.

## Main results

* `Stacks.Intersection.CycleFlatPullback.topologicalKrullDim_coe_eq` — the dimension of an
  irreducible closed subset is its delta-dimension.
* `Stacks.Intersection.CycleFlatPullback.topologicalKrullDim_preimage_le` — along a flat
  morphism of relative dimension `e` the inverse image of a closed subset of dimension at most
  `n` has dimension at most `n + e`.
* `Stacks.Intersection.CycleFlatPullback.intersectProperly_flatPullback` — `f^*α` and `f^*β`
  intersect properly.

## Implementation notes

The second conclusion of Tag 0B0Z, `f^*(α · β) = f^*α · f^*β`, is not stated. The intersection
product of two cycles, `AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct`, is the
bilinear extension of the Tor-formula product of two closed subvarieties, whereas
`Stacks.Intersection.FlatPullback.flatPullback_intersectionProductCycleGroup` concerns the
Tor-formula product of two coherent sheaves; relating the two is the Tor formula of Tag 0B0W.

## References

* [Stacks Project, Lemma 43.21.2 (Tag 0B0Z)](https://stacks.math.columbia.edu/tag/0B0Z)
* [Stacks Project, Lemma 43.21.1 (Tag 0B0Y)](https://stacks.math.columbia.edu/tag/0B0Y)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 0B0W](https://stacks.math.columbia.edu/tag/0B0W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Chow

namespace Stacks.Intersection.CycleFlatPullback

universe u

/-! ### Dimension of the closure of a point -/

/-- An irreducible closed subset is the closure of the generic point by which the cycle groups
index it. -/
theorem coe_eq_closure_genericPoint {Z : Scheme.{u}} (W : IrreducibleCloseds Z) :
    (W : Set Z) = closure {W.isIrreducible.genericPoint} :=
  (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).symm

/-- An irreducible closed subset which is the closure of a point is indexed by that point. -/
theorem genericPoint_eq_of_coe_eq_closure {Z : Scheme.{u}} (W : IrreducibleCloseds Z) (z : Z)
    (h : (W : Set Z) = closure ({z} : Set Z)) : W.isIrreducible.genericPoint = z :=
  (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).eq h.symm

/-- **Stacks Project, Tag 02QO.** Over a field the topological dimension of an irreducible
closed subset is its delta-dimension. -/
theorem topologicalKrullDim_coe_eq (K : Type u) [Field K] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of K)) [LocallyOfFiniteType p] (W : IrreducibleCloseds Z) (n : ℕ)
    (h : deltaDimension (fieldChowSituation K) p W = (n : ℤ)) :
    topologicalKrullDim (W : Set Z) = (n : WithBot ℕ∞) := by
  have hrel := deltaDimension_eq_of_isGenericPoint (fieldChowSituation K) p W
    W.isIrreducible.genericPoint (W.isIrreducible.isGenericPoint_genericPoint W.isClosed)
  rw [coe_eq_closure_genericPoint W,
    topologicalKrullDim_closure_singleton_eq K p W.isIrreducible.genericPoint, ← hrel, h]
  simp

/-! ### The dimension of an inverse image -/

/-- **The topological form of Stacks 02RE part (1).** For a flat morphism `f : X ⟶ Y` of
varieties over a field with `dim X = dim Y + e`, the inverse image of a closed subset of
dimension at most `n` has dimension at most `n + e`. -/
theorem topologicalKrullDim_preimage_le (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (T : Closeds Y) (n : ℕ) (hTn : topologicalKrullDim (T : Set Y) ≤ (n : WithBot ℕ∞)) :
    topologicalKrullDim (f.base ⁻¹' (T : Set Y)) ≤ ((n + e : ℕ) : WithBot ℕ∞) := by
  have hlft : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have hlnY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hlnX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  set I := Scheme.IdealSheafData.vanishingIdeal T with hI
  set M : Y.Modules :=
    (Scheme.Modules.pushforward I.subschemeι).obj (Stacks.Ample.unitModule _) with hM
  have hsuppM : SheafOfModules.supp M = (T : Set Y) := by
    rw [hM, Stacks.Chow.supp_pushforwardStructureSheaf]
    exact (Scheme.IdealSheafData.range_subschemeι I).trans (by simp [hI])
  have hcohM : M.IsCoherent := by rw [hM]; infer_instance
  have hftM : M.IsFiniteType := isFiniteType_of_isCoherent M
  have hdelta := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY M n
    (by rw [hsuppM]; exact hTn)
  have hdelta' := schemeDeltaDimension_support_pullback_le (fieldChowSituation K) sX sY f hbase e
    (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) M (n : ℤ) hdelta
  have hcohP : ((Scheme.Modules.pullback f).obj M).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback f M
  have hsuppP : SheafOfModules.supp ((Scheme.Modules.pullback f).obj M) =
      f.base ⁻¹' (T : Set Y) := by rw [Stacks.Modules.supp_pullback, hsuppM]
  have hfin := topologicalKrullDim_supp_le_of_field_schemeDeltaDimension_le K sX
    ((Scheme.Modules.pullback f).obj M) (n + e) (by push_cast; exact hdelta')
  rwa [hsuppP] at hfin

/-! ### Tag 0B0Z: the pulled-back cycles intersect properly -/

/-- Let `f : X ⟶ Y` be a flat morphism of varieties over a field `K` with `dim X = dim Y + e`,
let `α` be an `r`-cycle and `β` an `s`-cycle on `Y`, and assume `α` and `β` intersect properly.
Then the flat pullbacks `f^*α` and `f^*β` intersect properly. -/
@[stacks 0B0Z "the first conclusion only, that `f^*α` and `f^*β` intersect properly, proved \
unconditionally and without assuming nonsingularity; the second conclusion \
`f^*(α · β) = f^*α · f^*β` is neither proved nor stated, needing the Tor formula of Stacks \
0B0W — see the implementation notes"]
theorem intersectProperly_flatPullback (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) (r s : ℕ)
    (α : CycleGroup (fieldChowSituation K) sY (r : ℤ))
    (β : CycleGroup (fieldChowSituation K) sY (s : ℤ))
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1) :
    haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    AlgebraicCycle.IntersectProperly
      (flatPullback (fieldChowSituation K) sX sY f hbase e
        (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (r : ℤ) α).1
      (flatPullback (fieldChowSituation K) sX sY f hbase e
        (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (s : ℤ) β).1 := by
  have hlft : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  obtain ⟨dY, hdY⟩ := exists_topologicalKrullDim_eq_natCast_of_isVariety K sY
  have hdX : topologicalKrullDim X = ((dY + e : ℕ) : WithBot ℕ∞) := by
    rw [he, hdY]; push_cast; rfl
  intro W' V' hW' hV'
  have hdW' : deltaDimension (fieldChowSituation K) sX W' = ((r + e : ℕ) : ℤ) := by
    have h := (mem_cyclesOfDimension (fieldChowSituation K) sX ((r : ℤ) + (e : ℤ)) _).1
      (flatPullback (fieldChowSituation K) sX sY f hbase e
        (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (r : ℤ) α).2 W' hW'
    rw [h]; push_cast; ring
  have hdV' : deltaDimension (fieldChowSituation K) sX V' = ((s + e : ℕ) : ℤ) := by
    have h := (mem_cyclesOfDimension (fieldChowSituation K) sX ((s : ℤ) + (e : ℤ)) _).1
      (flatPullback (fieldChowSituation K) sX sY f hbase e
        (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (s : ℤ) β).2 V' hV'
    rw [h]; push_cast; ring
  have hdimW' := topologicalKrullDim_coe_eq K sX W' (r + e) hdW'
  have hdimV' := topologicalKrullDim_coe_eq K sX V' (s + e) hdV'
  rw [flatPullback_apply] at hW' hV'
  obtain ⟨hαw, -⟩ := mul_ne_zero_iff.1 hW'
  obtain ⟨hβv, -⟩ := mul_ne_zero_iff.1 hV'
  obtain ⟨W, hWdef⟩ : ∃ W : IrreducibleCloseds Y, W =
      ⟨closure ({f.base W'.isIrreducible.genericPoint} : Set Y),
        isIrreducible_singleton.closure, isClosed_closure⟩ := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V : IrreducibleCloseds Y, V =
      ⟨closure ({f.base V'.isIrreducible.genericPoint} : Set Y),
        isIrreducible_singleton.closure, isClosed_closure⟩ := ⟨_, rfl⟩
  have hWgen : W.isIrreducible.genericPoint = f.base W'.isIrreducible.genericPoint :=
    genericPoint_eq_of_coe_eq_closure W _ (by rw [hWdef]; rfl)
  have hVgen : V.isIrreducible.genericPoint = f.base V'.isIrreducible.genericPoint :=
    genericPoint_eq_of_coe_eq_closure V _ (by rw [hVdef]; rfl)
  have hWV : AlgebraicGeometry.IntersectProperly W V :=
    hαβ W V (by rw [hWgen]; exact hαw) (by rw [hVgen]; exact hβv)
  have hdimW := topologicalKrullDim_coe_eq K sY W r
    ((mem_cyclesOfDimension (fieldChowSituation K) sY (r : ℤ) α.1).1 α.2 W
      (by rw [hWgen]; exact hαw))
  have hdimV := topologicalKrullDim_coe_eq K sY V s
    ((mem_cyclesOfDimension (fieldChowSituation K) sY (s : ℤ) β.1).1 β.2 V
      (by rw [hVgen]; exact hβv))
  have hsubW : (W' : Set X) ⊆ f.base ⁻¹' (W : Set Y) := by
    rw [coe_eq_closure_genericPoint W']
    refine closure_minimal (Set.singleton_subset_iff.2 ?_)
      (IsClosed.preimage f.continuous W.isClosed)
    rw [Set.mem_preimage, hWdef]
    exact subset_closure (Set.mem_singleton _)
  have hsubV : (V' : Set X) ⊆ f.base ⁻¹' (V : Set Y) := by
    rw [coe_eq_closure_genericPoint V']
    refine closure_minimal (Set.singleton_subset_iff.2 ?_)
      (IsClosed.preimage f.continuous V.isClosed)
    rw [Set.mem_preimage, hVdef]
    exact subset_closure (Set.mem_singleton _)
  have hsub : ((W' : Set X) ∩ (V' : Set X)) ⊆ f.base ⁻¹' ((W : Set Y) ∩ (V : Set Y)) := by
    rw [Set.preimage_inter]
    exact Set.inter_subset_inter hsubW hsubV
  rw [AlgebraicGeometry.intersectProperly_iff, hdimW', hdimV', hdX]
  by_cases hempty : IsEmpty ↥((W' : Set X) ∩ (V' : Set X))
  · rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 hempty]
    simp
  · obtain ⟨⟨x, hx⟩⟩ := not_isEmpty_iff.1 hempty
    have hTne : Nonempty ↥((W : Set Y) ∩ (V : Set Y)) := ⟨⟨f.base x, hsub hx⟩⟩
    have hTbot : topologicalKrullDim (↥((W : Set Y) ∩ (V : Set Y))) ≠ ⊥ := fun h ↦
      (not_isEmpty_iff.2 hTne) ((topologicalKrullDim_eq_bot_iff_isEmpty _).1 h)
    have hTle : topologicalKrullDim (↥((W : Set Y) ∩ (V : Set Y))) ≤ (dY : WithBot ℕ∞) := by
      rw [← hdY]
      exact topologicalKrullDim_subspace_le Y _
    obtain ⟨nT, hnT⟩ : ∃ nT : ℕ,
        topologicalKrullDim (↥((W : Set Y) ∩ (V : Set Y))) = (nT : WithBot ℕ∞) := by
      obtain ⟨y, hy⟩ := WithBot.ne_bot_iff_exists.mp hTbot
      have hy' : y ≤ (dY : ℕ∞) := by rw [← hy] at hTle; exact_mod_cast hTle
      have hytop : y ≠ ⊤ := fun h ↦ by simp [h] at hy'
      obtain ⟨nx, hnx⟩ := WithTop.ne_top_iff_exists.mp hytop
      exact ⟨nx, by rw [← hy, ← hnx]; rfl⟩
    have hsum : nT + dY ≤ r + s := by
      rw [AlgebraicGeometry.intersectProperly_iff, hnT, hdimW, hdimV, hdY] at hWV
      exact_mod_cast hWV
    have hpre : topologicalKrullDim (f.base ⁻¹' ((W : Set Y) ∩ (V : Set Y))) ≤
        ((nT + e : ℕ) : WithBot ℕ∞) :=
      topologicalKrullDim_preimage_le K sX sY f hbase e he
        ⟨((W : Set Y) ∩ (V : Set Y)), W.isClosed.inter V.isClosed⟩ nT (le_of_eq hnT)
    have hle : topologicalKrullDim (↥((W' : Set X) ∩ (V' : Set X))) ≤
        ((nT + e : ℕ) : WithBot ℕ∞) :=
      le_trans (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le hpre
    refine le_trans (add_le_add hle (le_refl _)) ?_
    have h1 : ((nT + e : ℕ) : WithBot ℕ∞) + ((dY + e : ℕ) : WithBot ℕ∞) =
        (((nT + e) + (dY + e) : ℕ) : WithBot ℕ∞) := by push_cast; rfl
    have h2 : ((r + e : ℕ) : WithBot ℕ∞) + ((s + e : ℕ) : WithBot ℕ∞) =
        (((r + e) + (s + e) : ℕ) : WithBot ℕ∞) := by push_cast; rfl
    rw [h1, h2]
    exact Nat.cast_le.mpr (by omega)

end Stacks.Intersection.CycleFlatPullback

end
