module

public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackCycleProduct
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaWhole

/-!
# Flat pullback and intersection products

Placeholder docstring, to be written.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Intersection.CycleFlatPullback

/-! ### The dimension of a support after flat pullback -/

/-- **The support of a pulled-back coherent sheaf.** For `f : X ⟶ Y` flat of relative dimension
`e` between varieties over `K`, if the support of `ℱ` has dimension at most `n` then the support
of `f^*ℱ` has dimension at most `n + e`: it is the inverse image of the support of `ℱ`. -/
theorem topologicalKrullDim_supp_pullback_le (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (F : Y.Modules) [F.IsFiniteType] (n : ℕ)
    (hFn : topologicalKrullDim (SheafOfModules.supp F : Set Y) ≤ (n : WithBot ℕ∞)) :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback f).obj F) : Set X) ≤
      ((n + e : ℕ) : WithBot ℕ∞) := by
  rw [Stacks.Modules.supp_pullback f F]
  exact Stacks.Intersection.CycleFlatPullback.topologicalKrullDim_preimage_le K sX sY f hbase e he
    ⟨_, SheafOfModules.isClosed_supp F⟩ n hFn

/-- **The intersection of the supports of two pulled-back coherent sheaves.** It is the inverse
image of the intersection of the two supports downstairs, so its dimension grows by at most the
relative dimension. -/
theorem topologicalKrullDim_supp_inter_pullback_le (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (F G : Y.Modules) [F.IsFiniteType] [G.IsFiniteType] (n : ℕ)
    (hFG : topologicalKrullDim (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y) ≤
      (n : WithBot ℕ∞)) :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback f).obj F) ∩
        SheafOfModules.supp ((Scheme.Modules.pullback f).obj G) : Set X) ≤
      ((n + e : ℕ) : WithBot ℕ∞) := by
  rw [Stacks.Modules.supp_pullback f F, Stacks.Modules.supp_pullback f G, ← Set.preimage_inter]
  exact Stacks.Intersection.CycleFlatPullback.topologicalKrullDim_preimage_le K sX sY f hbase e he
    ⟨_, (SheafOfModules.isClosed_supp F).inter (SheafOfModules.isClosed_supp G)⟩ n hFG

/-! ### The flat pullback of a prime cycle -/

/-- **The flat pullback of a prime cycle is the cycle of a pulled-back structure sheaf.** For `v`
a point of `Y` whose closure has delta-dimension `r`, the prime cycle `[V_v]` is the cycle
`[𝒪_{V_v}]_r` of the structure sheaf of its reduced closure (Tag 02QY), so its flat pullback is
`[f^*𝒪_{V_v}]_{r+e}` by Tag 0AZF.

This is the form in which the canonical presentation of a cycle survives flat pullback: the
pulled-back summands are cycles of coherent sheaves, which is all the bilinearity of the Section
43.17 product needs. They are not prime cycles, and need not be. -/
theorem flatPullback_primeCycle (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) (v : Y) (r : ℤ)
    (hv : schemeDeltaDimension (fieldChowSituation K)
      ((integralComponentAt v).subschemeι ≫ sY) = (r : EInt))
    (hb : letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      schemeDeltaDimension (fieldChowSituation K)
        ((reducedSupport (structureSheafAt v)).subschemeι ≫ sY) ≤ (r : EInt)) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI := AlgebraicGeometry.isCoherent_pullback f (structureSheafAt v)
    flatPullback (fieldChowSituation K) sX sY f hbase e
        (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) r
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
          (integralComponentAt v).subschemeι r) =
      cycleAssociatedToCoherentSheaf (fieldChowSituation K) sX
        ((Scheme.Modules.pullback f).obj (structureSheafAt v)) (r + (e : ℤ))
        (schemeDeltaDimension_support_pullback_le (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he)
          (structureSheafAt v) r hb) := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let := AlgebraicGeometry.isCoherent_pullback f (structureSheafAt v)
  rw [cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf (fieldChowSituation K)
    sY (integralComponentAt v).subschemeι r (le_of_eq hv)]
  exact flatPullback_cycleAssociatedToCoherentSheaf_of_isVariety K sX sY f hbase e he
    (structureSheafAt v) r hb

/-! ### The whole of Stacks 0B0Y -/

/-- **Stacks Project, Tag 0B0Y.** Let `f : X ⟶ Y` be a flat morphism of nonsingular varieties
over an algebraically closed field `K` — the chapter's convention, Tag 0AZ8 — and set
`e = dim X - dim Y`. Let `ℱ` and `𝒢` be coherent sheaves on `Y` with
`dim Supp ℱ ≤ r`, `dim Supp 𝒢 ≤ s` and `dim(Supp ℱ ∩ Supp 𝒢) ≤ r + s - dim Y`. Then the cycles
`[f^*ℱ]_{r+e}` and `[f^*𝒢]_{s+e}` intersect properly and

`f^*([ℱ]_r · [𝒢]_s) = [f^*ℱ]_{r+e} · [f^*𝒢]_{s+e}`.

`WithBot ℕ∞` has no subtraction, so `n = r + s - dim Y` is the relation `r + s = dim Y + n`. -/
@[stacks 0B0Y "the whole lemma in the case `r + s ≥ dim Y`, the expected dimension being a \
natural number `n`; every case, `r + s < dim Y` included, is \
`flatPullback_coherentSheafCycleProduct_integerDimension`. Here: both that `[f^*ℱ]_{r+e}` and \
`[f^*𝒢]_{s+e}` intersect properly \
and the identity `f^*([ℱ]_r · [𝒢]_s) = [f^*ℱ]_{r+e} · [f^*𝒢]_{s+e}`, for a flat morphism of \
nonsingular varieties over an algebraically closed field — the chapter's own convention, Tag \
0AZ8 — under the source's own three dimension bounds on `Supp ℱ`, `Supp 𝒢` and their \
intersection. `WithBot ℕ∞` has no subtraction, so `n = r + s - dim Y` is the relation \
`r + s = dim Y + n`. Both products are the Section 43.17 product of cycles \
`AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct` (Tag 0B08), so this is the \
source's statement and not merely its Tor-sheaf shadow: the passage between the two is Tag \
0B0W, applied downstairs and upstairs. The flat pullback of the alternating sum of Tor cycles, \
which is the other half of the source's proof, is \
`Stacks.Intersection.FlatPullback.flatPullback_intersectionProductCycleGroup_eq_pullbackSheaves`."]
theorem flatPullback_coherentSheafCycleProduct (K : Type u) [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    [IsVariety K sX] [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X)
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX)
    (F G : Y.Modules) (hFc : _root_.SheafOfModules.IsCoherent F)
    (hGc : _root_.SheafOfModules.IsCoherent G) (r s n dY e : ℕ)
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (hrs : r + s = dY + n)
    (hFr : topologicalKrullDim (SheafOfModules.supp F : Set Y) ≤ (r : WithBot ℕ∞))
    (hGs : topologicalKrullDim (SheafOfModules.supp G : Set Y) ≤ (s : WithBot ℕ∞))
    (hFG : topologicalKrullDim (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y) ≤
      (n : WithBot ℕ∞)) :
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
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (n : ℤ)
          ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY (n : ℤ)
              (coherentSheafCycle (fieldChowSituation K) sY F (r : ℤ) hFrY)
              (coherentSheafCycle (fieldChowSituation K) sY G (s : ℤ) hGsY),
            torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sY hY
              (n : ℤ) _ _⟩).1 =
        torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((n + e : ℕ) : ℤ)
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
  have hFGXtop := topologicalKrullDim_supp_inter_pullback_le K sX sY f hbase e he F G n hFG
  have hdX : topologicalKrullDim X = ((dY + e : ℕ) : WithBot ℕ∞) := by
    rw [he, hdY]; push_cast; rfl
  have hrs' : (r + e) + (s + e) = (dY + e) + (n + e) := by omega
  obtain ⟨hpropX, hidX⟩ := Stacks.Intersection.ReductionToDiagonal.torFormula K sX hX
    ((Scheme.Modules.pullback f).obj F) ((Scheme.Modules.pullback f).obj G)
    (AlgebraicGeometry.isCoherent_pullback f F) (AlgebraicGeometry.isCoherent_pullback f G)
    (r + e) (s + e) (n + e) (dY + e) hdX hrs' hFrXtop hGsXtop hFGXtop
  obtain ⟨-, hidY⟩ := Stacks.Intersection.ReductionToDiagonal.torFormula K sY hY F G hFc hGc
    r s n dY hdY hrs hFr hGs hFG
  refine ⟨hpropX, ?_⟩
  have harg : (⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY (n : ℤ)
          (coherentSheafCycle (fieldChowSituation K) sY F (r : ℤ) _)
          (coherentSheafCycle (fieldChowSituation K) sY G (s : ℤ) _),
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sY hY
          (n : ℤ) _ _⟩ : CycleGroup (fieldChowSituation K) sY (n : ℤ)) =
      intersectionProductCycleGroup (fieldChowSituation K) sY hY F G hFc hGc (n : ℤ) _ :=
    Subtype.ext hidY
  rw [harg,
    Stacks.Intersection.FlatPullback.flatPullback_intersectionProductCycleGroup_eq_pullbackSheaves
      K sX sY hX hY f hbase e he F G hFc hGc (n : ℤ) _, hidX]
  rfl

/-! ### The flat pullback of a single Section 43.14 product -/

/-- **The flat pullback of the product of two prime cycles.** For `v`, `w` points of `Y` whose
closures have delta-dimensions `r` and `s` and intersect properly, the Section 43.17 product of
the flat pullbacks `f^*[V_v]` and `f^*[W_w]` is the pulled-back summand
`[f^*𝒪_{V_v}]_{r+e} · [f^*𝒪_{W_w}]_{s+e}`.

This is the pairwise step of Tag 0B0Z: by Tag 0B0W upstairs the product of the two sheaf cycles
is the alternating sum of the `Tor` cycles of the two pulled-back structure sheaves, which is
exactly the summand that `flatPullback_torFormulaCycleIntersectionProduct` produces. -/
theorem torFormulaCycleIntersectionProduct_flatPullback_primeCycle (K : Type u) [Field K]
    [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    [IsVariety K sX] [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X)
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX)
    (e dY r s n : ℕ) (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (hrs : r + s = dY + n) (v w : Y)
    (hv : relativeDimension (fieldChowSituation K).dimensionFunction sY v = (r : ℤ))
    (hw : relativeDimension (fieldChowSituation K).dimensionFunction sY w = (s : ℤ))
    (hprop : AlgebraicGeometry.IntersectProperly
      (⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩ : IrreducibleCloseds Y)
      ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((n : ℤ) + (e : ℤ))
        (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (r : ℤ)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
            (integralComponentAt v).subschemeι (r : ℤ))).1
        (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (s : ℤ)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
            (integralComponentAt w).subschemeι (s : ℤ))).1 =
      flatPullbackSubvarietyProductTotal K sX sY hX hY f hbase e he (n : ℤ) v w := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := isCoherent_structureSheafAt v
  have := isCoherent_structureSheafAt w
  have := isFiniteType_of_isCoherent (structureSheafAt v)
  have := isFiniteType_of_isCoherent (structureSheafAt w)
  have := AlgebraicGeometry.isCoherent_pullback f (structureSheafAt v)
  have := AlgebraicGeometry.isCoherent_pullback f (structureSheafAt w)
  -- the support of the structure sheaf of a point closure is that closure
  have hsupp : ∀ z : Y, SheafOfModules.supp (structureSheafAt z) = closure ({z} : Set Y) := by
    intro z
    rw [show structureSheafAt z =
      (Scheme.Modules.pushforward (integralComponentAt z).subschemeι).obj
        (Stacks.Ample.unitModule _) from rfl, supp_pushforwardStructureSheaf,
      Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
  have hdimv : topologicalKrullDim (closure ({v} : Set Y)) = (r : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_singleton_eq K sY v, hv]; simp
  have hdimw : topologicalKrullDim (closure ({w} : Set Y)) = (s : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_singleton_eq K sY w, hw]; simp
  have hsum : topologicalKrullDim (closure ({v} : Set Y)) +
      topologicalKrullDim (closure ({w} : Set Y)) = (dY : WithBot ℕ∞) + (n : WithBot ℕ∞) := by
    rw [hdimv, hdimw, ← Nat.cast_add, ← Nat.cast_add, hrs]
  have hFrtop : topologicalKrullDim (SheafOfModules.supp (structureSheafAt v) : Set Y) ≤
      (r : WithBot ℕ∞) := by rw [hsupp v, hdimv]
  have hGstop : topologicalKrullDim (SheafOfModules.supp (structureSheafAt w) : Set Y) ≤
      (s : WithBot ℕ∞) := by rw [hsupp w, hdimw]
  have hFGtop : topologicalKrullDim (SheafOfModules.supp (structureSheafAt v) ∩
      SheafOfModules.supp (structureSheafAt w) : Set Y) ≤ (n : WithBot ℕ∞) := by
    rw [hsupp v, hsupp w]
    exact topologicalKrullDim_inter_le_of_intersectProperly_of_add_eq hprop hdY hsum
  have hbd : TorSupportBound (fieldChowSituation K) sY hY (n : ℤ) v w :=
    torSupportBound_of_intersectProperly K sY hY v w hdY hsum hprop
  have hdX : topologicalKrullDim X = ((dY + e : ℕ) : WithBot ℕ∞) := by
    rw [he, hdY]; push_cast; rfl
  have hrs' : (r + e) + (s + e) = (dY + e) + (n + e) := by omega
  obtain ⟨-, hidX⟩ := Stacks.Intersection.ReductionToDiagonal.torFormula K sX hX
    ((Scheme.Modules.pullback f).obj (structureSheafAt v))
    ((Scheme.Modules.pullback f).obj (structureSheafAt w))
    (AlgebraicGeometry.isCoherent_pullback f (structureSheafAt v))
    (AlgebraicGeometry.isCoherent_pullback f (structureSheafAt w))
    (r + e) (s + e) (n + e) (dY + e) hdX hrs'
    (topologicalKrullDim_supp_pullback_le K sX sY f hbase e he (structureSheafAt v) r hFrtop)
    (topologicalKrullDim_supp_pullback_le K sX sY f hbase e he (structureSheafAt w) s hGstop)
    (topologicalKrullDim_supp_inter_pullback_le K sX sY f hbase e he (structureSheafAt v)
      (structureSheafAt w) n hFGtop)
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
    flatPullbackSubvarietyProductTotal_eq_of_bound K sX sY hX hY f hbase e he (n : ℤ) v w hbd]
  exact hidX

/-! ### The whole of Stacks 0B0Z -/

/-- **Stacks Project, Tag 0B0Z.** Let `f : X ⟶ Y` be a flat morphism of nonsingular varieties
over an algebraically closed field `K` — the chapter's convention, Tag 0AZ8 — with
`dim X = dim Y + e`. Let `α` be an `r`-cycle and `β` an `s`-cycle on `Y` which intersect
properly. Then `f^*α` and `f^*β` intersect properly and

`f^*(α · β) = f^*α · f^*β`. -/
@[stacks 0B0Z "the whole lemma in the case `r + s ≥ dim Y`, the product being graded by a \
natural number `n`; every case, `r + s < dim Y` included, is \
`flatPullback_torFormulaCycleIntersectionProduct_eq_integerDimension`. Here: both that `f^*α` \
and `f^*β` intersect properly and the identity \
`f^*(α · β) = f^*α · f^*β`, for a flat morphism of nonsingular varieties over an algebraically \
closed field — the chapter's own convention, Tag 0AZ8 — with `dim X = dim Y + e`. The products \
are the Section 43.17 product of cycles of Tag 0B08, graded so that an `r`-cycle and an \
`s`-cycle multiply into dimension `n` with `r + s = dim Y + n`, `WithBot ℕ∞` having no \
subtraction. The source's `[V] = [𝒪_V]_r` is \
`AlgebraicGeometry.TorFormula.coherentSheafCycle_structureSheafAt` and its \
`f^*[V] = [f^*𝒪_V]_{r+e}` is Tag 0AZF, so the pulled-back components are cycles of coherent \
sheaves; bilinearity of the product then reduces the identity to one pair of components, where \
it is Tag 0B0W upstairs."]
theorem flatPullback_torFormulaCycleIntersectionProduct_eq (K : Type u) [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    [IsVariety K sX] [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X)
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX)
    (e dY r s n : ℕ) (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (hrs : r + s = dY + n)
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
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (n : ℤ)
          ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY (n : ℤ) α.1 β.1,
            torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sY hY
              (n : ℤ) α.1 β.1⟩).1 =
        torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((n : ℤ) + (e : ℤ))
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
  set P : Y → CycleGroup (fieldChowSituation K) sY (r : ℤ) := fun v =>
    cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
      (integralComponentAt v).subschemeι (r : ℤ) with hPdef
  set Q : Y → CycleGroup (fieldChowSituation K) sY (s : ℤ) := fun w =>
    cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
      (integralComponentAt w).subschemeι (s : ℤ) with hQdef
  have hα : (Function.support α.1).Finite := finite_support_of_compactSpace α.1
  have hβ : (Function.support β.1).Finite := finite_support_of_compactSpace β.1
  -- a pulled-back cycle, as a finite sum of cycles of pulled-back structure sheaves
  have hpull : ∀ (m : ℕ) (γ : CycleGroup (fieldChowSituation K) sY (m : ℤ))
      (hγ : (Function.support γ.1).Finite),
      (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (m : ℤ) γ).1 =
        ∑ v ∈ hγ.toFinset, γ.1 v •
          (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (m : ℤ)
            (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
              (integralComponentAt v).subschemeι (m : ℤ))).1 := by
    intro m γ hγ
    have h1 : flatPullback (fieldChowSituation K) sX sY f hbase e hrel (m : ℤ) γ =
        ∑ v ∈ hγ.toFinset, γ.1 v •
          flatPullback (fieldChowSituation K) sX sY f hbase e hrel (m : ℤ)
            (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
              (integralComponentAt v).subschemeι (m : ℤ)) := by
      conv_lhs => rw [cycle_eq_sum_zsmul_primeCycles γ hγ]
      rw [map_sum]
      exact Finset.sum_congr rfl fun v _ => map_zsmul _ _ _
    rw [h1]
    simp
  -- the pairwise identity at each pair of components
  have hpair : ∀ v ∈ hα.toFinset, ∀ w ∈ hβ.toFinset,
      torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((n : ℤ) + (e : ℤ))
          (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (r : ℤ) (P v)).1
          (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (s : ℤ) (Q w)).1 =
        flatPullbackSubvarietyProductTotal K sX sY hX hY f hbase e he (n : ℤ) v w := by
    intro v hv w hw
    exact torFormulaCycleIntersectionProduct_flatPullback_primeCycle K sX sY hX hY f hbase e dY
      r s n hdY he hrs v w
      ((mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) sY (r : ℤ) α.1).1 α.2 v
        (hα.mem_toFinset.1 hv))
      ((mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) sY (s : ℤ) β.1).1 β.2 w
        (hβ.mem_toFinset.1 hw))
      (hαβ _ _ (by rw [genericPoint_closure_singleton]; exact hα.mem_toFinset.1 hv)
        (by rw [genericPoint_closure_singleton]; exact hβ.mem_toFinset.1 hw))
  -- the right-hand side, expanded by bilinearity
  have hRHS : torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((n : ℤ) + (e : ℤ))
        (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (r : ℤ) α).1
        (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (s : ℤ) β).1 =
      ∑ v ∈ hα.toFinset, ∑ w ∈ hβ.toFinset, (α.1 v * β.1 w) •
        flatPullbackSubvarietyProductTotal K sX sY hX hY f hbase e he (n : ℤ) v w := by
    show cycleIntersectionProduct (torFormulaSubvarietyProductTotal (fieldChowSituation K) sX hX
        ((n : ℤ) + (e : ℤ))) _ _ = _
    rw [hpull r α hα, hpull s β hβ, cycleIntersectionProduct_sum_left]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [cycleIntersectionProduct_zsmul_left _ _ (finite_support_of_compactSpace _)
      (finite_support_of_compactSpace _), cycleIntersectionProduct_sum_right, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [cycleIntersectionProduct_zsmul_right _ _ (finite_support_of_compactSpace _)
      (finite_support_of_compactSpace _), smul_smul]
    exact congrArg (fun z => (α.1 v * β.1 w) • z) (hpair v hv w hw)
  -- the left-hand side, from the double sum over pairs downstairs
  have hsub : Function.support (fun q : Y × Y => (α.1 q.1 * β.1 q.2) •
      flatPullbackSubvarietyProductTotal K sX sY hX hY f hbase e he (n : ℤ) q.1 q.2) ⊆
      ↑(hα.toFinset ×ˢ hβ.toFinset) := by
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨hα.mem_toFinset.2 ?_, hβ.mem_toFinset.2 ?_⟩)
    · exact fun h0 => hq (by rw [h0, zero_mul, zero_smul])
    · exact fun h0 => hq (by rw [h0, mul_zero, zero_smul])
  rw [hRHS, flatPullback_torFormulaCycleIntersectionProduct K sX sY hX hY f hbase e he (n : ℤ)
    α.1 β.1, finsum_eq_sum_of_support_subset _ hsub, Finset.sum_product]

end Stacks.Intersection.CycleFlatPullback

end
