module

public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackSubvarietyProduct

/-!
# Flat pullback through the double sum defining the product of two cycles

Let `f : X ⟶ Y` be a flat morphism of nonsingular varieties over a field with
`dim X = dim Y + e`, and let `α` and `β` be cycles on `Y`. The intersection product `α · β` of
Section 43.17 is the bilinear extension

`α · β = ∑_{(v, w)} α(v) β(w) (V_v · W_w)`

of the Section 43.14 product of two closed subvarieties, which is
`AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct` of Tag 0B08. This file shows

`f^*(α · β) = ∑_{(v, w)} α(v) β(w) ([f^*𝒪_{V_v}]_{n+e} · [f^*𝒪_{W_w}]_{n+e})`,

the sum still indexed by the pairs of components **downstairs** and each summand the Tor-formula
product of the two pulled-back structure sheaves.

## Main definitions

* `Stacks.Intersection.CycleFlatPullback.flatPullbackSubvarietyProductTotal` — the summand
  `[f^*𝒪_{V_v}]_{n+e} · [f^*𝒪_{W_w}]_{n+e}` of the displayed sum, read at every pair of points of
  `Y`, and the zero cycle at a pair whose `Tor` sheaves downstairs have too big a support.

## Main results

* `AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct_mem_cyclesOfDimension` — the
  product of two cycles is an `n`-cycle.
* `Stacks.Intersection.CycleFlatPullback.flatPullback_torFormulaCycleIntersectionProduct` — the
  displayed identity, with no hypothesis beyond flatness and the relative dimension.
* `Stacks.Intersection.CycleFlatPullback.flatPullbackSubvarietyProductTotal_eq_of_bound` and
  `CycleFlatPullback.flatPullbackSubvarietyProductTotal_eq_of_intersectProperly` — at a pair of
  components of two properly intersecting cycles the summand is the Tor-formula product of the
  pulled-back structure sheaves.

## References

* [Stacks Project, Lemma 43.21.2 (Tag 0B0Z)](https://stacks.math.columbia.edu/tag/0B0Z)
* [Stacks Project, Lemma 43.21.1 (Tag 0B0Y)](https://stacks.math.columbia.edu/tag/0B0Y)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
* [Stacks Project, Tag 0B0W](https://stacks.math.columbia.edu/tag/0B0W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace AlgebraicGeometry.TorFormula

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The product of two cycles is an `n`-cycle -/

/-- The Section 43.14 product read at a pair of points is an `n`-cycle. -/
theorem torFormulaSubvarietyProductTotal_mem_cyclesOfDimension
    (C : Stacks.Chow.ChowSituation.{u}) {Y : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p]
    [IsLocallyNoetherian Y] (hY : AlgebraicGeometry.IsRegular Y) (n : ℤ) (v w : Y) :
    torFormulaSubvarietyProductTotal C p hY n v w ∈ cyclesOfDimension C p n := by
  by_cases h : TorSupportBound C p hY n v w
  · rw [torFormulaSubvarietyProductTotal_eq_of_bound C p hY n h]
    exact intersectionProductCycle_mem_cyclesOfDimension C p hY (structureSheafAt v)
      (structureSheafAt w) (isCoherent_structureSheafAt v) (isCoherent_structureSheafAt w) n h
  · rw [torFormulaSubvarietyProductTotal_eq_zero C p hY n h]
    exact AddSubgroup.zero_mem _

/-- The intersection product of two cycles is an `n`-cycle. -/
theorem torFormulaCycleIntersectionProduct_mem_cyclesOfDimension
    (C : Stacks.Chow.ChowSituation.{u}) {Y : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p]
    [IsLocallyNoetherian Y] (hY : AlgebraicGeometry.IsRegular Y) (n : ℤ)
    (α β : AlgebraicCycle Y ℤ) :
    torFormulaCycleIntersectionProduct C p hY n α β ∈ cyclesOfDimension C p n := by
  rw [torFormulaCycleIntersectionProduct, cycleIntersectionProduct]
  refine finsum_induction _ (AddSubgroup.zero_mem _)
    (fun a b ha hb ↦ AddSubgroup.add_mem _ ha hb) fun q ↦ ?_
  exact AddSubgroup.zsmul_mem _
    (torFormulaSubvarietyProductTotal_mem_cyclesOfDimension C p hY n q.1 q.2) _

/-- The summand of `α · β` indexed by a pair of points, read in the group `Z_n(Y)` of
`n`-cycles. -/
def torFormulaCycleProductSummandGroup (C : Stacks.Chow.ChowSituation.{u}) {Y : Scheme.{u}}
    (p : Y ⟶ C.S) [LocallyOfFiniteType p] [IsLocallyNoetherian Y]
    (hY : AlgebraicGeometry.IsRegular Y) (n : ℤ) (α β : AlgebraicCycle Y ℤ) (q : Y × Y) :
    CycleGroup C p n :=
  (α q.1 * β q.2) • (⟨torFormulaSubvarietyProductTotal C p hY n q.1 q.2,
    torFormulaSubvarietyProductTotal_mem_cyclesOfDimension C p hY n q.1 q.2⟩ : CycleGroup C p n)

/-- On a quasi-compact `Y`, only finitely many summands of `α · β` are nonzero. -/
theorem hasFiniteSupport_torFormulaCycleProductSummandGroup
    (C : Stacks.Chow.ChowSituation.{u}) {Y : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p]
    [IsLocallyNoetherian Y] [CompactSpace Y] (hY : AlgebraicGeometry.IsRegular Y) (n : ℤ)
    (α β : AlgebraicCycle Y ℤ) :
    Function.HasFiniteSupport (torFormulaCycleProductSummandGroup C p hY n α β) := by
  refine ((finite_support_of_compactSpace α).prod (finite_support_of_compactSpace β)).subset ?_
  intro q hq
  refine ⟨?_, ?_⟩ <;> by_contra h <;> simp only [Function.notMem_support] at h <;>
    exact hq (by simp [torFormulaCycleProductSummandGroup, h])

/-- The intersection product of two cycles, read in `Z_n(Y)`, is the sum over pairs of points of
the summands of the double sum. -/
theorem torFormulaCycleIntersectionProduct_eq_finsum (C : Stacks.Chow.ChowSituation.{u})
    {Y : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p] [IsLocallyNoetherian Y]
    [CompactSpace Y] (hY : AlgebraicGeometry.IsRegular Y) (n : ℤ) (α β : AlgebraicCycle Y ℤ) :
    (⟨torFormulaCycleIntersectionProduct C p hY n α β,
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension C p hY n α β⟩ :
          CycleGroup C p n) =
      ∑ᶠ q : Y × Y, torFormulaCycleProductSummandGroup C p hY n α β q :=
  Subtype.ext (AddMonoidHom.map_finsum (cyclesOfDimension C p n).subtype
    (hasFiniteSupport_torFormulaCycleProductSummandGroup C p hY n α β)).symm

end AlgebraicGeometry.TorFormula

namespace Stacks.Intersection.CycleFlatPullback

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The pulled-back summand -/

/-- The flat pullback of the Section 43.14 product of the reduced closures of two points of `Y`,
read at every pair of points: the Tor-formula product
`[f^*𝒪_{V_v}]_{n+e} · [f^*𝒪_{W_w}]_{n+e}` of the two pulled-back structure sheaves at a pair
whose `Tor` sheaves downstairs have supports of delta-dimension at most `n`, and the zero cycle
at a pair where they do not. -/
def flatPullbackSubvarietyProductTotal (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (hX : AlgebraicGeometry.IsRegular X) (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y)
    [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) (n : ℤ) (v w : Y) :
    AlgebraicCycle X ℤ :=
  open Classical in
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  if h : TorSupportBound (fieldChowSituation K) sY hY n v w then
    intersectionProductCycle (fieldChowSituation K) sX hX
      ((Scheme.Modules.pullback f).obj (structureSheafAt v))
      ((Scheme.Modules.pullback f).obj (structureSheafAt w))
      (isCoherent_pullback f (structureSheafAt v))
      (isCoherent_pullback f (structureSheafAt w)) (n + (e : ℤ))
      (Stacks.Intersection.FlatPullback.schemeDeltaDimension_torSheaf_flatPullback_le
        K sX sY hX hY f hbase e he (structureSheafAt v) (structureSheafAt w)
        (isCoherent_structureSheafAt v) (isCoherent_structureSheafAt w) n h)
  else 0

/-- At a pair of points whose `Tor` sheaves downstairs have supports of delta-dimension at most
`n`, the pulled-back summand is the Tor-formula product of the two pulled-back structure
sheaves. -/
theorem flatPullbackSubvarietyProductTotal_eq_of_bound (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (hX : AlgebraicGeometry.IsRegular X) (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y)
    [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) (n : ℤ) (v w : Y)
    (h : haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      TorSupportBound (fieldChowSituation K) sY hY n v w) :
    haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    flatPullbackSubvarietyProductTotal K sX sY hX hY f hbase e he n v w =
      intersectionProductCycle (fieldChowSituation K) sX hX
        ((Scheme.Modules.pullback f).obj (structureSheafAt v))
        ((Scheme.Modules.pullback f).obj (structureSheafAt w))
        (isCoherent_pullback f (structureSheafAt v))
        (isCoherent_pullback f (structureSheafAt w)) (n + (e : ℤ))
        (Stacks.Intersection.FlatPullback.schemeDeltaDimension_torSheaf_flatPullback_le
          K sX sY hX hY f hbase e he (structureSheafAt v) (structureSheafAt w)
          (isCoherent_structureSheafAt v) (isCoherent_structureSheafAt w) n h) :=
  dite_eq_left h

/-- At a pair of points some `Tor` sheaf of which has too big a support downstairs, the
pulled-back summand is the zero cycle. -/
theorem flatPullbackSubvarietyProductTotal_eq_zero (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (hX : AlgebraicGeometry.IsRegular X) (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y)
    [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) (n : ℤ) (v w : Y)
    (h : haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      ¬ TorSupportBound (fieldChowSituation K) sY hY n v w) :
    flatPullbackSubvarietyProductTotal K sX sY hX hY f hbase e he n v w = 0 :=
  dite_eq_right h

/-- For cycles `α` and `β` on `Y` which intersect properly, with `dim Y = m` and the dimensions
of the closures of a component of `α` and a component of `β` summing to `m + n`, the pulled-back
summand at any pair of components is the Tor-formula product of the two pulled-back structure
sheaves. -/
theorem flatPullbackSubvarietyProductTotal_eq_of_intersectProperly (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX]
    [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X) (hY : AlgebraicGeometry.IsRegular Y)
    (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) {m n : ℕ}
    {α β : AlgebraicCycle Y ℤ} (hαβ : AlgebraicCycle.IntersectProperly α β)
    (hdimY : topologicalKrullDim Y = (m : WithBot ℕ∞))
    (hdim : ∀ v ∈ Function.support α, ∀ w ∈ Function.support β,
      topologicalKrullDim (closure ({v} : Set Y)) +
        topologicalKrullDim (closure ({w} : Set Y)) = (m : WithBot ℕ∞) + (n : WithBot ℕ∞))
    (v : Y) (hv : α v ≠ 0) (w : Y) (hw : β w ≠ 0) :
    haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    ∃ hb, flatPullbackSubvarietyProductTotal K sX sY hX hY f hbase e he (n : ℤ) v w =
      intersectionProductCycle (fieldChowSituation K) sX hX
        ((Scheme.Modules.pullback f).obj (structureSheafAt v))
        ((Scheme.Modules.pullback f).obj (structureSheafAt w))
        (isCoherent_pullback f (structureSheafAt v))
        (isCoherent_pullback f (structureSheafAt w)) ((n : ℤ) + (e : ℤ)) hb := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hbd : TorSupportBound (fieldChowSituation K) sY hY (n : ℤ) v w :=
    torSupportBound_of_intersectProperly K sY hY v w hdimY
      (hdim v (Function.mem_support.2 hv) w (Function.mem_support.2 hw))
      (hαβ _ _ (by rwa [genericPoint_closure_singleton])
        (by rwa [genericPoint_closure_singleton]))
  exact ⟨_, flatPullbackSubvarietyProductTotal_eq_of_bound K sX sY hX hY f hbase e he (n : ℤ)
    v w hbd⟩

/-! ### Flat pullback through the double sum -/

/-- **Flat pullback through the double sum defining `α · β`.** Let `f : X ⟶ Y` be a flat morphism
of nonsingular varieties over a field `K` with `dim X = dim Y + e`, and let `α` and `β` be cycles
on `Y`. Then

`f^*(α · β) = ∑_{(v, w)} α(v) β(w) ([f^*𝒪_{V_v}]_{n+e} · [f^*𝒪_{W_w}]_{n+e})`,

the sum over pairs of components of `α` and `β` on `Y` of the Tor-formula products of the
pulled-back structure sheaves. -/
theorem flatPullback_torFormulaCycleIntersectionProduct (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (hX : AlgebraicGeometry.IsRegular X) (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y)
    [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) (n : ℤ)
    (α β : AlgebraicCycle Y ℤ) :
    haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    (flatPullback (fieldChowSituation K) sX sY f hbase e
        (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) n
        ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY n α β,
          torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sY hY
            n α β⟩).1 =
      ∑ᶠ q : Y × Y, (α q.1 * β q.2) •
        flatPullbackSubvarietyProductTotal K sX sY hX hY f hbase e he n q.1 q.2 := by
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hfin := hasFiniteSupport_torFormulaCycleProductSummandGroup (fieldChowSituation K) sY hY
    n α β
  have key : ∀ q : Y × Y,
      (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) n
          (torFormulaCycleProductSummandGroup (fieldChowSituation K) sY hY n α β q)).1 =
        (α q.1 * β q.2) •
          flatPullbackSubvarietyProductTotal K sX sY hX hY f hbase e he n q.1 q.2 := by
    intro q
    rw [torFormulaCycleProductSummandGroup, map_zsmul, AddSubgroupClass.coe_zsmul]
    congr 1
    by_cases h : TorSupportBound (fieldChowSituation K) sY hY n q.1 q.2
    · have harg : (⟨torFormulaSubvarietyProductTotal (fieldChowSituation K) sY hY n q.1 q.2,
            torFormulaSubvarietyProductTotal_mem_cyclesOfDimension (fieldChowSituation K) sY hY
              n q.1 q.2⟩ : CycleGroup (fieldChowSituation K) sY n) =
          ⟨torSubvarietyProductOfBound (fieldChowSituation K) sY hY n h,
            intersectionProductCycle_mem_cyclesOfDimension (fieldChowSituation K) sY hY
              (structureSheafAt q.1) (structureSheafAt q.2) (isCoherent_structureSheafAt q.1)
              (isCoherent_structureSheafAt q.2) n h⟩ :=
        Subtype.ext (torFormulaSubvarietyProductTotal_eq_of_bound (fieldChowSituation K) sY hY
          n h)
      rw [harg, flatPullback_torSubvarietyProductOfBound K sX sY hX hY f hbase e he n q.1 q.2 h,
        flatPullbackSubvarietyProductTotal_eq_of_bound K sX sY hX hY f hbase e he n q.1 q.2 h]
    · have harg : (⟨torFormulaSubvarietyProductTotal (fieldChowSituation K) sY hY n q.1 q.2,
            torFormulaSubvarietyProductTotal_mem_cyclesOfDimension (fieldChowSituation K) sY hY
              n q.1 q.2⟩ : CycleGroup (fieldChowSituation K) sY n) = 0 :=
        Subtype.ext (torFormulaSubvarietyProductTotal_eq_zero (fieldChowSituation K) sY hY n h)
      rw [harg, map_zero,
        flatPullbackSubvarietyProductTotal_eq_zero K sX sY hX hY f hbase e he n q.1 q.2 h]
      rfl
  have hfin' : Function.HasFiniteSupport (fun q : Y × Y =>
      flatPullback (fieldChowSituation K) sX sY f hbase e
        (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) n
        (torFormulaCycleProductSummandGroup (fieldChowSituation K) sY hY n α β q)) := by
    exact hfin.subset (Function.support_comp_subset (map_zero _) _)
  have hval : ((∑ᶠ q : Y × Y, flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) n
          (torFormulaCycleProductSummandGroup (fieldChowSituation K) sY hY n α β q)).1 :
        AlgebraicCycle X ℤ) =
      ∑ᶠ q : Y × Y, (flatPullback (fieldChowSituation K) sX sY f hbase e
        (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) n
        (torFormulaCycleProductSummandGroup (fieldChowSituation K) sY hY n α β q)).1 :=
    AddMonoidHom.map_finsum
      (cyclesOfDimension (fieldChowSituation K) sX (n + (e : ℤ))).subtype hfin'
  rw [torFormulaCycleIntersectionProduct_eq_finsum (fieldChowSituation K) sY hY n α β,
    AddMonoidHom.map_finsum _ hfin, hval]
  exact finsum_congr key

end Stacks.Intersection.CycleFlatPullback

end
