module

public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackWhole
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaWhole
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.SurjectiveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Multiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.Unconditional
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.NegativeDimensionCycles
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula for a flat proper morphism, for cycles

Let `f : X ⟶ Y` be a flat proper morphism of nonsingular varieties over an algebraically closed
field — the chapter's convention, Tag 0AZ8 — and set `e = dim X - dim Y`. Let `α` be an
`r`-cycle on `X` and `β` an `s`-cycle on `Y`, and assume that `α` and `f^*β` intersect properly.
Then `f_*α` and `β` intersect properly and

`f_*(α) · β = f_*(α · f^*β)`.

This is Stacks Tag 0B10 in full, for arbitrary cycles, with the intersection product of cycles of
Tag 0B08.

## Main results

* `Stacks.Intersection.ProjectionFormula.exists_specializes_relativeDimension_eq_add_of_flat` —
  every point of `f⁻¹(W)`, for `W` the closure of a point `w`, specializes from a point over `w`
  of delta-dimension `δ(w) + e`: the source's "`f⁻¹(W)` has pure dimension `s + e`".
* `Stacks.Intersection.ProjectionFormula.topologicalKrullDim_closure_inter_preimage_le` — for
  components `V` of `α` and `W` of `β`, `dim (V ∩ f⁻¹W) ≤ r + s - dim Y`.
* `Stacks.Intersection.ProjectionFormula.properPushforward_coherentSheafCycleProduct` — the
  identity for `α = [ℱ]_r` and `β = [𝒢]_s`, with the products of cycles of Tag 0B08.
* `Stacks.Intersection.ProjectionFormula.closure_inter_preimage_eq_empty` — when
  `r + s < dim Y`, `V ∩ f⁻¹W` is empty.
* `Stacks.Intersection.ProjectionFormula.properPushforward_torFormulaCycleIntersectionProduct_eq`
  — **Tag 0B10**, both conclusions, for arbitrary cycles and every `r`, `s`, the dimension
  `n = r + s - dim Y` of the products being an integer.

## Implementation notes

The source reduces by linearity to `α = [V]` and `β = [W]`. So does the proof here: on a variety
a cycle is a finite sum of prime cycles (`Stacks.Chow.cycle_eq_sum_zsmul_primeCycles`), the
product of cycles is bilinear, proper pushforward and flat pullback are additive, and
`f^*[W] = [f^*𝒪_W]_{s+e}` (Stacks 0AZF). For one pair, Tag 0B0W upstairs and downstairs turns the
two products of cycles into the alternating sums of Tor cycles of Stacks 0AZR, and between those
the sheaf form `properPushforward_intersectionProductCycleGroup_unconditional` (in
`Stacks.Intersection.ProjectionFormula`) applies. Tag 0B0W asks for
`dim (V ∩ f⁻¹W) ≤ r + s - dim Y`. The source gets it from the purity of
`f⁻¹(W)`: every component of `f⁻¹(W)` dominates `W` and has dimension `s + e`, so it is a component
of `f^*β`, and it meets `V` properly.

## References

* [Stacks Project, Lemma 43.22.1 (Tag 0B10)](https://stacks.math.columbia.edu/tag/0B10)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
* [Stacks Project, Tag 0B0W](https://stacks.math.columbia.edu/tag/0B0W)
* [Stacks Project, Tag 0AZ8](https://stacks.math.columbia.edu/tag/0AZ8)
* [Stacks Project, Tag 0AZD](https://stacks.math.columbia.edu/tag/0AZD)
* [Stacks Project, Tag 0AZF](https://stacks.math.columbia.edu/tag/0AZF)
* [Stacks Project, Tag 02FX](https://stacks.math.columbia.edu/tag/02FX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Intersection.ProjectionFormula

open Stacks.Chow AlgebraicGeometry.TorFormula

/-- A point in the support of a `k`-cycle has delta-dimension `k`. -/
private theorem relativeDimension_eq_of_apply_ne_zero (K : Type u) [Field K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) [IsVariety K sX] {k : ℤ} (c : CycleGroup (fieldChowSituation K) sX k)
    {x : X} (hx : c.1 x ≠ 0) :
    relativeDimension (fieldChowSituation K).dimensionFunction sX x = k :=
  (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) sX k c.1).1 c.2 x hx

/-- The closure of a point of delta-dimension `r` has topological Krull dimension `r`. -/
private theorem topologicalKrullDim_closure_singleton_eq_of_relativeDimension_eq (K : Type u)
    [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [IsVariety K sX] {x : X} {r : ℕ}
    (hx : relativeDimension (fieldChowSituation K).dimensionFunction sX x = (r : ℤ)) :
    topologicalKrullDim (closure ({x} : Set X)) = (r : WithBot ℕ∞) := by
  rw [topologicalKrullDim_closure_singleton_eq K sX x, hx, Int.toNat_natCast]

/-- If `dim Y = dY` and `dim X = dim Y + e`, then `dim X = dY + e`. -/
private theorem topologicalKrullDim_eq_natCast_add {X Y : Scheme.{u}} {dY e : ℕ}
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) :
    topologicalKrullDim X = ((dY + e : ℕ) : WithBot ℕ∞) := by
  rw [he, hdY]; push_cast; rfl

/-- Along a proper map, `closure {y} ∩ closure {w}` is covered by the image of
`closure {x} ∩ f⁻¹ (closure {w})` for any `x` over `y`. -/
private theorem closure_inter_subset_image_closure_inter_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] {x : X} {y : Y} (w : Y) (hxy : f.base x = y) :
    closure ({y} : Set Y) ∩ closure {w} ⊆
      f.base '' (closure ({x} : Set X) ∩ f.base ⁻¹' closure {w}) := by
  rintro p ⟨hpy, hpw⟩
  have himage : closure ({y} : Set Y) ⊆ f.base '' closure ({x} : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr ⟨x, subset_closure rfl, hxy⟩)
      (f.isClosedMap _ isClosed_closure)
  obtain ⟨q, hq, rfl⟩ := himage hpy
  exact ⟨q, ⟨hq, hpw⟩, rfl⟩

/-- A point `y` in the support of a proper pushforward has a preimage `x` in the support of the
cycle, with the same delta-dimension. -/
private theorem exists_apply_ne_zero_of_properPushforward_apply_ne_zero (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX]
    [IsVariety K sY] (f : X ⟶ Y) [IsProper f] (hbase : f ≫ sY = sX) {k : ℤ}
    (α : CycleGroup (fieldChowSituation K) sX k) {y : Y}
    (hy : (properPushforward (fieldChowSituation K) sX sY f hbase k α).1 y ≠ 0) :
    ∃ x : X, f.base x = y ∧ α.1 x ≠ 0 ∧
      relativeDimension (fieldChowSituation K).dimensionFunction sX x =
        relativeDimension (fieldChowSituation K).dimensionFunction sY y := by
  rw [properPushforward_apply] at hy
  obtain ⟨x, hxy, hx⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  obtain rfl : f.base x = y := hxy
  refine ⟨x, rfl, left_ne_zero_of_mul hx, ?_⟩
  by_contra h
  exact hx (by rw [ite_eq_right h, mul_zero])

/-- Bilinearity of the intersection product of cycles over finite sums. -/
private theorem cycleIntersectionProduct_sum_zsmul_sum_zsmul {X : Scheme.{u}} [CompactSpace X]
    (prod : X → X → AlgebraicCycle X ℤ) {ι κ : Type*} (s : Finset ι) (t : Finset κ) (a : ι → ℤ)
    (b : κ → ℤ) (A : ι → AlgebraicCycle X ℤ) (B : κ → AlgebraicCycle X ℤ) :
    cycleIntersectionProduct prod (∑ i ∈ s, a i • A i) (∑ j ∈ t, b j • B j) =
      ∑ i ∈ s, ∑ j ∈ t, (a i * b j) • cycleIntersectionProduct prod (A i) (B j) := by
  rw [cycleIntersectionProduct_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cycleIntersectionProduct_zsmul_left _ _ (finite_support_of_compactSpace _)
    (finite_support_of_compactSpace _), cycleIntersectionProduct_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cycleIntersectionProduct_zsmul_right _ _ (finite_support_of_compactSpace _)
    (finite_support_of_compactSpace _), smul_smul]

/-! ### The purity of the inverse image of a subvariety -/

/-- **A point of a fibre specializes from a point of residue transcendence degree `r`**, for a
morphism whose fibres are equidimensional of dimension `r`: the generic point of an irreducible
component of the fibre through the point (Stacks 02FX). -/
theorem exists_specializes_toNat_residueTrdeg_eq_of_relativeDimension {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (r : ℕ) (hrel : AlgebraicGeometry.RelativeDimension f r)
    (x₀ : X) :
    ∃ x : X, x ⤳ x₀ ∧ f.base x = f.base x₀ ∧ Cardinal.toNat (residueTrdeg f x) = r := by
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({f.asFiber x₀} : Set (f.fiber (f.base x₀))))
    isIrreducible_singleton.closure
  set ζ := hW.1.genericPoint with hζ
  have hζW : IsGenericPoint ζ W :=
    hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
  set x := f.fiberι (f.base x₀) ζ with hxdef
  have hfx : f.base x = f.base x₀ := by
    have : x ∈ Set.range (f.fiberι (f.base x₀)).base := ⟨ζ, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  have hζx₀ : ζ ⤳ f.asFiber x₀ :=
    specializes_iff_mem_closure.mpr (hζW ▸ hsub (subset_closure rfl))
  have hxx₀ : x ⤳ x₀ := by
    have := hζx₀.map (f.fiberι (f.base x₀)).continuous
    rwa [Scheme.Hom.fiberι_asFiber] at this
  refine ⟨x, hxx₀, hfx, ?_⟩
  -- a point of the fibre of `x` generalizing `x` is `x`
  have hmaxX : ∀ x' : X, f.base x' = f.base x → x' ⤳ x → x' = x := by
    intro x' hx'f hx'
    have hmem : x' ∈ Set.range (f.fiberι (f.base x₀)).base := by
      rw [Scheme.Hom.range_fiberι]; exact hx'f.trans hfx
    obtain ⟨ζ', rfl⟩ := hmem
    have hsp : ζ' ⤳ ζ := (f.fiberι (f.base x₀)).isEmbedding.specializes_iff.mp hx'
    have hsub' : W ⊆ closure ({ζ'} : Set (f.fiber (f.base x₀))) := by
      rw [← hζW]
      exact closure_minimal (Set.singleton_subset_iff.mpr hsp.mem_closure) isClosed_closure
    have hgen : IsGenericPoint ζ' W :=
      Set.Subset.antisymm (hW.2 isIrreducible_singleton.closure hsub') hsub'
    rw [hgen.eq hζW]
  have hmax : IsMax (f.asFiber x) := by
    intro z hz
    have hspec : (f.fiberι (f.base x)).base z ⤳ x := by
      have h' : z ⤳ f.asFiber x := hz
      simpa using h'.map (f.fiberι (f.base x)).continuous
    have hzf : f.base ((f.fiberι (f.base x)).base z) = f.base x := by
      have : (f.fiberι (f.base x)).base z ∈ Set.range (f.fiberι (f.base x)).base := ⟨z, rfl⟩
      rw [Scheme.Hom.range_fiberι] at this
      exact this
    refine le_of_eq ((f.fiberι (f.base x)).isEmbedding.injective ?_)
    rw [hmaxX _ hzf hspec]
    exact (Scheme.Hom.fiberι_asFiber f x).symm
  have hzero : ringKrullDim ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x)) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact_mod_cast Order.coheight_eq_zero.mpr hmax
  have hq : LocallyOfFiniteType (f.fiberToSpecResidueField (f.base x)) := by
    change LocallyOfFiniteType (Limits.pullback.snd f (Y.fromSpecResidueField (f.base x)))
    infer_instance
  have hrelx := hrel (f.base x) ⟨f.asFiber x⟩
  have hAt := @topologicalKrullDimAt_eq_of_equidimensional _ _ (f.fiber (f.base x))
    (f.fiberToSpecResidueField (f.base x)) hq r hrelx.1 hrelx.2 (f.asFiber x)
  have hfor := topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg f x
  change topologicalKrullDimAt (f.fiber (f.base x)) (f.asFiber x) =
    ringKrullDim ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x)) +
      (Cardinal.toENat (residueTrdeg f x) : WithBot ℕ∞) at hfor
  rw [hAt, hzero, zero_add] at hfor
  have hENat : Cardinal.toENat (residueTrdeg f x) = r := (WithBot.coe_eq_coe.mp hfor).symm
  simpa [Cardinal.toNat_toENat] using congrArg ENat.toNat hENat

/-- **The purity of `f⁻¹(W)` for a flat morphism of varieties** (the source's "`f⁻¹(W)` has pure
dimension `s + e`"). Let `f : X ⟶ Y` be a flat morphism of varieties over a field with
`dim X = dim Y + e`, and let `w ⤳ f p`. Then `p` specializes from a point `z` over `w` with
`δ(z) = δ(w) + e`: going down for the flat `f` (Stacks 00HS) lifts `w` to a generalization of `p`,
and the fibre over `w` is equidimensional of dimension `e` (Stacks 02JS). -/
theorem exists_specializes_relativeDimension_eq_add_of_flat (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX]
    [IsVariety K sY] (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞)) {p : X} {w : Y}
    (hw : w ⤳ f p) :
    ∃ z : X, z ⤳ p ∧ f z = w ∧
      relativeDimension (fieldChowSituation K).dimensionFunction sX z =
        relativeDimension (fieldChowSituation K).dimensionFunction sY w + e := by
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  obtain ⟨z₀, hz₀p, hz₀w⟩ := Flat.generalizingMap f hw
  obtain ⟨z, hzz₀, hzf, htr⟩ := exists_specializes_toNat_residueTrdeg_eq_of_relativeDimension f e
    (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) z₀
  refine ⟨z, hzz₀.trans hz₀p, hzf.trans hz₀w, ?_⟩
  have hstep :=
    relativeDimension_comp_eq_add_trdeg (fieldChowSituation K).dimensionFunction sY f z
  rw [hbase, htr, hzf, hz₀w] at hstep
  exact hstep

/-! ### The dimension of `V ∩ f⁻¹(W)` -/

/-- **Components of `f⁻¹(W)` are components of `f^*β`.** Let `f : X ⟶ Y` be a flat morphism of
varieties over a field with `dim X = dim Y + e`, let `β` be an `s`-cycle on `Y` and `w` a point
with `β(w) ≠ 0`. A point `z` over `w` with `δ(z) = s + e` carries a nonzero coefficient of
`f^*β`: the coefficient is `β(w)` times the multiplicity of `f^*𝒪_W` at `z` (Stacks 0AZF), which
is positive because `z` lies in the support `f⁻¹(W)` and has the top delta-dimension. -/
theorem flatPullback_apply_ne_zero (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e s : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (β : CycleGroup (fieldChowSituation K) sY (s : ℤ)) {w : Y} (hw : β.1 w ≠ 0) {z : X}
    (hzw : f z = w)
    (hz : relativeDimension (fieldChowSituation K).dimensionFunction sX z = ((s + e : ℕ) : ℤ)) :
    haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    (flatPullback (fieldChowSituation K) sX sY f hbase e
      (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (s : ℤ) β).1 z ≠ 0 := by
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := isCoherent_structureSheafAt w
  have := isFiniteType_of_isCoherent (structureSheafAt w)
  have hpc := AlgebraicGeometry.isCoherent_pullback f (structureSheafAt w)
  have hδw := relativeDimension_eq_of_apply_ne_zero K sY β hw
  have hdimw : topologicalKrullDim (SheafOfModules.supp (structureSheafAt w) : Set Y) ≤
      (s : WithBot ℕ∞) := by
    rw [supp_structureSheafAt, topologicalKrullDim_closure_singleton_eq K sY w, hδw]
    simp
  have hb := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY
    (structureSheafAt w) s hdimw
  have hprime := congrArg (fun c => c.1 z)
    (Stacks.Intersection.CycleFlatPullback.flatPullback_primeCycle K sX sY f hbase e he w (s : ℤ)
      (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq (fieldChowSituation K) sY
        w hδw) hb)
  rw [flatPullback_apply] at hprime ⊢
  have hzsupp : z ∈ SheafOfModules.supp ((Scheme.Modules.pullback f).obj (structureSheafAt w)) := by
    rw [Stacks.Modules.supp_pullback, Set.mem_preimage, hzw, supp_structureSheafAt]
    exact subset_closure rfl
  have hbX := schemeDeltaDimension_support_pullback_le (fieldChowSituation K) sX sY f hbase e
    (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (structureSheafAt w) s hb
  have hz' : relativeDimension (fieldChowSituation K).dimensionFunction sX z = (s : ℤ) + e := by
    rw [hz]; push_cast; rfl
  have hlen := isFiniteLength_stalk_of_relativeDimension_eq (fieldChowSituation K) sX _ hbX hz'
  have hpos := sheafMultiplicity_pos_of_mem_supp _ hlen hzsupp
  rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq (fieldChowSituation K) sX _ _
    hbX hz'] at hprime
  have hweight : flatPullbackWeight (fieldChowSituation K) sX f ((s : ℤ) + (e : ℤ)) z ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprime
    exact hpos.ne' hprime.symm
  rw [hzw]
  exact mul_ne_zero hw hweight

/-- **`dim (V ∩ f⁻¹W) ≤ r + s - dim Y` for components `V` of `α` and `W` of `β`.** Let
`f : X ⟶ Y` be a flat morphism of varieties over a field with `dim X = dim Y + e`, let `v ∈ X` with
`δ(v) = r` and let `β` be an `s`-cycle on `Y` with `β(w) ≠ 0`. If the closure of `v` meets every
component of `f^*β` properly, then `dim (closure {v} ∩ f⁻¹(closure {w})) ≤ n`, where
`r + s = dim Y + n`. A point `p` of the intersection specializes from a point `z` over `w` with
`δ(z) = s + e`, which is a component of `f^*β`; so `p` lies in `closure {v} ∩ closure {z}`, of
dimension at most `n`. -/
theorem topologicalKrullDim_closure_inter_preimage_le (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e dY r s n : ℕ)
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (hrs : r + s = dY + n) (β : CycleGroup (fieldChowSituation K) sY (s : ℤ)) {v : X} {w : Y}
    (hv : relativeDimension (fieldChowSituation K).dimensionFunction sX v = (r : ℤ))
    (hw : β.1 w ≠ 0)
    (hvβ : ∀ z : X,
      haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      (flatPullback (fieldChowSituation K) sX sY f hbase e
        (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (s : ℤ) β).1 z ≠ 0 →
      AlgebraicGeometry.IntersectProperly
        ⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩
        ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩) :
    topologicalKrullDim (closure ({v} : Set X) ∩ f.base ⁻¹' closure ({w} : Set Y) : Set X) ≤
      (n : WithBot ℕ∞) := by
  have hδw := relativeDimension_eq_of_apply_ne_zero K sY β hw
  have hdX := topologicalKrullDim_eq_natCast_add hdY he
  have hT : IsClosed (closure ({v} : Set X) ∩ f.base ⁻¹' closure ({w} : Set Y)) :=
    isClosed_closure.inter (isClosed_closure.preimage f.base.hom.2)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  refine topologicalKrullDim_le_of_forall_relativeDimension_le K sX _ hT n fun p hp => ?_
  obtain ⟨hpv, hpw⟩ := hp
  obtain ⟨z, hzp, hzw, hzδ⟩ := exists_specializes_relativeDimension_eq_add_of_flat K sX sY f
    hbase e he (specializes_iff_mem_closure.mpr hpw)
  rw [hδw] at hzδ
  have hzδ' : relativeDimension (fieldChowSituation K).dimensionFunction sX z =
      ((s + e : ℕ) : ℤ) := by rw [hzδ]; push_cast; rfl
  have hprop := hvβ z (flatPullback_apply_ne_zero K sX sY f hbase e s he β hw hzw hzδ')
  have hsum : topologicalKrullDim (closure ({v} : Set X)) +
      topologicalKrullDim (closure ({z} : Set X)) =
        ((dY + e : ℕ) : WithBot ℕ∞) + (n : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_singleton_eq_of_relativeDimension_eq K sX hv,
      topologicalKrullDim_closure_singleton_eq_of_relativeDimension_eq K sX hzδ',
      ← Nat.cast_add, ← Nat.cast_add]
    congr 1
    omega
  have hinter := topologicalKrullDim_inter_le_of_intersectProperly_of_add_eq hprop hdX hsum
  have : JacobsonSpace (fieldChowSituation K).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of K)))
  exact relativeDimension_le_of_topologicalKrullDim_le (fieldChowSituation K)
    (fun _ _ => rfl) sX (isClosed_closure.inter isClosed_closure) hinter
    ⟨hpv, specializes_iff_mem_closure.mp hzp⟩

/-! ### The identity for cycles of coherent sheaves -/

/-- The support of a proper direct image has dimension at most that of the support. -/
theorem topologicalKrullDim_supp_pushforward_le_of_isProper (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX]
    [IsVariety K sY] (f : X ⟶ Y) [IsProper f] (hbase : f ≫ sY = sX) (F : X.Modules)
    [F.IsCoherent] (r : ℕ)
    (hFr : topologicalKrullDim (SheafOfModules.supp F : Set X) ≤ (r : WithBot ℕ∞)) :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pushforward f).obj F) : Set Y) ≤
      (r : WithBot ℕ∞) :=
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : F.IsFiniteType := isFiniteType_of_isCoherent F
  have := AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
  have : ((Scheme.Modules.pushforward f).obj F).IsFiniteType := isFiniteType_of_isCoherent _
  topologicalKrullDim_image_le K sX sY f hbase _ (SheafOfModules.isClosed_supp F) r hFr _
    (SheafOfModules.isClosed_supp _)
    (supp_pushforward_subset_image f F (SheafOfModules.isClosed_supp F))

/-- **Stacks 0B10 for cycles of coherent sheaves.** Let `f : X ⟶ Y` be a flat proper morphism of
nonsingular varieties over an algebraically closed field with `dim X = dim Y + e`, and let `ℱ`,
`𝒢` be coherent with `dim Supp ℱ ≤ r`, `dim Supp 𝒢 ≤ s` and
`dim (Supp ℱ ∩ f⁻¹ Supp 𝒢) ≤ n`, where `r + s = dim Y + n`. Then

`f_*([ℱ]_r · [f^*𝒢]_{s+e}) = [f_*ℱ]_r · [𝒢]_s`,

the products being the intersection product of cycles of Tag 0B08. Tag 0B0W upstairs and
downstairs identifies both sides with alternating sums of Tor cycles, which
`properPushforward_intersectionProductCycleGroup_unconditional` compares. -/
theorem properPushforward_coherentSheafCycleProduct (K : Type u) [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX]
    [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X) (hY : AlgebraicGeometry.IsRegular Y)
    (f : X ⟶ Y) [Flat f] [IsProper f] (hbase : f ≫ sY = sX) (F : X.Modules) (G : Y.Modules)
    (hFc : _root_.SheafOfModules.IsCoherent F) (hGc : _root_.SheafOfModules.IsCoherent G)
    (r s n dY e : ℕ) (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (hrs : r + s = dY + n)
    (hFr : topologicalKrullDim (SheafOfModules.supp F : Set X) ≤ (r : WithBot ℕ∞))
    (hGs : topologicalKrullDim (SheafOfModules.supp G : Set Y) ≤ (s : WithBot ℕ∞))
    (hFG : topologicalKrullDim
      (SheafOfModules.supp F ∩ f.base ⁻¹' SheafOfModules.supp G : Set X) ≤ (n : WithBot ℕ∞)) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    letI := hFc
    letI := hGc
    letI := isFiniteType_of_isCoherent F
    letI := isFiniteType_of_isCoherent G
    letI := AlgebraicGeometry.isCoherent_pullback f G
    letI := AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
    (properPushforward (fieldChowSituation K) sX sY f hbase (n : ℤ)
        ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n : ℤ)
            (coherentSheafCycle (fieldChowSituation K) sX F (r : ℤ)
              (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sX F r hFr))
            (coherentSheafCycle (fieldChowSituation K) sX ((Scheme.Modules.pullback f).obj G)
              ((s : ℤ) + (e : ℤ))
              (schemeDeltaDimension_support_pullback_le (fieldChowSituation K) sX sY f hbase e
                (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) G (s : ℤ)
                (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY G s hGs))),
          torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩).1 =
      torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY (n : ℤ)
        (coherentSheafCycle (fieldChowSituation K) sY ((Scheme.Modules.pushforward f).obj F)
          (r : ℤ) (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY _ r
            (topologicalKrullDim_supp_pushforward_le_of_isProper K sX sY f hbase F r hFr)))
        (coherentSheafCycle (fieldChowSituation K) sY G (s : ℤ)
          (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY G s hGs)) := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have := hFc
  have := hGc
  have := isFiniteType_of_isCoherent F
  have := isFiniteType_of_isCoherent G
  have hcG := AlgebraicGeometry.isCoherent_pullback f G
  have hpF := AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
  have := isFiniteType_of_isCoherent ((Scheme.Modules.pushforward f).obj F)
  have hdX := topologicalKrullDim_eq_natCast_add hdY he
  have hrs' : r + (s + e) = (dY + e) + n := by omega
  have hGsX := Stacks.Intersection.CycleFlatPullback.topologicalKrullDim_supp_pullback_le K sX sY
    f hbase e he G s hGs
  have hFGX : topologicalKrullDim (SheafOfModules.supp F ∩
      SheafOfModules.supp ((Scheme.Modules.pullback f).obj G) : Set X) ≤ (n : WithBot ℕ∞) := by
    rw [Stacks.Modules.supp_pullback]; exact hFG
  have hpFr := topologicalKrullDim_supp_pushforward_le_of_isProper K sX sY f hbase F r hFr
  have hST : (SheafOfModules.supp ((Scheme.Modules.pushforward f).obj F) ∩
      SheafOfModules.supp G : Set Y) ⊆
        f.base '' (SheafOfModules.supp F ∩ f.base ⁻¹' SheafOfModules.supp G) := by
    intro y hy
    obtain ⟨x, hxF, hxy⟩ :=
      supp_pushforward_subset_image f F (SheafOfModules.isClosed_supp F) hy.1
    exact ⟨x, ⟨hxF, by rw [Set.mem_preimage, hxy]; exact hy.2⟩, hxy⟩
  have hpFG : topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pushforward f).obj F) ∩
      SheafOfModules.supp G : Set Y) ≤ (n : WithBot ℕ∞) :=
    topologicalKrullDim_image_le K sX sY f hbase _
      ((SheafOfModules.isClosed_supp F).inter
        ((SheafOfModules.isClosed_supp G).preimage f.base.hom.2)) n hFG _
      ((SheafOfModules.isClosed_supp _).inter (SheafOfModules.isClosed_supp G)) hST
  obtain ⟨-, hidX⟩ := Stacks.Intersection.ReductionToDiagonal.torFormula K sX hX F
    ((Scheme.Modules.pullback f).obj G) hFc hcG r (s + e) n (dY + e) hdX hrs' hFr hGsX hFGX
  simp only [Nat.cast_add] at hidX
  obtain ⟨-, hidY⟩ := Stacks.Intersection.ReductionToDiagonal.torFormula K sY hY
    ((Scheme.Modules.pushforward f).obj F) G hpF hGc r s n dY hdY hrs hpFr hGs hpFG
  have hFn := torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation K) sX hX F
    ((Scheme.Modules.pullback f).obj G) hFc hcG (n : ℤ)
    (fun w hw => relativeDimension_le_of_topologicalKrullDim_le (fieldChowSituation K)
      (fun _ _ => rfl) sX ((SheafOfModules.isClosed_supp F).inter
        (SheafOfModules.isClosed_supp _)) hFGX hw)
  have harg : (⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n : ℤ)
          (coherentSheafCycle (fieldChowSituation K) sX F (r : ℤ)
            (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sX F r hFr))
          (coherentSheafCycle (fieldChowSituation K) sX ((Scheme.Modules.pullback f).obj G)
            ((s : ℤ) + (e : ℤ))
            (schemeDeltaDimension_support_pullback_le (fieldChowSituation K) sX sY f hbase e
              (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) G (s : ℤ)
              (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY G s hGs))),
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩ :
          CycleGroup (fieldChowSituation K) sX (n : ℤ)) =
      intersectionProductCycleGroup (fieldChowSituation K) sX hX F
        ((Scheme.Modules.pullback f).obj G) hFc hcG (n : ℤ) hFn :=
    Subtype.ext hidX
  rw [harg, properPushforward_intersectionProductCycleGroup_unconditional K sX sY hX hY f hbase F
    hFc G hGc (n : ℤ) hFn]
  exact hidY.symm

/-- **`V ∩ f⁻¹(W)` is empty when `r + s < dim Y`.** With the notation of
`topologicalKrullDim_closure_inter_preimage_le`, if `r + s < dim Y` then a component `V` of `α`
meeting every component of `f^*β` properly is disjoint from `f⁻¹(W)`: a point of the intersection
lies in `V ∩ Z` for a component `Z` of `f^*β` (the purity of `f⁻¹(W)`), and `V` and `Z` meet
properly in dimension `r + (s + e) - dim X < 0`. -/
theorem closure_inter_preimage_eq_empty (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e dY r s : ℕ)
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (hrs : r + s < dY) (β : CycleGroup (fieldChowSituation K) sY (s : ℤ)) {v : X} {w : Y}
    (hv : relativeDimension (fieldChowSituation K).dimensionFunction sX v = (r : ℤ))
    (hw : β.1 w ≠ 0)
    (hvβ : ∀ z : X,
      haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      (flatPullback (fieldChowSituation K) sX sY f hbase e
        (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (s : ℤ) β).1 z ≠ 0 →
      AlgebraicGeometry.IntersectProperly
        ⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩
        ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩) :
    closure ({v} : Set X) ∩ f.base ⁻¹' closure ({w} : Set Y) = ∅ := by
  have hδw := relativeDimension_eq_of_apply_ne_zero K sY β hw
  have hdX := topologicalKrullDim_eq_natCast_add hdY he
  refine Set.eq_empty_of_forall_notMem fun p hp => ?_
  obtain ⟨hpv, hpw⟩ := hp
  obtain ⟨z, hzp, hzw, hzδ⟩ := exists_specializes_relativeDimension_eq_add_of_flat K sX sY f
    hbase e he (specializes_iff_mem_closure.mpr hpw)
  rw [hδw] at hzδ
  have hzδ' : relativeDimension (fieldChowSituation K).dimensionFunction sX z =
      ((s + e : ℕ) : ℤ) := by rw [hzδ]; push_cast; rfl
  have hprop := hvβ z (flatPullback_apply_ne_zero K sX sY f hbase e s he β hw hzw hzδ')
  rw [AlgebraicGeometry.intersectProperly_iff] at hprop
  change topologicalKrullDim (↥(closure ({v} : Set X) ∩ closure ({z} : Set X))) +
      topologicalKrullDim X ≤ topologicalKrullDim (closure ({v} : Set X)) +
        topologicalKrullDim (closure ({z} : Set X)) at hprop
  rw [topologicalKrullDim_closure_singleton_eq_of_relativeDimension_eq K sX hv,
    topologicalKrullDim_closure_singleton_eq_of_relativeDimension_eq K sX hzδ', hdX] at hprop
  have hne : topologicalKrullDim (↥(closure ({v} : Set X) ∩ closure ({z} : Set X))) ≠ ⊥ := by
    intro h
    rw [topologicalKrullDim_eq_bot_iff_isEmpty] at h
    exact h.false ⟨p, hpv, specializes_iff_mem_closure.mp hzp⟩
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← ha, ← Nat.cast_add] at hprop
  have h1 : a + ((dY + e : ℕ) : ℕ∞) ≤ ((r + (s + e) : ℕ) : ℕ∞) := by exact_mod_cast hprop
  have h2 : ((dY + e : ℕ) : ℕ∞) ≤ ((r + (s + e) : ℕ) : ℕ∞) := le_trans le_add_self h1
  have h3 : dY + e ≤ r + (s + e) := by exact_mod_cast h2
  omega

/-! ### Tag 0B10 -/

/-- **Stacks Project, Tag 0B10.** Let `f : X ⟶ Y` be a flat proper morphism of nonsingular
varieties over an algebraically closed field `K` — the chapter's convention, Tag 0AZ8 — with
`dim X = dim Y + e`. Let `α` be an `r`-cycle on `X` and `β` an `s`-cycle on `Y`, and assume that
`α` and `f^*β` intersect properly. Then `f_*α` and `β` intersect properly and

`f_*(α) · β = f_*(α · f^*β)`.

The products are the intersection product of cycles of Tag 0B08 in dimension
`n = r + s - dim Y`, an integer: on `X` the same `n` is `r + (s + e) - dim X`. When `n < 0` the
supports of `f_*α` and `β` are disjoint and both products vanish, as there are no cycles of
negative dimension. -/
@[stacks 0B10 "the whole lemma: both that `f_*α` and `β` intersect properly and the identity \
`f_*(α) · β = f_*(α · f^*β)`, for arbitrary cycles `α ∈ Z_r(X)` and `β ∈ Z_s(Y)` and every \
`r`, `s`, under the source's assumption that `α` and `f^*β` intersect properly, for a flat \
proper morphism of nonsingular varieties over an algebraically closed field — the chapter's \
own convention, Tag 0AZ8 — with `dim X = dim Y + e`. The products are the Section 43.17 \
product of cycles of Tag 0B08 in dimension `n = r + s - dim Y`, an integer."]
theorem properPushforward_torFormulaCycleIntersectionProduct_eq (K : Type u) [Field K]
    [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    [IsVariety K sX] [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X)
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [Flat f] [IsProper f]
    (hbase : f ≫ sY = sX) (e dY r s : ℕ) (n : ℤ)
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (hrs : (r : ℤ) + (s : ℤ) = (dY : ℤ) + n)
    (α : CycleGroup (fieldChowSituation K) sX (r : ℤ))
    (β : CycleGroup (fieldChowSituation K) sY (s : ℤ))
    (hαβ : haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
      AlgebraicCycle.IntersectProperly α.1
        (flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (s : ℤ) β).1) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    AlgebraicCycle.IntersectProperly
        (properPushforward (fieldChowSituation K) sX sY f hbase (r : ℤ) α).1 β.1 ∧
      (properPushforward (fieldChowSituation K) sX sY f hbase n
          ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX n α.1
              (flatPullback (fieldChowSituation K) sX sY f hbase e
                (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (s : ℤ) β).1,
            torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sX hX
              n _ _⟩).1 =
        torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY n
          (properPushforward (fieldChowSituation K) sX sY f hbase (r : ℤ) α).1 β.1 := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn
    replace hrs : r + s = dY + n := by exact_mod_cast hrs
    classical
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
    set hrel := relativeDimension_of_flat_of_isVariety K sX sY f hbase e he with hrelDef
    have hdX := topologicalKrullDim_eq_natCast_add hdY he
    -- the dimension bound for a pair of components
    have hbound : ∀ v, α.1 v ≠ 0 → ∀ w, β.1 w ≠ 0 →
        topologicalKrullDim (closure ({v} : Set X) ∩ f.base ⁻¹' closure ({w} : Set Y) : Set X) ≤
          (n : WithBot ℕ∞) := fun v hv w hw =>
      topologicalKrullDim_closure_inter_preimage_le K sX sY f hbase e dY r s n hdY he hrs β
        (relativeDimension_eq_of_apply_ne_zero K sX α hv) hw fun z hz =>
          hαβ ⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩
            ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
            (by rw [genericPoint_closure_singleton]; exact hv)
            (by rw [genericPoint_closure_singleton]; exact hz)
    refine ⟨?_, ?_⟩
    · -- the properness clause
      intro W V hW hV
      set y := W.isIrreducible.genericPoint with hy
      set w := V.isIrreducible.genericPoint with hw
      have hWy : (W : Set Y) = closure {y} :=
        (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).symm
      have hVw : (V : Set Y) = closure {w} :=
        (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).symm
      obtain ⟨x, hxy, hαx, hδx⟩ :=
        exists_apply_ne_zero_of_properPushforward_apply_ne_zero K sX sY f hbase α hW
      have hdimW : topologicalKrullDim (W : Set Y) = (r : WithBot ℕ∞) := by
        rw [hWy]
        exact topologicalKrullDim_closure_singleton_eq_of_relativeDimension_eq K sY
          (hδx.symm.trans (relativeDimension_eq_of_apply_ne_zero K sX α hαx))
      have hdimV : topologicalKrullDim (V : Set Y) = (s : WithBot ℕ∞) := by
        rw [hVw]
        exact topologicalKrullDim_closure_singleton_eq_of_relativeDimension_eq K sY
          (relativeDimension_eq_of_apply_ne_zero K sY β hV)
      have hsub : ((W : Set Y) ∩ (V : Set Y)) ⊆
          f.base '' (closure ({x} : Set X) ∩ f.base ⁻¹' closure ({w} : Set Y)) := by
        rw [hWy, hVw]
        exact closure_inter_subset_image_closure_inter_preimage f w hxy
      have hle := topologicalKrullDim_image_le K sX sY f hbase _
        (isClosed_closure.inter (isClosed_closure.preimage f.base.hom.2)) n
        (hbound x hαx w hV) _ (W.isClosed.inter V.isClosed) hsub
      rw [AlgebraicGeometry.intersectProperly_iff, hdimW, hdimV, hdY]
      calc topologicalKrullDim (↥((W : Set Y) ∩ (V : Set Y))) + (dY : WithBot ℕ∞)
          ≤ (n : WithBot ℕ∞) + (dY : WithBot ℕ∞) := by gcongr
        _ = (r : WithBot ℕ∞) + (s : WithBot ℕ∞) := by
          rw [← Nat.cast_add, ← Nat.cast_add]; congr 1; omega
    · -- the identity, by bilinearity from the identity for one pair of components
      have hα : (Function.support α.1).Finite := finite_support_of_compactSpace α.1
      have hβ : (Function.support β.1).Finite := finite_support_of_compactSpace β.1
      have hsuppv : ∀ v, α.1 v ≠ 0 →
          topologicalKrullDim (SheafOfModules.supp (structureSheafAt v) : Set X) ≤
            (r : WithBot ℕ∞) := fun v hv => by
        rw [supp_structureSheafAt]
        exact (topologicalKrullDim_closure_singleton_eq_of_relativeDimension_eq K sX
          (relativeDimension_eq_of_apply_ne_zero K sX α hv)).le
      have hsuppw : ∀ w, β.1 w ≠ 0 →
          topologicalKrullDim (SheafOfModules.supp (structureSheafAt w) : Set Y) ≤
            (s : WithBot ℕ∞) := fun w hw => by
        rw [supp_structureSheafAt]
        exact (topologicalKrullDim_closure_singleton_eq_of_relativeDimension_eq K sY
          (relativeDimension_eq_of_apply_ne_zero K sY β hw)).le
      -- the prime cycles of `α` and `β` as cycles of structure sheaves
      have hP : ∀ v (hv : v ∈ hα.toFinset),
          cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX
              (integralComponentAt v).subschemeι (r : ℤ) =
            cycleAssociatedToCoherentSheaf (fieldChowSituation K) sX (structureSheafAt v) (r : ℤ)
              (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sX _ r
                (hsuppv v (hα.mem_toFinset.1 hv))) := fun v hv =>
        cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf (fieldChowSituation K) sX
          _ (r : ℤ) (le_of_eq (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq
            (fieldChowSituation K) sX v
            (relativeDimension_eq_of_apply_ne_zero K sX α (hα.mem_toFinset.1 hv))))
      have hQ : ∀ w (hw : w ∈ hβ.toFinset),
          cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
              (integralComponentAt w).subschemeι (s : ℤ) =
            cycleAssociatedToCoherentSheaf (fieldChowSituation K) sY (structureSheafAt w) (s : ℤ)
              (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY _ s
                (hsuppw w (hβ.mem_toFinset.1 hw))) := fun w hw =>
        cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf (fieldChowSituation K) sY
          _ (s : ℤ) (le_of_eq (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq
            (fieldChowSituation K) sY w
            (relativeDimension_eq_of_apply_ne_zero K sY β (hβ.mem_toFinset.1 hw))))
      set P : X → CycleGroup (fieldChowSituation K) sX (r : ℤ) := fun v =>
        cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX
          (integralComponentAt v).subschemeι (r : ℤ) with hPdef
      set Q : Y → CycleGroup (fieldChowSituation K) sY (s : ℤ) := fun w =>
        cycleAssociatedToClosedSubscheme (fieldChowSituation K) sY
          (integralComponentAt w).subschemeι (s : ℤ) with hQdef
      -- the expansions of `α`, `β`, `f^*β` and `f_*α` along the prime cycles
      have hαsum : α.1 = ∑ v ∈ hα.toFinset, α.1 v • (P v).1 := by
        conv_lhs => rw [cycle_eq_sum_zsmul_primeCycles α hα]
        simp [P]
      have hβsum : β.1 = ∑ w ∈ hβ.toFinset, β.1 w • (Q w).1 := by
        conv_lhs => rw [cycle_eq_sum_zsmul_primeCycles β hβ]
        simp [Q]
      have hpullβ : (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (s : ℤ) β).1 =
          ∑ w ∈ hβ.toFinset, β.1 w •
            (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (s : ℤ) (Q w)).1 := by
        have h1 : flatPullback (fieldChowSituation K) sX sY f hbase e hrel (s : ℤ) β =
            ∑ w ∈ hβ.toFinset, β.1 w •
              flatPullback (fieldChowSituation K) sX sY f hbase e hrel (s : ℤ) (Q w) := by
          conv_lhs => rw [cycle_eq_sum_zsmul_primeCycles β hβ]
          rw [map_sum]
          exact Finset.sum_congr rfl fun w _ => map_zsmul _ _ _
        rw [h1]
        simp
      have hpushα : (properPushforward (fieldChowSituation K) sX sY f hbase (r : ℤ) α).1 =
          ∑ v ∈ hα.toFinset, α.1 v •
            (properPushforward (fieldChowSituation K) sX sY f hbase (r : ℤ) (P v)).1 := by
        have h1 : properPushforward (fieldChowSituation K) sX sY f hbase (r : ℤ) α =
            ∑ v ∈ hα.toFinset, α.1 v •
              properPushforward (fieldChowSituation K) sX sY f hbase (r : ℤ) (P v) := by
          conv_lhs => rw [cycle_eq_sum_zsmul_primeCycles α hα]
          rw [← properPushforwardHom_apply, map_sum]
          exact Finset.sum_congr rfl fun v _ => by
            rw [map_zsmul, properPushforwardHom_apply]
        rw [h1]
        simp
      -- the identity for one pair of components
      have hpair : ∀ v ∈ hα.toFinset, ∀ w ∈ hβ.toFinset,
          (properPushforward (fieldChowSituation K) sX sY f hbase (n : ℤ)
            ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n : ℤ) (P v).1
                (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (s : ℤ) (Q w)).1,
              torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sX hX
                (n : ℤ) _ _⟩).1 =
            torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY (n : ℤ)
              (properPushforward (fieldChowSituation K) sX sY f hbase (r : ℤ) (P v)).1 (Q w).1 := by
        intro v hv w hw
        have hv' := hα.mem_toFinset.1 hv
        have hw' := hβ.mem_toFinset.1 hw
        have := isCoherent_structureSheafAt v
        have := isCoherent_structureSheafAt w
        have hpQ := Stacks.Intersection.CycleFlatPullback.flatPullback_primeCycle K sX sY f hbase e
          he w (s : ℤ)
          (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq (fieldChowSituation K)
            sY w (relativeDimension_eq_of_apply_ne_zero K sY β hw'))
          (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY _ s
            (hsuppw w hw'))
        have hpP := properPushforward_cycleAssociatedToCoherentSheaf_unconditional
          (fieldChowSituation K) sX sY f hbase (structureSheafAt v) (r : ℤ)
          (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sX _ r (hsuppv v hv'))
        have hFG : topologicalKrullDim (SheafOfModules.supp (structureSheafAt v) ∩
            f.base ⁻¹' SheafOfModules.supp (structureSheafAt w) : Set X) ≤ (n : WithBot ℕ∞) := by
          rw [supp_structureSheafAt, supp_structureSheafAt]
          exact hbound v hv' w hw'
        have hstep := properPushforward_coherentSheafCycleProduct K sX sY hX hY f hbase
          (structureSheafAt v) (structureSheafAt w) (isCoherent_structureSheafAt v)
          (isCoherent_structureSheafAt w) r s n dY e hdY he hrs (hsuppv v hv') (hsuppw w hw') hFG
        have := AlgebraicGeometry.isCoherent_pullback f (structureSheafAt w)
        have :=
          AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f (structureSheafAt v)
        have hΦ : ∀ A B : AlgebraicCycle X ℤ, ∀ A' B' : AlgebraicCycle X ℤ, A = A' → B = B' →
            (properPushforward (fieldChowSituation K) sX sY f hbase (n : ℤ)
              ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n : ℤ) A B,
                torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sX
                  hX (n : ℤ) A B⟩).1 =
              (properPushforward (fieldChowSituation K) sX sY f hbase (n : ℤ)
                ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n : ℤ) A' B',
                  torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sX
                    hX (n : ℤ) A' B'⟩).1 := by
          rintro A B A' B' rfl rfl; rfl
        have hA : (P v).1 = (cycleAssociatedToCoherentSheaf (fieldChowSituation K) sX
            (structureSheafAt v) (r : ℤ)
            (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sX _ r
              (hsuppv v hv'))).1 := congrArg Subtype.val (hP v hv)
        have hB : (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (s : ℤ) (Q w)).1 =
            (cycleAssociatedToCoherentSheaf (fieldChowSituation K) sX
              ((Scheme.Modules.pullback f).obj (structureSheafAt w)) ((s : ℤ) + (e : ℤ))
              (schemeDeltaDimension_support_pullback_le (fieldChowSituation K) sX sY f hbase e
                (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (structureSheafAt w)
                (s : ℤ) (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY _ s
                  (hsuppw w hw')))).1 := congrArg Subtype.val hpQ
        have hC : (properPushforward (fieldChowSituation K) sX sY f hbase (r : ℤ) (P v)).1 =
            (cycleAssociatedToCoherentSheaf (fieldChowSituation K) sY
              ((Scheme.Modules.pushforward f).obj (structureSheafAt v)) (r : ℤ)
              (schemeDeltaDimension_reducedSupport_pushforward_le (fieldChowSituation K) sX sY f
                hbase _ (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sX _ r
                  (hsuppv v hv')))).1 :=
          (congrArg (fun c => (properPushforward (fieldChowSituation K) sX sY f hbase (r : ℤ)
            c).1) (hP v hv)).trans (congrArg Subtype.val hpP)
        have hD : (Q w).1 = (cycleAssociatedToCoherentSheaf (fieldChowSituation K) sY
            (structureSheafAt w) (s : ℤ)
            (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le K sY _ s
              (hsuppw w hw'))).1 := congrArg Subtype.val (hQ w hw)
        rw [hΦ _ _ _ _ hA hB, hC, hD]
        exact hstep
      -- the two sides expanded by bilinearity
      have hexpX : torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n : ℤ) α.1
            (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (s : ℤ) β).1 =
          ∑ v ∈ hα.toFinset, ∑ w ∈ hβ.toFinset, (α.1 v * β.1 w) •
            torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n : ℤ) (P v).1
              (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (s : ℤ) (Q w)).1 := by
        change cycleIntersectionProduct
          (torFormulaSubvarietyProductTotal (fieldChowSituation K) sX hX (n : ℤ)) _ _ = _
        conv_lhs => rw [hαsum, hpullβ]
        exact cycleIntersectionProduct_sum_zsmul_sum_zsmul _ _ _ _ _ _ _
      have hexpY : torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY (n : ℤ)
            (properPushforward (fieldChowSituation K) sX sY f hbase (r : ℤ) α).1 β.1 =
          ∑ v ∈ hα.toFinset, ∑ w ∈ hβ.toFinset, (α.1 v * β.1 w) •
            torFormulaCycleIntersectionProduct (fieldChowSituation K) sY hY (n : ℤ)
              (properPushforward (fieldChowSituation K) sX sY f hbase (r : ℤ) (P v)).1 (Q w).1 := by
        change cycleIntersectionProduct
          (torFormulaSubvarietyProductTotal (fieldChowSituation K) sY hY (n : ℤ)) _ _ = _
        conv_lhs => rw [hpushα, hβsum]
        exact cycleIntersectionProduct_sum_zsmul_sum_zsmul _ _ _ _ _ _ _
      -- the left side, read in the cycle group and pushed forward
      have hL : (⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n : ℤ) α.1
              (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (s : ℤ) β).1,
            torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sX hX
              (n : ℤ) _ _⟩ : CycleGroup (fieldChowSituation K) sX (n : ℤ)) =
          ∑ v ∈ hα.toFinset, ∑ w ∈ hβ.toFinset, (α.1 v * β.1 w) •
            (⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n : ℤ) (P v).1
                (flatPullback (fieldChowSituation K) sX sY f hbase e hrel (s : ℤ) (Q w)).1,
              torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sX hX
                (n : ℤ) _ _⟩ : CycleGroup (fieldChowSituation K) sX (n : ℤ)) := by
        apply Subtype.ext
        refine hexpX.trans ?_
        simp
      rw [hL, hexpY, ← properPushforwardHom_apply, map_sum]
      simp only [map_sum, map_zsmul, properPushforwardHom_apply, AddSubmonoidClass.coe_finsetSum,
        AddSubgroupClass.coe_zsmul]
      exact Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun w hw => by
        rw [hpair v hv w hw]
  have hrs' : r + s < dY := by omega
  refine ⟨?_, ?_⟩
  · -- the properness clause: the supports of `f_*α` and `β` are disjoint
    intro W V hW hV
    set y := W.isIrreducible.genericPoint with hy
    set w := V.isIrreducible.genericPoint with hw
    have hWy : (W : Set Y) = closure {y} :=
      (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).symm
    have hVw : (V : Set Y) = closure {w} :=
      (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).symm
    obtain ⟨x, hxy, hαx, -⟩ :=
      exists_apply_ne_zero_of_properPushforward_apply_ne_zero K sX sY f hbase α hW
    have hempty := closure_inter_preimage_eq_empty K sX sY f hbase e dY r s hdY he hrs' β
      (relativeDimension_eq_of_apply_ne_zero K sX α hαx) hV fun z hz => hαβ
        ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
        ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
        (by rw [genericPoint_closure_singleton]; exact hαx)
        (by rw [genericPoint_closure_singleton]; exact hz)
    have hWV : ((W : Set Y) ∩ (V : Set Y)) = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun p hp => ?_
      rw [hWy, hVw] at hp
      obtain ⟨q, hq, -⟩ := closure_inter_subset_image_closure_inter_preimage f w hxy hp
      rwa [hempty] at hq
    rw [AlgebraicGeometry.intersectProperly_iff, hWV,
      (topologicalKrullDim_eq_bot_iff_isEmpty _).2 (Set.isEmpty_coe_sort.mpr rfl)]
    simp
  · -- both products are cycles of negative dimension
    rw [cycleGroup_eq_zero_of_neg K sY hn
      (properPushforward (fieldChowSituation K) sX sY f hbase n _)]
    exact (congrArg Subtype.val (cycleGroup_eq_zero_of_neg K sY hn
      ⟨_, torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K)
        sY hY n _ _⟩)).symm

end Stacks.Intersection.ProjectionFormula

end
