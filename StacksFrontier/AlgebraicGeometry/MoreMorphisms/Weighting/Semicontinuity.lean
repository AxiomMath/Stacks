module

public import Mathlib.Topology.Semicontinuity.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.PurelyInseparableDecomposition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FiniteChart
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Weighting
public import StacksCore.Tactic.StacksAttribute

/-!
# Semicontinuity for positive weightings

A positive weighting of a locally quasi-finite morphism is upper semicontinuous on the source,
and — for a separated morphism with finite fibres — its weighted fibre sum is lower
semicontinuous on the target.

## Main results

* `AlgebraicGeometry.IsWeighting.upperSemicontinuous`: a positive weighting is upper
  semicontinuous.
* `AlgebraicGeometry.lowerSemicontinuous_separableDegreeWeightedFiberSum`: the weighted fibre sum
  of a positive weighting of a separated morphism with finite fibres is lower semicontinuous.

## Implementation notes

Local quasi-finiteness is `AlgebraicGeometry.LocallyOfFiniteType` together with
`AlgebraicGeometry.LocallyQuasiFinite`, and a positive weighting is an integer-valued weighting
that is strictly positive at every point.

Upper semicontinuity is local: a finite open chart through `x` over an étale neighbourhood of
`f x` has weighted fibre sum equal to `w x` at the distinguished point, because its fibre there
is the single point above `x` and the residue extension is purely inseparable; on the open set
where that locally constant function keeps its value the weighted fibre sum bounds every weight
from above, which is the required inequality.

Lower semicontinuity comes from the decomposition of the source, over an étale neighbourhood,
into open-and-closed pieces finite over the neighbourhood: the weighted fibre sum of the whole
is the sum over the pieces, each distinguished piece contributes a locally constant function,
the residual piece contributes a nonnegative one which vanishes at the distinguished point, and
an étale map is open.

## References

* [Stacks Project, Tag 0F3I](https://stacks.math.columbia.edu/tag/0F3I)
* [Stacks Project, Tag 0F3J](https://stacks.math.columbia.edu/tag/0F3J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A weighting has locally constant weighted fibre sum on a finite open piece of an étale base
change. -/
private lemma isLocallyConstant_fiberSum_of_isFinite_opens {X Y Z : Scheme.{u}} {f : X ⟶ Y}
    {w : X → ℤ} (hw : IsWeighting f w) (g : Z ⟶ Y) [Etale g] (V : (pullback f g).Opens)
    (hfin : IsFinite (V.ι ≫ pullback.snd f g)) :
    IsLocallyConstant (separableDegreeWeightedFiberSum (V.ι ≫ pullback.snd f g)
      (w ∘ (V.ι ≫ pullback.fst f g))) := by
  have hcomm : (V.ι ≫ pullback.fst f g) ≫ f = (V.ι ≫ pullback.snd f g) ≫ g := by
    simp only [Category.assoc, pullback.condition]
  refine hw.isLocallyConstant _ _ g hcomm inferInstance ?_ hfin
  have : pullback.lift (V.ι ≫ pullback.fst f g) (V.ι ≫ pullback.snd f g) hcomm = V.ι := by
    apply pullback.hom_ext
    exacts [pullback.lift_fst _ _ _, pullback.lift_snd _ _ _]
  rw [this]
  infer_instance

/-- Every point of the source of a locally quasi-finite morphism with a positive weighting has
an open neighbourhood on which the weighting is bounded by its value at that point. -/
private lemma exists_isOpen_weight_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (w : X → ℤ)
    (hw : IsWeighting f w) (hpos : ∀ x, 0 < w x) (x : X) :
    ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ ∀ z ∈ N, w z ≤ w x := by
  classical
  obtain ⟨U, m, D, a, hdata, hcover⟩ := exists_finite_opens_chart_at_point f x
  obtain ⟨p, hpf, hpu⟩ :=
    Scheme.Pullback.exists_preimage_pullback x U.point U.map_point.symm
  obtain ⟨j₀, hj₀⟩ := hcover p hpu hpf
  let V := D j₀
  let fst : pullback f U.toBase ⟶ X := pullback.fst f U.toBase
  let π : pullback f U.toBase ⟶ U.scheme := pullback.snd f U.toBase
  let g := V.ι ≫ π
  let j := V.ι ≫ fst
  obtain ⟨hfinite, hfiber, hsource, ⟨ha, hpure⟩⟩ := hdata j₀
  have : IsFinite g := hfinite
  have hax : j (a j₀) = x := hsource
  have hcenter : separableDegreeWeightedFiberSum g (w ∘ j) U.point = w x := by
    rw [separableDegreeWeightedFiberSum_eq_of_fiber_singleton g (w ∘ j) U.point (a j₀)
      hfiber ha hpure]
    show w (j (a j₀)) = w x
    rw [hax]
  have hLC := isLocallyConstant_fiberSum_of_isFinite_opens hw U.toBase V hfinite
  let W : Set U.scheme := {u | separableDegreeWeightedFiberSum g (w ∘ j) u = w x}
  have hWopen : IsOpen W := hLC.isOpen_fiber (w x)
  refine ⟨j '' (g ⁻¹' W), j.isOpenMap _ (hWopen.preimage g.continuous), ⟨a j₀, ?_, hax⟩, ?_⟩
  · show g (a j₀) ∈ W
    rw [ha]
    exact hcenter
  · rintro z ⟨z', hz'W, rfl⟩
    have hsum : separableDegreeWeightedFiberSum g (w ∘ j) (g z') = w x := hz'W
    have hbound := le_separableDegreeWeightedFiberSum g (w ∘ j) (g z') z' rfl
      (g.finite_preimage_singleton (g z')) fun q ↦ hpos (j q)
    simpa only [Function.comp_apply] using hbound.trans_eq hsum

/-- **Stacks Project, Tag 0F3I.** A positive weighting of a locally quasi-finite morphism is
upper semicontinuous on its source. -/
@[stacks 0F3I]
theorem IsWeighting.upperSemicontinuous
    {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] {w : X → ℤ}
    (hw : IsWeighting f w) (hpos : ∀ x, 0 < w x) :
    UpperSemicontinuous w := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  refine fun a ↦ isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
  obtain ⟨N, hNopen, hxN, hbound⟩ := exists_isOpen_weight_le f w hw hpos x
  filter_upwards [hNopen.mem_nhds hxN] with z hz
  exact lt_of_le_of_lt (hbound z hz) hx

/-- **Stacks Project, Tag 0F3J.** The weighted fibre sum of a positive weighting of a
separated, locally quasi-finite morphism with finite fibres is lower semicontinuous. -/
@[stacks 0F3J, ega "IV 18.2.8" "semicontinuity of n(y)"]
theorem lowerSemicontinuous_separableDegreeWeightedFiberSum
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (hfinite : ∀ y, (f ⁻¹' {y}).Finite) (w : X → ℤ)
    (hw : IsWeighting f w) (hpos : ∀ x, 0 < w x) :
    LowerSemicontinuous (separableDegreeWeightedFiberSum f w) := by
  classical
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro c
  apply isOpen_iff_forall_mem_open.mpr
  intro y hy
  change c < separableDegreeWeightedFiberSum f w y at hy
  obtain ⟨n, xs, hxs, hxi⟩ := exists_fin_bijective_isolated_fiber f hfinite y
  obtain ⟨U, m, D, v, hdisj, hcover, hclopen, hdata, hnone⟩ :=
    exists_etaleNeighborhood_purelyInseparable_decomposition f n y xs hxs.1 hxi
  let P := pullback f U.toBase
  let fst : P ⟶ X := pullback.fst f U.toBase
  let π : P ⟶ U.scheme := pullback.snd f U.toBase
  let wP : P → ℤ := w ∘ fst
  let A := Σ i : Fin n, Fin (m i)
  let part : Option A → U.scheme → ℤ := fun k ↦
    separableDegreeWeightedFiberSum ((D k).ι ≫ π) (wP ∘ (D k).ι)
  have hdisj' : ∀ i j : Option A, i ≠ j → Disjoint (D i : Set P) (D j : Set P) :=
    fun i j hij ↦ hdisj (Set.mem_univ i) (Set.mem_univ j) hij
  have hcover' : ∀ p : P, ∃ k, p ∈ D k := by
    intro p
    have hp : p ∈ ⋃ k : Option A, (D k).1 := by rw [hcover]; trivial
    exact Set.mem_iUnion.mp hp
  have hfiniteP : ∀ u, (π ⁻¹' {u}).Finite := fun u ↦
    finite_preimage_singleton_of_isPullback f fst π U.toBase
      (IsPullback.of_hasPullback f U.toBase) hfinite u
  have hsum : ∀ u, separableDegreeWeightedFiberSum π wP u = ∑ k : Option A, part k u := by
    intro u
    have h := congrFun
      (separableDegreeWeightedFiberSum_eq_sum_opens π wP D hdisj' hcover' hfiniteP) u
    simpa only [Finset.sum_apply] using h
  have hbasechange : ∀ u : U.scheme,
      separableDegreeWeightedFiberSum f w (U.toBase u) =
        separableDegreeWeightedFiberSum π wP u :=
    congrFun (separableDegreeWeightedFiberSum_comp_of_isPullback
      f fst π U.toBase (IsPullback.of_hasPullback f U.toBase) hfinite w)
  have huniv : (Finset.univ : Finset (Option A)) = Finset.insertNone Finset.univ := by
    ext k
    cases k <;> simp
  have hres_nonneg : ∀ u, 0 ≤ part none u := fun u ↦
    separableDegreeWeightedFiberSum_nonneg _ _ (fun q ↦ (hpos (fst ((D none).ι q))).le) u
  have htotal_ge : ∀ u, (∑ a : A, part (some a) u) ≤
      separableDegreeWeightedFiberSum π wP u := by
    intro u
    calc
      (∑ a : A, part (some a) u) ≤ part none u + ∑ a : A, part (some a) u :=
        le_add_of_nonneg_left (hres_nonneg u)
      _ = ∑ k : Option A, part k u := by rw [huniv, Finset.sum_insertNone]
      _ = separableDegreeWeightedFiberSum π wP u := (hsum u).symm
  have hpiece_lc : ∀ a : A, IsLocallyConstant (part (some a)) := fun a ↦
    isLocallyConstant_fiberSum_of_isFinite_opens hw U.toBase (D (some a)) (hdata a.1 a.2).1
  let T : Set U.scheme := ⋂ a : A, {u | part (some a) u = part (some a) U.point}
  have hTopen : IsOpen T := isOpen_iInter_of_finite fun a ↦ (hpiece_lc a).isOpen_fiber _
  have hTpoint : U.point ∈ T := Set.mem_iInter.mpr fun a ↦ rfl
  have hres_zero : part none U.point = 0 :=
    separableDegreeWeightedFiberSum_eq_zero_of_fiber_eq_empty _ _ _
      (fiber_eq_empty_of_forall_ne f y xs hxs.2 U (D none) hnone)
  have hcenter : separableDegreeWeightedFiberSum f w y = ∑ a : A, part (some a) U.point := by
    calc
      separableDegreeWeightedFiberSum f w y =
          separableDegreeWeightedFiberSum π wP U.point := by
        have hbc := hbasechange U.point
        rwa [U.map_point] at hbc
      _ = ∑ k : Option A, part k U.point := hsum U.point
      _ = part none U.point + ∑ a : A, part (some a) U.point := by
        rw [huniv, Finset.sum_insertNone]
      _ = ∑ a : A, part (some a) U.point := by rw [hres_zero, zero_add]
  refine ⟨U.toBase '' T, ?_, U.toBase.isOpenMap T hTopen, ⟨U.point, hTpoint, U.map_point⟩⟩
  rintro z ⟨u, hu, rfl⟩
  refine lt_of_lt_of_le hy ?_
  calc
    separableDegreeWeightedFiberSum f w y = ∑ a : A, part (some a) U.point := hcenter
    _ = ∑ a : A, part (some a) u :=
      Finset.sum_congr rfl fun a _ ↦ ((Set.mem_iInter.mp hu) a).symm
    _ ≤ separableDegreeWeightedFiberSum π wP u := htotal_ge u
    _ = separableDegreeWeightedFiberSum f w (U.toBase u) := (hbasechange u).symm

end AlgebraicGeometry
