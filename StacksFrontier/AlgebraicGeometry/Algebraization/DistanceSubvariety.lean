module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceFunction
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceVanishing
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Dimension.DimensionFunction
public import StacksFrontier.Topology.Dimension.DimensionFunctionIsCatenary
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The distance from a closed point or a closed subvariety (Stacks Example 0EJ1)

Stacks Example 0EJ1 computes the distance function `δ_Z` on a Noetherian scheme `Y` carrying a
dimension function `δ`, in the case where `Z` is the closure of a single point `ζ`, i.e. an
irreducible closed subvariety (cases (2b), (2c), (2d) of the example), and the special case
where `ζ` is a closed point (cases (1a), (1b)).

## Main results

* `distanceFunction_eq_sub_of_specializes` (case 2b): if `y ⤳ ζ`, i.e. `Z ⊆ closure {y}`, then
  `δ_Z(y) = δ(y) - δ(ζ)`.
* `distanceFunction_eq_of_isClosed_of_specializes` (case 1a): the special case of (2b) where
  `ζ` is a closed point.
* `distanceFunction_eq_one_of_not_specializes` (case 2c): if `¬ (ζ ⤳ y)` and `δ y ≤ δ ζ`, then
  `δ_Z(y) = 1`.
* `distanceFunction_eq_sub_add_one_of_not_specializes` (case 2d): if `¬ (y ⤳ ζ)` and
  `δ ζ < δ y`, then `δ_Z(y) = δ(y) - δ(ζ) + 1`.
* `distanceFunction_eq_add_one_of_not_specializes` (case 1b): the special case of (2c)/(2d)
  where `ζ` is a closed point.

## Implementation notes

Cases (2c) and (2d) both come from a single auxiliary zigzag of two legs, `Z ⊆ ⊤ ⊇ closure {y}
= closure {y}`, whose weight is exactly `(δ y - δ ζ).toNat + 1` regardless of the comparison
between `δ y` and `δ ζ`; this needs `[IrreducibleSpace Y]` (satisfied, e.g., by affine space
over a field) so that `⊤` has a well-defined generic point dominating every other point. The
two cases differ only in which lower bound on the distance matches this upper bound.

## References

* [Stacks Project, Tag 0EJ1](https://stacks.math.columbia.edu/tag/0EJ1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

open TopologicalSpace.IrreducibleCloseds (closureSingleton coe_closureSingleton)

namespace Stacks.Algebraization

/-- The underlying space of a scheme is sober in the sense of `StacksSober`. -/
@[sga "4 IV 4.2.1" "partial"]
private lemma distanceSubvariety_scheme_stacksSober (Y : Scheme.{u}) : StacksSober Y :=
  stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩

/-- A dimension function is antitone with respect to specialization. -/
private lemma dimensionFunction_le_of_specializes
    {Y : Scheme.{u}} (δ : DimensionFunction Y) {a b : Y} (h : a ⤳ b) : δ b ≤ δ a := by
  rcases eq_or_ne a b with rfl | hne
  · exact le_rfl
  · exact (δ.strictAnti_specializes h hne).le

/-- A specialization `a ⤳ b` gives an inclusion of closures `closure {b} ⊆ closure {a}`. -/
private lemma closureSingleton_le_of_specializes {Y : Type*} [TopologicalSpace Y] {a b : Y}
    (h : a ⤳ b) : closureSingleton b ≤ closureSingleton a := by
  rw [← SetLike.coe_subset_coe, coe_closureSingleton, coe_closureSingleton]
  exact h.closure_subset

/-- The codimension of `closure {b}` in `closure {a}` for `a ⤳ b` is `δ a - δ b`. -/
private lemma topCodim_closureSingleton_eq_toNat_sub
    {Y : Scheme.{u}} [IsNoetherian Y] (δ : DimensionFunction Y) {a b : Y} (h : a ⤳ b) :
    IrreducibleClosedsCodim.topCodim (closureSingleton b) (closureSingleton a) =
      ((δ a - δ b).toNat : ℕ∞) :=
  codim_closure_singleton_eq_delta_diff (distanceSubvariety_scheme_stacksSober Y) δ.toFun
    δ.isDimensionFunctionForCatenary a b h

/-- In an irreducible space, every connected component meets `closure {ζ}`. -/
private lemma connectedComponent_inter_closure_singleton_nonempty
    {Y : Type*} [TopologicalSpace Y] [IrreducibleSpace Y] (ζ y : Y) :
    (connectedComponent y ∩ closure ({ζ} : Set Y)).Nonempty := by
  rw [PreconnectedSpace.connectedComponent_eq_univ]
  exact ⟨ζ, Set.mem_univ ζ, subset_closure rfl⟩

/-- The closed subset `{z}` for a closed point `z` equals `closure {z}`. -/
private lemma closeds_singleton_eq_closure {Y : Type*} [TopologicalSpace Y] {z : Y}
    (hz : IsClosed ({z} : Set Y)) :
    (⟨{z}, hz⟩ : Closeds Y) = (⟨closure {z}, isClosed_closure⟩ : Closeds Y) :=
  SetLike.coe_injective hz.closure_eq.symm

/-- A dimension function attains its greatest value on the closure of a point exactly at that
point. -/
private lemma isGreatest_image_closureSingleton
    {Y : Scheme.{u}} (δ : DimensionFunction Y) (ζ : Y) :
    IsGreatest (δ '' closure ({ζ} : Set Y)) (δ ζ) :=
  ⟨⟨ζ, subset_closure rfl, rfl⟩, by
    rintro _ ⟨z, hz, rfl⟩
    exact dimensionFunction_le_of_specializes δ (specializes_iff_mem_closure.mpr hz)⟩

/-- **Stacks Project, Tag 0EJ1, case (2b).** If `y ⤳ ζ`, i.e. the subvariety `closure {ζ}` is
contained in `closure {y}`, the distance from `closure {ζ}` to `y` is `δ(y) - δ(ζ)`. -/
@[stacks 0EJ1 "subvariety_specializes"]
public theorem distanceFunction_eq_sub_of_specializes
    (Y : Scheme.{u}) [IsNoetherian Y] (δ : DimensionFunction Y) (ζ y : Y) (h : y ⤳ ζ) :
    distanceFunction Y (⟨closure {ζ}, isClosed_closure⟩ : Closeds Y) y =
      ((δ y - δ ζ).toNat : ℕ∞) := by
  set Z : Closeds Y := ⟨closure {ζ}, isClosed_closure⟩
  have hmeet : (connectedComponent y ∩ (Z : Set Y)).Nonempty :=
    ⟨ζ, (isIrreducible_singleton.closure.isConnected).subset_connectedComponent
      (subset_closure rfl) (specializes_iff_mem_closure.mp h), subset_closure rfl⟩
  let hs0 : DistanceSystem Y Z y :=
    ⟨0, fun _ => closureSingleton ζ, fun _ => closureSingleton y,
      fun _ => closureSingleton_le_of_specializes h,
      fun i => i.elim0,
      subset_rfl,
      coe_closureSingleton y⟩
  have hcod : IrreducibleClosedsCodim.topCodim (closureSingleton ζ) (closureSingleton y) =
      ((δ y - δ ζ).toNat : ℕ∞) :=
    topCodim_closureSingleton_eq_toNat_sub δ h
  have hupcod : hs0.upCodimension ⟨0, Nat.zero_lt_succ hs0.k⟩ = (δ y - δ ζ).toNat := by
    show (IrreducibleClosedsCodim.topCodim (closureSingleton ζ) (closureSingleton y)).toNat = _
    rw [hcod, ENat.toNat_natCast]
  have hk0 : hs0.k = 0 := rfl
  have huniv1 : (Finset.univ : Finset (Fin (hs0.k + 1))) = {⟨0, Nat.zero_lt_succ hs0.k⟩} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Fin.ext (by have := i.isLt; omega)
  have hempty : (Finset.univ : Finset (Fin hs0.k)) = ∅ := by
    ext j
    exact j.elim0
  have hweight : hs0.weight = (δ y - δ ζ).toNat := by
    show hs0.k + (Finset.univ : Finset (Fin (hs0.k + 1))).sup (fun i =>
        (∑ j : Fin (hs0.k + 1), if i.val ≤ j.val then hs0.upCodimension j else 0) -
        (∑ j : Fin hs0.k, if i.val ≤ j.val then hs0.downCodimension j else 0)) =
      (δ y - δ ζ).toNat
    simp only [huniv1, Finset.sup_singleton, Finset.sum_singleton, hempty, Finset.sum_empty,
      le_refl, if_true, Nat.sub_zero, hupcod, hk0, Nat.zero_add]
  refine le_antisymm ?_ (distanceFunction_ge_dimensionFunction_sub_max Y Z δ (δ ζ)
    (isGreatest_image_closureSingleton δ ζ) y)
  rw [distanceFunction_eq_iInf_of_nonempty Y Z y hmeet, ← hweight]
  exact iInf_le _ hs0

/-- **Stacks Project, Tag 0EJ1, case (1a).** If `z` is a closed point and `y ⤳ z`, the distance
from `{z}` to `y` is `δ(y)`. -/
@[stacks 0EJ1 "closed_point_specializes"]
public theorem distanceFunction_eq_of_isClosed_of_specializes
    (Y : Scheme.{u}) [IsNoetherian Y] (δ : DimensionFunction Y) (z y : Y)
    (hz : IsClosed ({z} : Set Y)) (hz0 : δ z = 0) (h : y ⤳ z) :
    distanceFunction Y (⟨{z}, hz⟩ : Closeds Y) y = ((δ y).toNat : ℕ∞) := by
  rw [closeds_singleton_eq_closure hz, distanceFunction_eq_sub_of_specializes Y δ z y h, hz0,
    sub_zero]

/-- Shared upper bound for cases (2c) and (2d): a zigzag of two legs through the generic point
of `Y` always witnesses weight `(δ(y) - δ(ζ)).toNat + 1`, regardless of how `δ(y)` and `δ(ζ)`
compare. -/
private lemma distanceFunction_le_toNat_add_one
    (Y : Scheme.{u}) [IsNoetherian Y] [IrreducibleSpace Y] (δ : DimensionFunction Y) (ζ y : Y) :
    distanceFunction Y (⟨closure {ζ}, isClosed_closure⟩ : Closeds Y) y ≤
      ((δ y - δ ζ).toNat : ℕ∞) + 1 := by
  set Z : Closeds Y := ⟨closure {ζ}, isClosed_closure⟩ with hZdef
  have hmeet : (connectedComponent y ∩ (Z : Set Y)).Nonempty :=
    connectedComponent_inter_closure_singleton_nonempty ζ y
  have hηζ : genericPoint Y ⤳ ζ := genericPoint_specializes ζ
  have hηy : genericPoint Y ⤳ y := genericPoint_specializes y
  have hδζη : δ ζ ≤ δ (genericPoint Y) := dimensionFunction_le_of_specializes δ hηζ
  have hδyη : δ y ≤ δ (genericPoint Y) := dimensionFunction_le_of_specializes δ hηy
  let hs1 : DistanceSystem Y Z y :=
    ⟨1, fun i => if i.val = 0 then closureSingleton ζ else closureSingleton y,
      fun i => if i.val = 0 then closureSingleton (genericPoint Y) else closureSingleton y,
      fun i => by
        split_ifs
        · exact closureSingleton_le_of_specializes hηζ
        · exact le_rfl,
      fun i => by
        have h1 : ¬ (Fin.succ i).val = 0 := by simp [Fin.val_succ]
        have h0 : (Fin.castSucc i).val = 0 := by simp
        show (if (Fin.succ i).val = 0 then closureSingleton ζ else closureSingleton y) ≤
          (if (Fin.castSucc i).val = 0 then closureSingleton (genericPoint Y)
            else closureSingleton y)
        rw [if_neg h1, if_pos h0]
        exact closureSingleton_le_of_specializes hηy,
      by
        show (closureSingleton ζ : Set Y) ⊆ (Z : Set Y)
        simp [hZdef],
      by
        show (if (Fin.last 1).val = 0 then
            (closureSingleton (genericPoint Y) : IrreducibleCloseds Y)
          else closureSingleton y : Set Y) = closure {y}
        rw [if_neg (by simp : ¬ (Fin.last 1).val = 0)]
        exact coe_closureSingleton y⟩
  have hk1 : hs1.k = 1 := rfl
  have huniv2 : (Finset.univ : Finset (Fin (hs1.k + 1))) =
      {⟨0, Nat.zero_lt_succ hs1.k⟩, ⟨1, by omega⟩} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases Nat.lt_or_ge i.val 1 with h | h
    · exact Or.inl (Fin.ext (show i.val = 0 by omega))
    · exact Or.inr (Fin.ext (show i.val = 1 by have := i.isLt; omega))
  have huniv1 : (Finset.univ : Finset (Fin hs1.k)) = {⟨0, by omega⟩} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Fin.ext (show j.val = 0 by have := j.isLt; omega)
  have hupcod0 : hs1.upCodimension ⟨0, Nat.zero_lt_succ hs1.k⟩ =
      (δ (genericPoint Y) - δ ζ).toNat := by
    show (IrreducibleClosedsCodim.topCodim (closureSingleton ζ)
      (closureSingleton (genericPoint Y))).toNat = _
    rw [topCodim_closureSingleton_eq_toNat_sub δ hηζ, ENat.toNat_natCast]
  have hupcod1 : hs1.upCodimension ⟨1, by omega⟩ = 0 := by
    show (IrreducibleClosedsCodim.topCodim (closureSingleton y) (closureSingleton y)).toNat = 0
    simp [topCodim_self_eq_zero]
  have hdowncod0 : hs1.downCodimension ⟨0, by omega⟩ =
      (δ (genericPoint Y) - δ y).toNat := by
    show (IrreducibleClosedsCodim.topCodim (closureSingleton y)
      (closureSingleton (genericPoint Y))).toNat = _
    rw [topCodim_closureSingleton_eq_toNat_sub δ hηy, ENat.toNat_natCast]
  have hweight : hs1.weight = (δ y - δ ζ).toNat + 1 := by
    show hs1.k + (Finset.univ : Finset (Fin (hs1.k + 1))).sup (fun i =>
        (∑ j : Fin (hs1.k + 1), if i.val ≤ j.val then hs1.upCodimension j else 0) -
        (∑ j : Fin hs1.k, if i.val ≤ j.val then hs1.downCodimension j else 0)) =
      (δ y - δ ζ).toNat + 1
    have hne : (⟨0, Nat.zero_lt_succ hs1.k⟩ : Fin (hs1.k + 1)) ∉
        ({⟨1, by omega⟩} : Finset (Fin (hs1.k + 1))) := by
      simp only [Finset.mem_singleton]
      exact fun h => by simpa using congrArg Fin.val h
    simp only [huniv2, huniv1, Finset.sup_insert, Finset.sup_singleton,
      Finset.sum_insert hne, Finset.sum_singleton, hupcod0, hupcod1, hdowncod0, hk1]
    norm_num
    omega
  calc distanceFunction Y Z y ≤ (hs1.weight : ℕ∞) := by
        rw [distanceFunction_eq_iInf_of_nonempty Y Z y hmeet]
        exact iInf_le _ hs1
    _ = ((δ y - δ ζ).toNat : ℕ∞) + 1 := by rw [hweight]; push_cast; ring

/-- **Stacks Project, Tag 0EJ1, case (2c).** If `ζ` does not specialize to `y` and
`δ(y) ≤ δ(ζ)`, the distance from `closure {ζ}` to `y` is `1`. -/
@[stacks 0EJ1 "subvariety_codim_small"]
public theorem distanceFunction_eq_one_of_not_specializes
    (Y : Scheme.{u}) [IsNoetherian Y] [IrreducibleSpace Y] (δ : DimensionFunction Y) (ζ y : Y)
    (h : ¬ ζ ⤳ y) (hle : δ y ≤ δ ζ) :
    distanceFunction Y (⟨closure {ζ}, isClosed_closure⟩ : Closeds Y) y = 1 := by
  set Z : Closeds Y := ⟨closure {ζ}, isClosed_closure⟩
  have hynotin : y ∉ (Z : Set Y) := fun hmem => h (specializes_iff_mem_closure.mpr hmem)
  have hne0 : distanceFunction Y Z y ≠ 0 :=
    fun h0 => hynotin ((distanceFunction_eq_zero_iff_mem Y Z y).mp h0)
  have htoNat0 : (δ y - δ ζ).toNat = 0 := by omega
  have hub1 : distanceFunction Y Z y ≤ 1 := by
    simpa [htoNat0] using distanceFunction_le_toNat_add_one Y δ ζ y
  exact le_antisymm hub1 (Order.one_le_iff_ne_zero.mpr hne0)

/-- Shared sharp lower bound for case (2d): if `y` does not specialize to `ζ` and
`δ(ζ) < δ(y)`, every system witnessing the distance from `closure {ζ}` to `y` has weight at
least `(δ(y) - δ(ζ)).toNat + 1`. The extra `+ 1` over the bound of
`distanceFunction_ge_dimensionFunction_sub_max` comes from a case split on whether the system's
first irreducible closed piece is exactly `closure {ζ}`: if it is, the system cannot have length
`0` (else it would witness `y ⤳ ζ`), giving the `+ 1` from the length; if not, the generic point
of that piece is a strictly smaller specialization of `ζ`, giving the `+ 1` from the dimension
function gap. -/
private lemma distanceSystem_weight_ge_toNat_add_one
    (Y : Scheme.{u}) [IsNoetherian Y] (δ : DimensionFunction Y) (ζ y : Y)
    (hnspec : ¬ y ⤳ ζ) (hlt : δ ζ < δ y)
    (s : DistanceSystem Y (⟨closure {ζ}, isClosed_closure⟩ : Closeds Y) y) :
    (δ y - δ ζ).toNat + 1 ≤ s.weight := by
  classical
  let v : Fin (s.k + 1) → Y := fun i => (s.V i).isIrreducible'.genericPoint
  let w : Fin (s.k + 1) → Y := fun i => (s.W i).isIrreducible'.genericPoint
  have hv (i : Fin (s.k + 1)) : IsGenericPoint (v i) (s.V i : Set Y) :=
    (s.V i).isIrreducible'.isGenericPoint_genericPoint (s.V i).isClosed'
  have hw (i : Fin (s.k + 1)) : IsGenericPoint (w i) (s.W i : Set Y) :=
    (s.W i).isIrreducible'.isGenericPoint_genericPoint (s.W i).isClosed'
  have hspecUp (i : Fin (s.k + 1)) : w i ⤳ v i :=
    (hw i).specializes (s.V_le_W i (hv i).mem)
  have hspecDown (i : Fin s.k) : w i.castSucc ⤳ v i.succ :=
    (hw i.castSucc).specializes (s.V_next_le_W i (hv i.succ).mem)
  have hVIso (i : Fin (s.k + 1)) : closureSingleton (v i) = s.V i :=
    IrreducibleCloseds.ext (hv i).def
  have hWIso (i : Fin (s.k + 1)) : closureSingleton (w i) = s.W i :=
    IrreducibleCloseds.ext (hw i).def
  have hcodUp (i : Fin (s.k + 1)) :
      IrreducibleClosedsCodim.topCodim (s.V i) (s.W i) =
        ((δ (w i) - δ (v i)).toNat : ℕ∞) := by
    rw [← hVIso i, ← hWIso i]
    exact topCodim_closureSingleton_eq_toNat_sub δ (hspecUp i)
  have hcodDown (i : Fin s.k) :
      IrreducibleClosedsCodim.topCodim (s.V i.succ) (s.W i.castSucc) =
        ((δ (w i.castSucc) - δ (v i.succ)).toNat : ℕ∞) := by
    rw [← hVIso i.succ, ← hWIso i.castSucc]
    exact topCodim_closureSingleton_eq_toNat_sub δ (hspecDown i)
  have hupInt (i : Fin (s.k + 1)) : (s.upCodimension i : ℤ) = δ (w i) - δ (v i) := by
    unfold DistanceSystem.upCodimension
    rw [hcodUp i, ENat.toNat_natCast, Int.toNat_of_nonneg
      (sub_nonneg.mpr (dimensionFunction_le_of_specializes δ (hspecUp i)))]
  have hdownInt (i : Fin s.k) :
      (s.downCodimension i : ℤ) = δ (w i.castSucc) - δ (v i.succ) := by
    unfold DistanceSystem.downCodimension
    rw [hcodDown i, ENat.toNat_natCast, Int.toNat_of_nonneg
      (sub_nonneg.mpr (dimensionFunction_le_of_specializes δ (hspecDown i)))]
  have htelV :
      (∑ i : Fin s.k, (δ (v i.succ) - δ (v i.castSucc))) =
        δ (v (Fin.last s.k)) - δ (v 0) := by
    have hsucc :
        (∑ i : Fin s.k, δ (v i.succ)) + δ (v 0) =
          ∑ i : Fin (s.k + 1), δ (v i) := by
      rw [Fin.sum_univ_succ]
      ring
    have hcast :
        (∑ i : Fin s.k, δ (v i.castSucc)) + δ (v (Fin.last s.k)) =
          ∑ i : Fin (s.k + 1), δ (v i) := by
      rw [Fin.sum_univ_castSucc]
    rw [Finset.sum_sub_distrib]
    omega
  have hcap :
      (∑ i : Fin s.k,
        ((δ (w i.castSucc) - δ (v i.castSucc)) -
          (δ (w i.castSucc) - δ (v i.succ)))) =
        ∑ i : Fin s.k, (δ (v i.succ) - δ (v i.castSucc)) :=
    Finset.sum_congr rfl fun i _ => by ring
  have hwlast : w (Fin.last s.k) = y := by
    apply (hw (Fin.last s.k)).eq
    rw [s.W_last_eq_closure]
    exact isGenericPoint_closure
  have htel :
      (∑ i : Fin (s.k + 1), (s.upCodimension i : ℤ)) -
        (∑ i : Fin s.k, (s.downCodimension i : ℤ)) =
          δ y - δ (v 0) := by
    calc
      _ = (∑ i : Fin s.k,
            ((s.upCodimension i.castSucc : ℤ) - (s.downCodimension i : ℤ))) +
              (s.upCodimension (Fin.last s.k) : ℤ) := by
          rw [Fin.sum_univ_castSucc, Finset.sum_sub_distrib]
          ring
      _ = δ y - δ (v 0) := by
          simp_rw [hupInt, hdownInt]
          rw [hcap, htelV, hwlast]
          ring
  have hCB : ((∑ i : Fin (s.k + 1), s.upCodimension i : ℕ) : ℤ) -
      ((∑ i : Fin s.k, s.downCodimension i : ℕ) : ℤ) = δ y - δ (v 0) := by
    simpa [Nat.cast_sum] using htel
  have hwb : s.k + (∑ i : Fin (s.k + 1), s.upCodimension i) ≤
      s.weight + (∑ i : Fin s.k, s.downCodimension i) := by
    have hsup := Finset.le_sup
      (f := fun i : Fin (s.k + 1) =>
        (∑ j : Fin (s.k + 1), if i.val ≤ j.val then s.upCodimension j else 0) -
        (∑ j : Fin s.k, if i.val ≤ j.val then s.downCodimension j else 0))
      (b := (0 : Fin (s.k + 1))) (Finset.mem_univ _)
    simp only [Fin.val_zero, Nat.zero_le, if_true] at hsup
    unfold DistanceSystem.weight
    omega
  have hv0mem : v 0 ∈ closure {ζ} := s.V_zero_subset (hv 0).mem
  have hζspec_v0 : ζ ⤳ v 0 := specializes_iff_mem_closure.mpr hv0mem
  have hδv0_le : δ (v 0) ≤ δ ζ := dimensionFunction_le_of_specializes δ hζspec_v0
  rcases eq_or_ne (v 0) ζ with hveq | hveq
  · have hδeq : δ (v 0) = δ ζ := congrArg δ hveq
    have hk_pos : 1 ≤ s.k := by
      by_contra! hcontra
      have hk0 : s.k = 0 := by omega
      have hlastEq : Fin.last s.k = (0 : Fin (s.k + 1)) := by
        apply Fin.ext
        simp [Fin.val_last, hk0]
      have hW0 : (s.W (0 : Fin (s.k + 1)) : Set Y) = closure {y} := by
        rw [← hlastEq]
        exact s.W_last_eq_closure
      have hζmemW0 : ζ ∈ (s.W (0 : Fin (s.k + 1)) : Set Y) := by
        refine s.V_le_W 0 ?_
        rw [← hVIso 0, ← SetLike.mem_coe, coe_closureSingleton, hveq]
        exact subset_closure rfl
      rw [hW0] at hζmemW0
      exact hnspec (specializes_iff_mem_closure.mpr hζmemW0)
    omega
  · have hδlt : δ (v 0) < δ ζ := δ.strictAnti_specializes hζspec_v0 (Ne.symm hveq)
    omega

/-- **Stacks Project, Tag 0EJ1, case (2d).** If `y` does not specialize to `ζ` and
`δ(ζ) < δ(y)`, the distance from `closure {ζ}` to `y` is `δ(y) - δ(ζ) + 1`. -/
@[stacks 0EJ1 "subvariety_codim_large"]
public theorem distanceFunction_eq_sub_add_one_of_not_specializes
    (Y : Scheme.{u}) [IsNoetherian Y] [IrreducibleSpace Y] (δ : DimensionFunction Y) (ζ y : Y)
    (h : ¬ y ⤳ ζ) (hlt : δ ζ < δ y) :
    distanceFunction Y (⟨closure {ζ}, isClosed_closure⟩ : Closeds Y) y =
      ((δ y - δ ζ).toNat : ℕ∞) + 1 := by
  set Z : Closeds Y := ⟨closure {ζ}, isClosed_closure⟩
  have hmeet : (connectedComponent y ∩ (Z : Set Y)).Nonempty :=
    connectedComponent_inter_closure_singleton_nonempty ζ y
  refine le_antisymm (distanceFunction_le_toNat_add_one Y δ ζ y) ?_
  rw [distanceFunction_eq_iInf_of_nonempty Y Z y hmeet, le_iInf_iff]
  intro s
  exact_mod_cast distanceSystem_weight_ge_toNat_add_one Y δ ζ y h hlt s

/-- **Stacks Project, Tag 0EJ1, case (1b).** If `z` is a closed point and `y` does not
specialize to `z`, the distance from `{z}` to `y` is `δ(y) + 1`. -/
@[stacks 0EJ1 "closed_point_not_specializes"]
public theorem distanceFunction_eq_add_one_of_not_specializes
    (Y : Scheme.{u}) [IsNoetherian Y] [IrreducibleSpace Y] (δ : DimensionFunction Y) (z y : Y)
    (hz : IsClosed ({z} : Set Y)) (hz0 : δ z = 0) (h : ¬ y ⤳ z) :
    distanceFunction Y (⟨{z}, hz⟩ : Closeds Y) y = ((δ y).toNat : ℕ∞) + 1 := by
  rw [closeds_singleton_eq_closure hz]
  by_cases hle : δ y ≤ δ z
  · have hznotspec : ¬ z ⤳ y := by
      intro hzy
      apply h
      have hmem : y ∈ ({z} : Set Y) := by
        rw [← hz.closure_eq]
        exact specializes_iff_mem_closure.mp hzy
      rw [Set.mem_singleton_iff.mp hmem]
    rw [distanceFunction_eq_one_of_not_specializes Y δ z y hznotspec hle]
    have hδy0 : (δ y).toNat = 0 := by omega
    simp [hδy0]
  · push Not at hle
    rw [distanceFunction_eq_sub_add_one_of_not_specializes Y δ z y h hle, hz0, sub_zero]

end Stacks.Algebraization

end
