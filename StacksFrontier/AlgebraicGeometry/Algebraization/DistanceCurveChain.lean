module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceSubvariety
public import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPointChain

/-!
# Chains of curves and the distance from a closed point (Stacks Example 0EJ1, closing sentence)

The last paragraph of Stacks Example 0EJ1 generalizes case (1) of that example away from
affine space: for a scheme `Y` of finite type over a field and `Z = {z}` a closed point,
`δ_Z(y) = δ(y) + t`, where `t` is the minimum length of a chain of curves connecting `z` to a
closed point of `closure {y}`.

## Main definitions

* `Stacks.Algebraization.IsCurveIn` — a *curve in* `Y` is an integral closed subscheme of
  dimension one, encoded (as everywhere in this chapter) by its underlying irreducible closed
  subset.
* `Stacks.Algebraization.CurveChain` — a chain of curves connecting a point `z` to a closed
  point of a subset `S`.
* `Stacks.Algebraization.curveChainDistance` — the minimum length of such a chain, infinite if
  there is none.

## Main results

* `Stacks.Algebraization.DistanceSystem.weight_eq_add_sup` — the weight of a zigzag is
  `k + maxᵢ (δ(y) − δ(vᵢ))`, where `vᵢ` is the generic point of the `i`-th lower endpoint. The
  upper endpoints cancel in the telescoping sum, so only the lower ones survive.
* `Stacks.Algebraization.distanceFunction_le_add_curveChainDistance` — the inequality
  `δ_Z(y) ≤ δ(y) + t`.
* `Stacks.Algebraization.add_distanceSystem_k_le_weight` and
  `Stacks.Algebraization.add_le_distanceFunction` — the lower bound in terms of the length of a
  zigzag: `δ(y) + k ≤ weight`.
* `Stacks.Algebraization.distanceFunction_eq_add_curveChainDistance` — the equality, for `Y` of
  finite type over a field and any dimension function vanishing at the closed points.
* `Stacks.Algebraization.distanceFunction_eq_topologicalKrullDim_add_curveChainDistance` — the
  closing sentence of the example, with `δ(y) = dim closure {y}` the usual dimension function.

## Implementation notes

The two bounds take `Y` Noetherian with `JacobsonSpace Y` and a dimension function `δ`
vanishing at the closed points: that is what their arguments use, and it is the generality at
which the cases of 0EJ1 in `StacksFrontier.AlgebraicGeometry.Algebraization.DistanceSubvariety` are
stated. For a scheme of finite type over a field the normalization `δ = 0` at closed points pins
`δ` down to be the usual dimension function `y ↦ dim closure {y}`.

The weight of a zigzag `V₀ ⊆ W₀ ⊇ V₁ ⊆ ⋯ ⊆ Wₖ` telescopes: for every index `i`,
`cᵢ + ⋯ + cₖ − bᵢ − ⋯ − bₖ₋₁ = δ(y) − δ(vᵢ)`, because `cⱼ = δ(wⱼ) − δ(vⱼ)` and
`bⱼ = δ(wⱼ) − δ(vⱼ₊₁)`. This single identity gives both bounds: for the zigzag built from a
chain of curves all the `vᵢ` are the junction points of the chain, the first of which is the
closed point `z` with `δ(z) = 0`, so the maximum is `δ(y)` and the weight is `δ(y) + t`; and
for an arbitrary zigzag `v₀ = z`, so the weight is at least `δ(y) + k`.

The curve condition is not used in the upper bound: that bound holds for a chain of arbitrary
integral closed subschemes, which is the inequality of Stacks Remark 0EJ0. The lower bound turns
a zigzag with `k` descending legs into a chain of at most `k` curves, which needs that two
distinct closed points of an integral closed subscheme lie on a common curve. The source does not
state this; it is `Stacks.Algebraization.CurveThroughPoints.exists_dim_one_of_mem` of
`StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints`, proved with the Bertini
irreducibility theorem [Stacks, Tag 0G4F] and with no common affine neighbourhood of the two
points assumed. It is also why the equality is stated for `Y` of finite type over a field.

## References

* [Stacks Project, Tag 0EJ1](https://stacks.math.columbia.edu/tag/0EJ1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

open TopologicalSpace.IrreducibleCloseds (closureSingleton coe_closureSingleton)

namespace Stacks.Algebraization

/-! ## Curves and chains of curves -/

/-- A *curve in* `Y` is an integral closed subscheme of dimension one. As everywhere in this
chapter, an integral closed subscheme is encoded by its underlying irreducible closed subset,
which carries a canonical reduced — hence integral — scheme structure. -/
public def IsCurveIn {Y : Scheme.{u}} (C : IrreducibleCloseds Y) : Prop :=
  topologicalKrullDim (C : Set Y) = 1

/-- A chain of curves connecting `z` to a closed point of `S`: curves `C₀, …, C_{t-1}` in `Y`
and points `p₀ = z, p₁, …, p_t` with `pᵢ` and `pᵢ₊₁` both on `Cᵢ`, the last point `p_t` being a
closed point lying in `S`. A chain of length `0` is the assertion that `z` itself is a closed
point of `S`. -/
public structure CurveChain (Y : Scheme.{u}) (z : Y) (S : Set Y) where
  /-- The number of curves in the chain. -/
  length : ℕ
  /-- The junction points, starting at `z` and ending at a closed point of `S`. -/
  pt : Fin (length + 1) → Y
  /-- The curves of the chain. -/
  curve : Fin length → IrreducibleCloseds Y
  /-- Every member of the chain is a curve. -/
  isCurve : ∀ i, IsCurveIn (curve i)
  /-- The chain starts at `z`. -/
  pt_zero : pt 0 = z
  /-- The chain ends in `S`. -/
  pt_last_mem : pt (Fin.last length) ∈ S
  /-- The chain ends at a closed point. -/
  pt_last_isClosed : IsClosed ({pt (Fin.last length)} : Set Y)
  /-- The `i`-th curve passes through the `i`-th junction point. -/
  mem_castSucc : ∀ i : Fin length, pt i.castSucc ∈ (curve i : Set Y)
  /-- The `i`-th curve passes through the next junction point. -/
  mem_succ : ∀ i : Fin length, pt i.succ ∈ (curve i : Set Y)

/-- The minimum length of a chain of curves connecting `z` to a closed point of `S`; infinite
if there is no such chain. This is the quantity `t` of the closing paragraph of Stacks Example
0EJ1. -/
public def curveChainDistance (Y : Scheme.{u}) (z : Y) (S : Set Y) : ℕ∞ :=
  ⨅ c : CurveChain Y z S, (c.length : ℕ∞)

/-- A chain of curves witnesses its own length as an upper bound for the minimum. -/
public theorem curveChainDistance_le {Y : Scheme.{u}} {z : Y} {S : Set Y}
    (c : CurveChain Y z S) : curveChainDistance Y z S ≤ c.length :=
  iInf_le _ c

/-- A chain of curves ending in `S` ends in any larger set. -/
public def CurveChain.mono {Y : Scheme.{u}} {z : Y} {S S' : Set Y} (c : CurveChain Y z S)
    (h : S ⊆ S') : CurveChain Y z S' :=
  { c with pt_last_mem := h c.pt_last_mem }

/-- Enlarging the target set does not change the length of a chain of curves. -/
@[simp] public theorem CurveChain.length_mono {Y : Scheme.{u}} {z : Y} {S S' : Set Y}
    (c : CurveChain Y z S) (h : S ⊆ S') : (c.mono h).length = c.length := rfl

/-! ## The telescoping identity for the weight of a zigzag -/

/-- Splitting off the first term of a tail sum. -/
private lemma sum_ite_le_split {m : ℕ} (g : Fin m → ℤ) (a : ℕ) (i : Fin m) (hi : i.val = a) :
    (∑ j : Fin m, if a ≤ j.val then g j else 0) =
      g i + ∑ j : Fin m, if a + 1 ≤ j.val then g j else 0 := by
  classical
  subst hi
  have hterm : ∀ j : Fin m,
      ((if i.val ≤ j.val then g j else 0) - if i.val + 1 ≤ j.val then g j else 0) =
        if j = i then g j else 0 := by
    intro j
    by_cases h1 : i.val ≤ j.val
    · by_cases h2 : i.val + 1 ≤ j.val
      · have hne : j ≠ i := fun h => by rw [h] at h2; omega
        simp [h1, h2, hne]
      · have heq : j = i := Fin.ext (by omega)
        simp [heq]
    · have h2 : ¬ i.val + 1 ≤ j.val := by omega
      have hne : j ≠ i := fun h => by rw [h] at h1; omega
      simp [h1, h2, hne]
  have hsum := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hterm j)
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i g] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  linarith

/-- Only the last index contributes to a tail sum starting at the last index. -/
private lemma sum_ite_le_last {n : ℕ} (g : Fin (n + 1) → ℤ) :
    (∑ j : Fin (n + 1), if n ≤ j.val then g j else 0) = g (Fin.last n) := by
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro j _ hj
    have : ¬ n ≤ j.val := by
      have := j.isLt
      have : j.val ≠ n := fun h => hj (Fin.ext h)
      omega
    simp [this]
  · simp

/-- A tail sum over `Fin n` starting at the index `n` is empty. -/
private lemma sum_ite_le_last' {n : ℕ} (g : Fin n → ℤ) :
    (∑ j : Fin n, if n ≤ j.val then g j else 0) = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  have : ¬ n ≤ j.val := by have := j.isLt; omega
  simp [this]

variable {Y : Scheme.{u}}

/-- The generic point of the `i`-th lower endpoint of a zigzag. -/
public def lowerGenericPoint [IsNoetherian Y] {Z : Closeds Y} {y : Y}
    (s : DistanceSystem Y Z y) (i : Fin (s.k + 1)) : Y :=
  (s.V i).isIrreducible'.genericPoint

/-- **The telescoping identity.** For every index `i` of a zigzag from `Z` to `y`, the tail
`cᵢ + ⋯ + cₖ − bᵢ − ⋯ − bₖ₋₁` equals `δ(y) − δ(vᵢ)`, where `vᵢ` is the generic point of `Vᵢ`.
The upper endpoints cancel in pairs. -/
public theorem DistanceSystem.sum_sub_eq [IsNoetherian Y] (δ : DimensionFunction Y)
    {Z : Closeds Y} {y : Y} (s : DistanceSystem Y Z y) (i : Fin (s.k + 1)) :
    (∑ j : Fin (s.k + 1), if i.val ≤ j.val then (s.upCodimension j : ℤ) else 0) -
      (∑ j : Fin s.k, if i.val ≤ j.val then (s.downCodimension j : ℤ) else 0) =
      δ y - δ (lowerGenericPoint s i) := by
  classical
  have hsober : StacksSober Y :=
    stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩
  set v : Fin (s.k + 1) → Y := fun i => lowerGenericPoint s i
  set w : Fin (s.k + 1) → Y := fun i => (s.W i).isIrreducible'.genericPoint
  have hv : ∀ i, IsGenericPoint (v i) (s.V i : Set Y) := fun i =>
    (s.V i).isIrreducible'.isGenericPoint_genericPoint (s.V i).isClosed'
  have hw : ∀ i, IsGenericPoint (w i) (s.W i : Set Y) := fun i =>
    (s.W i).isIrreducible'.isGenericPoint_genericPoint (s.W i).isClosed'
  have hspecUp : ∀ i, w i ⤳ v i := fun i => (hw i).specializes (s.V_le_W i (hv i).mem)
  have hspecDown : ∀ i : Fin s.k, w i.castSucc ⤳ v i.succ := fun i =>
    (hw i.castSucc).specializes (s.V_next_le_W i (hv i.succ).mem)
  have hVIso : ∀ i, closureSingleton (v i) = s.V i := fun i =>
    IrreducibleCloseds.ext (hv i).def
  have hWIso : ∀ i, closureSingleton (w i) = s.W i := fun i =>
    IrreducibleCloseds.ext (hw i).def
  have h02 : ∀ a b : Y, a ⤳ b →
      IrreducibleClosedsCodim.topCodim (closureSingleton b) (closureSingleton a) =
        ((δ a - δ b).toNat : ℕ∞) :=
    fun a b hab => codim_closure_singleton_eq_delta_diff hsober δ.toFun
      δ.isDimensionFunctionForCatenary a b hab
  have hle : ∀ {a b : Y}, a ⤳ b → δ b ≤ δ a := by
    intro a b hab
    rcases eq_or_ne a b with rfl | hne
    · exact le_rfl
    · exact (δ.strictAnti_specializes hab hne).le
  have hupInt : ∀ i, (s.upCodimension i : ℤ) = δ (w i) - δ (v i) := by
    intro i
    unfold DistanceSystem.upCodimension
    rw [← hVIso i, ← hWIso i, h02 (w i) (v i) (hspecUp i), ENat.toNat_natCast,
      Int.toNat_of_nonneg (sub_nonneg.mpr (hle (hspecUp i)))]
  have hdownInt : ∀ i : Fin s.k,
      (s.downCodimension i : ℤ) = δ (w i.castSucc) - δ (v i.succ) := by
    intro i
    unfold DistanceSystem.downCodimension
    rw [← hVIso i.succ, ← hWIso i.castSucc, h02 (w i.castSucc) (v i.succ) (hspecDown i),
      ENat.toNat_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr (hle (hspecDown i)))]
  have hwlast : w (Fin.last s.k) = y := by
    apply (hw (Fin.last s.k)).eq
    rw [s.W_last_eq_closure]
    exact isGenericPoint_closure
  refine Fin.reverseInduction ?_ ?_ i
  · rw [show ((Fin.last s.k : Fin (s.k + 1)) : ℕ) = s.k from rfl, sum_ite_le_last,
      sum_ite_le_last', hupInt, hwlast]
    ring
  · intro j ih
    rw [show ((j.castSucc : Fin (s.k + 1)) : ℕ) = (j : ℕ) from rfl]
    rw [show ((j.succ : Fin (s.k + 1)) : ℕ) = (j : ℕ) + 1 from rfl] at ih
    rw [sum_ite_le_split (fun l : Fin (s.k + 1) => (s.upCodimension l : ℤ)) (j : ℕ)
        j.castSucc rfl,
      sum_ite_le_split (fun l : Fin s.k => (s.downCodimension l : ℤ)) (j : ℕ) j rfl]
    linarith [ih, hupInt j.castSucc, hdownInt j]

/-- **The weight of a zigzag.** It is `k + maxᵢ (δ(y) − δ(vᵢ))`, where `vᵢ` is the generic
point of the `i`-th lower endpoint. -/
public theorem DistanceSystem.weight_eq_add_sup [IsNoetherian Y] (δ : DimensionFunction Y)
    {Z : Closeds Y} {y : Y} (s : DistanceSystem Y Z y) :
    s.weight = s.k + (Finset.univ : Finset (Fin (s.k + 1))).sup
      (fun i => (δ y - δ (lowerGenericPoint s i)).toNat) := by
  classical
  unfold DistanceSystem.weight
  congr 1
  refine Finset.sup_congr rfl fun i _ => ?_
  have hmain := s.sum_sub_eq δ i
  have hup : ((∑ j : Fin (s.k + 1), if i.val ≤ j.val then s.upCodimension j else 0 : ℕ) : ℤ) =
      ∑ j : Fin (s.k + 1), if i.val ≤ j.val then (s.upCodimension j : ℤ) else 0 := by
    push_cast
    rfl
  have hdown : ((∑ j : Fin s.k, if i.val ≤ j.val then s.downCodimension j else 0 : ℕ) : ℤ) =
      ∑ j : Fin s.k, if i.val ≤ j.val then (s.downCodimension j : ℤ) else 0 := by
    push_cast
    rfl
  omega

/-! ## Values of a normalized dimension function -/

/-- A dimension function vanishing at the closed points of a Jacobson scheme is nonnegative:
every point specializes to a closed point. -/
public theorem dimensionFunction_nonneg [JacobsonSpace Y] (δ : DimensionFunction Y)
    (hδ : ∀ p : Y, IsClosed ({p} : Set Y) → δ p = 0) (x : Y) : 0 ≤ δ x := by
  obtain ⟨p, hpmem, hpcl⟩ := nonempty_inter_closedPoints
    (Set.singleton_nonempty x).closure isClosed_closure.isLocallyClosed
  have hspec : x ⤳ p := specializes_iff_mem_closure.mpr hpmem
  have h0 : δ p = 0 := hδ p (mem_closedPoints_iff.mp hpcl)
  rcases eq_or_ne x p with rfl | hne
  · omega
  · have := δ.strictAnti_specializes hspec hne
    omega

/-! ## The upper bound -/

/-- A chain of curves out of `z` ending in `closure {y}` puts `z` in the connected component
of `y`. -/
private lemma mem_connectedComponent_of_curveChain {z y : Y}
    (c : CurveChain Y z (closure {y})) : z ∈ connectedComponent y := by
  have hstep : ∀ j : Fin (c.length + 1),
      connectedComponent (c.pt 0) = connectedComponent (c.pt j) := by
    refine Fin.induction rfl ?_
    intro j ih
    rw [ih]
    have hsub := (c.curve j).isIrreducible'.isConnected.subset_connectedComponent
      (c.mem_castSucc j)
    exact connectedComponent_eq (hsub (c.mem_succ j))
  have h1 := hstep (Fin.last c.length)
  rw [c.pt_zero] at h1
  have h2 : connectedComponent (c.pt (Fin.last c.length)) = connectedComponent y := by
    have hymem : y ∈ closure ({y} : Set Y) := subset_closure rfl
    have hsub := (isIrreducible_singleton (x := y)).closure.isConnected
      |>.subset_connectedComponent hymem
    exact (connectedComponent_eq (hsub c.pt_last_mem)).symm
  rw [← h2, ← h1]
  exact mem_connectedComponent

/-- The distance from a closed point `z` is at most the supremum over a zigzag from `z` to `y`
of the quantities `δ(y) − δ(vᵢ)`, as `v₀ = z` and `δ(z) = 0`. -/
private lemma toNat_le_sup_lowerGenericPoint [IsNoetherian Y] (δ : DimensionFunction Y)
    (hδ : ∀ p : Y, IsClosed ({p} : Set Y) → δ p = 0) {z y : Y} (hz : IsClosed ({z} : Set Y))
    (s : DistanceSystem Y (⟨{z}, hz⟩ : Closeds Y) y) :
    (δ y).toNat ≤ (Finset.univ : Finset (Fin (s.k + 1))).sup
      (fun i => (δ y - δ (lowerGenericPoint s i)).toNat) := by
  have hv0 : lowerGenericPoint s ⟨0, Nat.zero_lt_succ s.k⟩ = z :=
    s.V_zero_subset ((s.V _).isIrreducible'.isGenericPoint_genericPoint (s.V _).isClosed').mem
  have hle := Finset.le_sup
    (f := fun i : Fin (s.k + 1) => (δ y - δ (lowerGenericPoint s i)).toNat)
    (Finset.mem_univ (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1)))
  rwa [hv0, hδ z hz, sub_zero] at hle

/-- **Stacks Project, Tag 0EJ1, closing sentence, upper bound.** A chain of curves of length `t`
connecting a closed point `z` to a closed point of `closure {y}` bounds the distance from `z`
to `y` by `δ(y) + t`.

The curve condition is not used: the bound holds for a chain of arbitrary integral closed
subschemes, which is the inequality of Stacks Remark 0EJ0. -/
public theorem distanceFunction_le_of_curveChain [IsNoetherian Y] [JacobsonSpace Y]
    (δ : DimensionFunction Y) (hδ : ∀ p : Y, IsClosed ({p} : Set Y) → δ p = 0)
    (z y : Y) (hz : IsClosed ({z} : Set Y)) (c : CurveChain Y z (closure {y})) :
    distanceFunction Y (⟨{z}, hz⟩ : Closeds Y) y ≤ ((δ y).toNat : ℕ∞) + c.length := by
  classical
  have hsober : StacksSober Y :=
    stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩
  -- the chain puts `z` in the connected component of `y`
  have hmeet : (connectedComponent y ∩ ({z} : Set Y)).Nonempty :=
    ⟨z, mem_connectedComponent_of_curveChain c, rfl⟩
  -- the zigzag attached to the chain
  let W : Fin (c.length + 1) → IrreducibleCloseds Y := fun i =>
    if h : (i : ℕ) < c.length then c.curve ⟨i, h⟩ else closureSingleton y
  have hWlt : ∀ (i : Fin (c.length + 1)) (h : (i : ℕ) < c.length), W i = c.curve ⟨i, h⟩ := by
    intro i h
    simp only [W, dif_pos h]
  have hWlast : W (Fin.last c.length) = closureSingleton y := by
    simp only [W, Fin.val_last, dif_neg (lt_irrefl c.length)]
  let s : DistanceSystem Y (⟨{z}, hz⟩ : Closeds Y) y :=
    { k := c.length
      V := fun i => closureSingleton (c.pt i)
      W := W
      V_le_W := by
        intro i
        rcases lt_or_ge (i : ℕ) c.length with h | h
        · rw [hWlt i h, ← SetLike.coe_subset_coe, coe_closureSingleton]
          refine closure_minimal (Set.singleton_subset_iff.mpr ?_) (c.curve _).isClosed'
          have := c.mem_castSucc ⟨i, h⟩
          rwa [show (⟨(i : ℕ), h⟩ : Fin c.length).castSucc = i from Fin.ext rfl] at this
        · have hi : i = Fin.last c.length :=
            Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
          subst hi
          rw [hWlast, ← SetLike.coe_subset_coe, coe_closureSingleton, coe_closureSingleton]
          exact closure_minimal (Set.singleton_subset_iff.mpr c.pt_last_mem) isClosed_closure
      V_next_le_W := by
        intro i
        have hi : (i.castSucc : ℕ) < c.length := by simp
        rw [hWlt i.castSucc hi, ← SetLike.coe_subset_coe, coe_closureSingleton]
        refine closure_minimal (Set.singleton_subset_iff.mpr ?_) (c.curve _).isClosed'
        have := c.mem_succ i
        rwa [show (⟨(i.castSucc : ℕ), hi⟩ : Fin c.length) = i from Fin.ext rfl]
      V_zero_subset := by
        show (closureSingleton (c.pt 0) : Set Y) ⊆ ({z} : Set Y)
        rw [coe_closureSingleton, c.pt_zero, hz.closure_eq]
      W_last_eq_closure := by
        rw [hWlast]
        exact coe_closureSingleton y }
  -- the generic points of the lower endpoints are the junction points of the chain
  have hgen : ∀ i : Fin (s.k + 1), lowerGenericPoint s i = c.pt i := by
    intro i
    have h1 : IsGenericPoint (lowerGenericPoint s i) (s.V i : Set Y) :=
      (s.V i).isIrreducible'.isGenericPoint_genericPoint (s.V i).isClosed'
    have h2 : IsGenericPoint (c.pt i) (s.V i : Set Y) := by
      show IsGenericPoint (c.pt i) ((closureSingleton (c.pt i) : IrreducibleCloseds Y) : Set Y)
      rw [coe_closureSingleton]
      exact isGenericPoint_closure
    exact h1.eq h2
  have hsup : (Finset.univ : Finset (Fin (s.k + 1))).sup
      (fun i => (δ y - δ (lowerGenericPoint s i)).toNat) = (δ y).toNat := by
    refine le_antisymm (Finset.sup_le fun i _ => ?_) ?_
    · have := dimensionFunction_nonneg δ hδ (lowerGenericPoint s i)
      omega
    · exact toNat_le_sup_lowerGenericPoint δ hδ hz s
  have hweight : s.weight = (δ y).toNat + c.length := by
    rw [s.weight_eq_add_sup δ, hsup]
    show c.length + (δ y).toNat = (δ y).toNat + c.length
    omega
  calc distanceFunction Y (⟨{z}, hz⟩ : Closeds Y) y ≤ (s.weight : ℕ∞) := by
        rw [distanceFunction_eq_iInf_of_nonempty Y _ y hmeet]
        exact iInf_le _ s
    _ = ((δ y).toNat : ℕ∞) + c.length := by rw [hweight]; push_cast; ring

/-- **Stacks Project, Tag 0EJ1, closing sentence, upper bound.** The distance from a closed point
`z` to `y` is at most `δ(y)` plus the minimum length of a chain of curves connecting `z` to a
closed point of `closure {y}`.

This is one of the two bounds of the closing sentence of the example; the equality is
`distanceFunction_eq_topologicalKrullDim_add_curveChainDistance`, which carries the tag. -/
public theorem distanceFunction_le_add_curveChainDistance [IsNoetherian Y] [JacobsonSpace Y]
    (δ : DimensionFunction Y) (hδ : ∀ p : Y, IsClosed ({p} : Set Y) → δ p = 0)
    (z y : Y) (hz : IsClosed ({z} : Set Y)) :
    distanceFunction Y (⟨{z}, hz⟩ : Closeds Y) y ≤
      ((δ y).toNat : ℕ∞) + curveChainDistance Y z (closure {y}) := by
  rw [curveChainDistance, ENat.add_iInf]
  exact le_iInf fun c => distanceFunction_le_of_curveChain δ hδ z y hz c

/-! ## The lower bound in terms of the length of a zigzag -/

/-- Every zigzag from a closed point `z` to `y` has weight at least `δ(y) + k`, where `k` is
its number of descending legs. -/
public theorem add_distanceSystem_k_le_weight [IsNoetherian Y] [JacobsonSpace Y]
    (δ : DimensionFunction Y) (hδ : ∀ p : Y, IsClosed ({p} : Set Y) → δ p = 0)
    (z y : Y) (hz : IsClosed ({z} : Set Y))
    (s : DistanceSystem Y (⟨{z}, hz⟩ : Closeds Y) y) :
    (δ y).toNat + s.k ≤ s.weight := by
  have := toNat_le_sup_lowerGenericPoint δ hδ hz s
  rw [s.weight_eq_add_sup δ]
  omega

/-- **Stacks Project, Tag 0EJ1, closing sentence, lower bound.** The distance from a closed point
`z` to `y` is at least `δ(y)` plus the least number of descending legs of a zigzag from `z` to
`y`. -/
public theorem add_le_distanceFunction [IsNoetherian Y] [JacobsonSpace Y]
    (δ : DimensionFunction Y) (hδ : ∀ p : Y, IsClosed ({p} : Set Y) → δ p = 0)
    (z y : Y) (hz : IsClosed ({z} : Set Y)) :
    ((δ y).toNat : ℕ∞) + (⨅ s : DistanceSystem Y (⟨{z}, hz⟩ : Closeds Y) y, (s.k : ℕ∞)) ≤
      distanceFunction Y (⟨{z}, hz⟩ : Closeds Y) y := by
  classical
  by_cases hmeet : (connectedComponent y ∩ (({z} : Set Y))).Nonempty
  · rw [distanceFunction_eq_iInf_of_nonempty Y (⟨{z}, hz⟩ : Closeds Y) y hmeet, ENat.add_iInf]
    refine le_iInf fun s => le_trans (iInf_le _ s) ?_
    exact_mod_cast add_distanceSystem_k_le_weight δ hδ z y hz s
  · rw [distanceFunction_eq_top_of_disjoint Y (⟨{z}, hz⟩ : Closeds Y) y hmeet]
    exact le_top

/-! ## The equality, modulo connecting two closed points by a curve -/

/-- A sequence of closed points in which consecutive members either agree or lie on a common
curve is a chain of curves, of length at most the number of steps. -/
private lemma exists_curveChain_of_steps (z : Y) (n : ℕ) : ∀ p : Fin (n + 1) → Y,
    p 0 = z →
    (∀ i, IsClosed ({p i} : Set Y)) →
    (∀ i : Fin n, p i.castSucc = p i.succ ∨
      ∃ C : IrreducibleCloseds Y, IsCurveIn C ∧ p i.castSucc ∈ (C : Set Y) ∧
        p i.succ ∈ (C : Set Y)) →
    ∃ c : CurveChain Y z {p (Fin.last n)}, c.length ≤ n := by
  induction n with
  | zero =>
      intro p hp0 hpcl _
      have hzcl : IsClosed ({z} : Set Y) := by rw [← hp0]; exact hpcl 0
      exact ⟨⟨0, fun _ => z, fun i => i.elim0, fun i => i.elim0, rfl, hp0.symm, hzcl,
        fun i => i.elim0, fun i => i.elim0⟩, le_rfl⟩
  | succ n ih =>
      intro p hp0 hpcl hstep
      obtain ⟨c', hc'⟩ := ih (fun i : Fin (n + 1) => p i.castSucc) hp0
        (fun i => hpcl i.castSucc)
        (fun i => by
          have h := hstep i.castSucc
          rwa [show (i.castSucc : Fin (n + 1)).succ = i.succ.castSucc from rfl] at h)
      have hlastmem : c'.pt (Fin.last c'.length) = p (Fin.last n).castSucc := c'.pt_last_mem
      rcases hstep (Fin.last n) with heq | ⟨C, hC, hmem1, hmem2⟩
      · -- the last step is trivial: the chain already ends at the final point
        refine ⟨c'.mono ?_, le_trans hc' (Nat.le_succ n)⟩
        rw [Set.singleton_subset_iff, Set.mem_singleton_iff, heq,
          show (Fin.last n).succ = Fin.last (n + 1) from rfl]
      · -- append the curve `C` of the last step
        refine ⟨{ length := c'.length + 1
                  pt := Fin.snoc c'.pt (p (Fin.last (n + 1)))
                  curve := Fin.snoc c'.curve C
                  isCurve := ?_
                  pt_zero := ?_
                  pt_last_mem := ?_
                  pt_last_isClosed := ?_
                  mem_castSucc := ?_
                  mem_succ := ?_ }, Nat.succ_le_succ hc'⟩
        · refine Fin.lastCases ?_ ?_
          · rw [Fin.snoc_last]; exact hC
          · intro j; rw [Fin.snoc_castSucc]; exact c'.isCurve j
        · rw [show (0 : Fin (c'.length + 2)) = (0 : Fin (c'.length + 1)).castSucc from rfl,
            Fin.snoc_castSucc]
          exact c'.pt_zero
        · rw [Fin.snoc_last]
          exact rfl
        · rw [Fin.snoc_last]
          exact hpcl (Fin.last (n + 1))
        · refine Fin.lastCases ?_ ?_
          · rw [Fin.snoc_last, Fin.snoc_castSucc, hlastmem]
            exact hmem1
          · intro j
            rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
            exact c'.mem_castSucc j
        · refine Fin.lastCases ?_ ?_
          · rw [Fin.snoc_last, show (Fin.last c'.length).succ = Fin.last (c'.length + 1) from rfl,
              Fin.snoc_last]
            rw [show (Fin.last n).succ = Fin.last (n + 1) from rfl] at hmem2
            exact hmem2
          · intro j
            rw [Fin.snoc_castSucc,
              show (j.castSucc : Fin (c'.length + 1)).succ = j.succ.castSucc from rfl,
              Fin.snoc_castSucc]
            exact c'.mem_succ j

/-- Every zigzag from a closed point `z` to `y` yields a chain of curves from `z` to a closed
point of `closure {y}` of length at most the number of descending legs of the zigzag: two
distinct closed points of an integral closed subscheme of `Y` lie on a common curve
(`Stacks.Algebraization.CurveThroughPoints.exists_dim_one_of_mem`). -/
private lemma curveChainDistance_le_distanceSystem_k {k : Type u} [Field k]
    (f : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (z y : Y) (hz : IsClosed ({z} : Set Y))
    (s : DistanceSystem Y (⟨{z}, hz⟩ : Closeds Y) y) :
    curveChainDistance Y z (closure {y}) ≤ s.k := by
  classical
  let : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
  -- a closed point on each lower endpoint of the zigzag
  have hex : ∀ i : Fin (s.k + 1),
      ∃ q : Y, q ∈ (s.V i : Set Y) ∧ IsClosed ({q} : Set Y) := by
    intro i
    obtain ⟨q, hq, hqcl⟩ := nonempty_inter_closedPoints (s.V i).isIrreducible'.nonempty
      (s.V i).isClosed'.isLocallyClosed
    exact ⟨q, hq, mem_closedPoints_iff.mp hqcl⟩
  choose q hqmem hqcl using hex
  have hzero : (0 : Fin (s.k + 1)) = ⟨0, Nat.zero_lt_succ s.k⟩ := Fin.ext (by simp)
  have hq0 : q 0 = z := by
    rw [hzero]
    exact s.V_zero_subset (hqmem _)
  -- consecutive points lie on a common upper endpoint, hence on a common curve
  have hstep : ∀ i : Fin s.k, q i.castSucc = q i.succ ∨
      ∃ C : IrreducibleCloseds Y, IsCurveIn C ∧ q i.castSucc ∈ (C : Set Y) ∧
        q i.succ ∈ (C : Set Y) := by
    intro i
    rcases eq_or_ne (q i.castSucc) (q i.succ) with h | h
    · exact Or.inl h
    · exact Or.inr (CurveThroughPoints.exists_dim_one_of_mem f (s.W i.castSucc)
        (s.V_le_W i.castSucc (hqmem i.castSucc)) (s.V_next_le_W i (hqmem i.succ))
        (hqcl i.castSucc) (hqcl i.succ) h)
  obtain ⟨c, hc⟩ := exists_curveChain_of_steps z s.k q hq0 hqcl hstep
  have hsub : ({q (Fin.last s.k)} : Set Y) ⊆ closure {y} := by
    rw [Set.singleton_subset_iff, ← s.W_last_eq_closure]
    exact s.V_le_W (Fin.last s.k) (hqmem (Fin.last s.k))
  exact le_trans (curveChainDistance_le (c.mono hsub)) (Nat.cast_le.mpr hc)

/-- **The closing sentence of Stacks Example 0EJ1, for a dimension function vanishing at closed
points.** For `Y` of finite type over a field, `z` a closed point and `δ` a dimension function on
`Y` vanishing at the closed points, the distance `δ_Z(y)` from `Z = {z}` is `δ(y) + t`, where `t`
is the minimum length of a chain of curves connecting `z` to a closed point of `closure {y}`.

On a scheme of finite type over a field such a `δ` is the usual dimension function
`y ↦ dim closure {y}`; `distanceFunction_eq_topologicalKrullDim_add_curveChainDistance` states the
equality with that function written out. -/
public theorem distanceFunction_eq_add_curveChainDistance
    {k : Type u} [Field k] (f : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (δ : DimensionFunction Y)
    (hδ : ∀ p : Y, IsClosed ({p} : Set Y) → δ p = 0)
    (z y : Y) (hz : IsClosed ({z} : Set Y)) :
    let : IsNoetherian Y :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
    distanceFunction Y (⟨{z}, hz⟩ : Closeds Y) y =
      ((δ y).toNat : ℕ∞) + curveChainDistance Y z (closure {y}) := by
  classical
  let : IsNoetherian Y :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
  let : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
  show distanceFunction Y (⟨{z}, hz⟩ : Closeds Y) y =
    ((δ y).toNat : ℕ∞) + curveChainDistance Y z (closure {y})
  refine le_antisymm (distanceFunction_le_add_curveChainDistance δ hδ z y hz) ?_
  by_cases hmeet : (connectedComponent y ∩ (({z} : Set Y))).Nonempty
  · rw [distanceFunction_eq_iInf_of_nonempty Y (⟨{z}, hz⟩ : Closeds Y) y hmeet]
    refine le_iInf fun s => ?_
    calc ((δ y).toNat : ℕ∞) + curveChainDistance Y z (closure {y})
        ≤ ((δ y).toNat : ℕ∞) + (s.k : ℕ∞) :=
          add_le_add le_rfl (curveChainDistance_le_distanceSystem_k f z y hz s)
      _ ≤ (s.weight : ℕ∞) := by
          exact_mod_cast add_distanceSystem_k_le_weight δ hδ z y hz s
  · rw [distanceFunction_eq_top_of_disjoint Y (⟨{z}, hz⟩ : Closeds Y) y hmeet]
    exact le_top

/-- **Stacks Project, Tag 0EJ1, closing sentence.** Let `Y` be of finite type over a field and
`Z = {z}` a closed point. Then `δ_Z(y) = δ(y) + t`, where `δ(y) = dim closure {y}` is the usual
dimension function and `t` is the minimum length of a chain of curves connecting `z` to a closed
point of `closure {y}`.

Both sides may be infinite: `t = ∞` when no chain of curves exists, which happens exactly when
`z` and `y` lie in different connected components, and then `δ_Z(y) = ∞` as well. The equality is
read in `WithBot ℕ∞`, where `dim closure {y}` lives. -/
@[stacks 0EJ1 "A generalization of case (1) is if Y is of finite type over a field and
Z = {z} is a closed point. Then δ_Z(y) = δ(y) + t where t is the minimum length of a chain of
curves connecting z to a closed point of the closure of {y}."]
public theorem distanceFunction_eq_topologicalKrullDim_add_curveChainDistance
    {k : Type u} [Field k] (f : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (z y : Y) (hz : IsClosed ({z} : Set Y)) :
    let : IsNoetherian Y :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
    ((distanceFunction Y (⟨{z}, hz⟩ : Closeds Y) y : ℕ∞) : WithBot ℕ∞) =
      topologicalKrullDim (closure ({y} : Set Y)) +
        ((curveChainDistance Y z (closure {y}) : ℕ∞) : WithBot ℕ∞) := by
  intro
  let : Algebra k (Y.residueField y) := CurveThroughPoints.residueAlgebra f y
  have hδ : ∀ p : Y, IsClosed ({p} : Set Y) →
      residueFieldTrdegDimensionFunction k Y f p = 0 := fun p hp => by
    show ((natTrdegResidueField k Y f p : ℕ) : ℤ) = 0
    rw [natTrdegResidueField_eq_zero_of_isClosed k Y f p hp]
    rfl
  have h := distanceFunction_eq_add_curveChainDistance f
    (residueFieldTrdegDimensionFunction k Y f) hδ z y hz
  rw [h, topologicalKrullDim_closure_singleton_eq_trdeg k Y f y]
  have : FinTrdeg k (Y.residueField y) := residueField_finTrdeg k f y
  have hfin : Algebra.trdeg k (Y.residueField y) < Cardinal.aleph0 :=
    trdeg_lt_aleph0 k _
  show (((((natTrdegResidueField k Y f y : ℕ) : ℤ).toNat : ℕ∞) +
      curveChainDistance Y z (closure {y}) : ℕ∞) : WithBot ℕ∞) = _
  rw [Int.toNat_natCast]
  have hcast : ((natTrdegResidueField k Y f y : ℕ) : ℕ∞) =
      Cardinal.toENat (Algebra.trdeg k (Y.residueField y)) := by
    show ((Cardinal.toNat (Algebra.trdeg k (Y.residueField y)) : ℕ) : ℕ∞) = _
    exact Cardinal.natCast_eq_toENat.mpr (Cardinal.cast_toNat_of_lt_aleph0 hfin)
  rw [hcast]
  push_cast
  rfl

end Stacks.Algebraization

end
