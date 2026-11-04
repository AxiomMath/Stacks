module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceFunction
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceSublevel
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceVanishing
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksFrontier.Topology.Dimension.DimensionFunction

/-!
# Distance along specializations

On a Noetherian catenary scheme, the distance from a closed subset at the generic point
of an immediate specialization is at most one more than its distance at the special point.
Iterating this along a zigzag whose leftward legs are immediate specializations bounds the
distance at the final point by the number of legs.

## Main results

* `Stacks.Algebraization.distanceFunction_le_add_one_of_isImmediateSpecialization` bounds the
  distance at the generic point of an immediate specialization.
* `Stacks.Algebraization.distanceFunction_le_of_zigzag_specializations` gives the bound for a
  zigzag indexed by `Fin (k + 1)` and `Fin k`.

## Implementation notes

The distance is the extended-natural-valued function `Stacks.Algebraization.distanceFunction`,
so the first inequality also covers the case of infinite distance. In the zigzag the points
`y i` are the vertices and `y' i` are the intervening points: the leftward leg from `y' i` to
`y i` is immediate, while the rightward leg from `y' i` to `y (i + 1)` is an arbitrary
specialization, along which the sublevel sets of the distance are stable.

## References

* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Algebraization

open IrreducibleClosedsCodim

/-- Specialization reverses the order on closures of points. -/
private theorem closureSingleton_le_of_specializes {Y : Type u} [TopologicalSpace Y] {x y : Y}
    (h : x ⤳ y) :
    IrreducibleCloseds.closureSingleton y ≤ IrreducibleCloseds.closureSingleton x :=
  Specializes.closure_subset h

/-- The closure of a point covers the closure of an immediate specialization of it: a
strictly intermediate irreducible closed subset would have a strictly intermediate generic
point. -/
private theorem closureSingleton_covBy_of_isImmediateSpecialization
    {Y : Type u} [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
    {x y : Y} (h : IsImmediateSpecialization x y) :
    IrreducibleCloseds.closureSingleton y ⋖ IrreducibleCloseds.closureSingleton x := by
  have hne : closure ({y} : Set Y) ≠ closure ({x} : Set Y) := by
    intro heq
    exact h.2.1 (inseparable_iff_closure_eq.mpr heq.symm).eq
  refine ⟨?_, ?_⟩
  · exact lt_of_le_of_ne (closureSingleton_le_of_specializes h.1)
      (fun e => hne (by simpa using congrArg (fun z : IrreducibleCloseds Y => (z : Set Y)) e))
  · intro z hlow hhigh
    obtain ⟨g, hg⟩ := QuasiSober.sober z.isIrreducible z.isClosed
    have hgz : closure ({g} : Set Y) = (z : Set Y) := isGenericPoint_def.mp hg
    have htop : x ⤳ g := specializes_iff_mem_closure.mpr (hhigh.le hg.mem)
    have hbot : g ⤳ y := hg.specializes_iff_mem.mpr (hlow.le (subset_closure rfl))
    obtain rfl | rfl := h.2.2 g htop hbot
    · exact hhigh.ne (SetLike.coe_injective hgz.symm)
    · exact hlow.ne (SetLike.coe_injective hgz)

/-- Move a system ending at `y` to one ending at the generic point `y'` of an immediate
specialization, by enlarging its last upper endpoint to the closure of `y'`. -/
private def specializeDistanceSystem {Y : Scheme.{u}} [IsNoetherian Y]
    {Z : Closeds Y} {y' y : Y} (h : IsImmediateSpecialization y' y)
    (s : DistanceSystem Y Z y) :
    DistanceSystem Y Z y' := by
  classical
  refine ⟨s.k, s.V,
    Function.update s.W (Fin.last s.k) (IrreducibleCloseds.closureSingleton y'), ?_, ?_,
    s.V_zero_subset, ?_⟩
  · intro i
    by_cases hi : i = Fin.last s.k
    · subst i
      simp only [Function.update_self]
      have hVW : s.V (Fin.last s.k) ≤ IrreducibleCloseds.closureSingleton y := by
        simpa [s.W_last_eq_closureSingleton] using s.V_le_W (Fin.last s.k)
      exact le_trans hVW (closureSingleton_le_of_specializes h.1)
    · rw [Function.update_of_ne hi]
      exact s.V_le_W i
  · intro i
    rw [Function.update_of_ne (Fin.castSucc_ne_last i)]
    exact s.V_next_le_W i
  · simp

/-- Enlarging the last upper endpoint across one immediate specialization raises the weight
by at most one: the last ascending codimension grows by exactly one and no descending
codimension changes. -/
private theorem specializeDistanceSystem_weight_le {Y : Scheme.{u}} [IsNoetherian Y]
    (hY : IrreducibleClosedsCodim.IsCatenarySpace Y) {Z : Closeds Y}
    {y' y : Y} (h : IsImmediateSpecialization y' y)
    (s : DistanceSystem Y Z y) :
    (specializeDistanceSystem h s).weight ≤ s.weight + 1 := by
  classical
  let t := specializeDistanceSystem h s
  let last : Fin (s.k + 1) := Fin.last s.k
  have hlast : s.W last = IrreducibleCloseds.closureSingleton y :=
    s.W_last_eq_closureSingleton
  have hVW : s.V last ≤ s.W last := s.V_le_W last
  have hWW' : s.W last ≤ IrreducibleCloseds.closureSingleton y' :=
    hlast ▸ closureSingleton_le_of_specializes h.1
  have hcover : IrreducibleCloseds.closureSingleton y ⋖
      IrreducibleCloseds.closureSingleton y' :=
    closureSingleton_covBy_of_isImmediateSpecialization h
  have hcod : topCodim (s.V last) (IrreducibleCloseds.closureSingleton y') =
      topCodim (s.V last) (s.W last) + 1 := by
    rw [topCodim_additive_of_catenary hY (s.V last) (s.W last)
      (IrreducibleCloseds.closureSingleton y') hVW hWW', hlast,
      topCodim_eq_one_of_covby _ _ hcover]
  have hupLast : t.upCodimension last = s.upCodimension last + 1 := by
    show (topCodim (s.V last)
      (Function.update s.W (Fin.last s.k)
        (IrreducibleCloseds.closureSingleton y') last)).toNat =
      (topCodim (s.V last) (s.W last)).toNat + 1
    rw [Function.update_self, hcod]
    cases hval : topCodim (s.V last) (s.W last) with
    | top => exact (topCodim_ne_top_of_catenary hY _ _ hVW hval).elim
    | coe n => rfl
  have hup (j : Fin (s.k + 1)) :
      t.upCodimension j = s.upCodimension j + if j = last then 1 else 0 := by
    by_cases hj : j = last
    · subst j
      simp [hupLast]
    · have hj' : j ≠ Fin.last s.k := by simpa [last] using hj
      show (topCodim (s.V j)
        (Function.update s.W (Fin.last s.k)
          (IrreducibleCloseds.closureSingleton y') j)).toNat =
            s.upCodimension j + if j = last then 1 else 0
      rw [Function.update_of_ne hj']
      show (topCodim (s.V j) (s.W j)).toNat =
        (topCodim (s.V j) (s.W j)).toNat + if j = last then 1 else 0
      simp [hj]
  have hdown (j : Fin s.k) : t.downCodimension j = s.downCodimension j := by
    show (topCodim (s.V (Fin.succ j))
      (Function.update s.W (Fin.last s.k)
        (IrreducibleCloseds.closureSingleton y') (Fin.castSucc j))).toNat =
          s.downCodimension j
    rw [Function.update_of_ne (Fin.castSucc_ne_last j)]
    rfl
  let f₀ : Fin (s.k + 1) → ℕ := fun i =>
    (∑ j : Fin (s.k + 1), if i.val ≤ j.val then s.upCodimension j else 0) -
    (∑ j : Fin s.k, if i.val ≤ j.val then s.downCodimension j else 0)
  let f₁ : Fin (s.k + 1) → ℕ := fun i =>
    (∑ j : Fin (s.k + 1), if i.val ≤ j.val then t.upCodimension j else 0) -
    (∑ j : Fin s.k, if i.val ≤ j.val then t.downCodimension j else 0)
  have hsum (i : Fin (s.k + 1)) :
      (∑ j : Fin (s.k + 1), if i.val ≤ j.val then t.upCodimension j else 0) =
        (∑ j : Fin (s.k + 1), if i.val ≤ j.val then s.upCodimension j else 0) + 1 := by
    calc
      _ = (∑ j : Fin (s.k + 1), if i.val ≤ j.val then s.upCodimension j else 0) +
          ∑ j : Fin (s.k + 1),
            if i.val ≤ j.val then (if j = last then 1 else 0) else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hup j]
        split_ifs <;> simp
      _ = _ := by
        congr 1
        have hi : i.val ≤ last.val := i.is_le
        rw [Finset.sum_eq_single last]
        · simp [hi]
        · intro j hj hne
          simp [hne]
        · simp
  have hf (i : Fin (s.k + 1)) : f₁ i ≤ f₀ i + 1 := by
    dsimp [f₀, f₁]
    rw [hsum i]
    simp only [hdown]
    omega
  have hsup : (Finset.univ : Finset (Fin (s.k + 1))).sup f₁ ≤
      (Finset.univ : Finset (Fin (s.k + 1))).sup f₀ + 1 :=
    Finset.sup_le fun i _ => (hf i).trans
      (Nat.add_le_add_right (Finset.le_sup (f := f₀) (Finset.mem_univ i)) 1)
  show s.k + (Finset.univ : Finset (Fin (s.k + 1))).sup f₁ ≤
    (s.k + (Finset.univ : Finset (Fin (s.k + 1))).sup f₀) + 1
  omega

/-- **Stacks Project, Tag 0EIY.** An immediate specialization raises the distance from a
closed subset by at most one when passing from the special point to the generic point. -/
@[stacks 0EIY "immediate_specialization_bound"]
public theorem distanceFunction_le_add_one_of_isImmediateSpecialization
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y)
    (hY : IrreducibleClosedsCodim.IsCatenarySpace Y)
    {y' y : Y} (h : IsImmediateSpecialization y' y) :
    distanceFunction Y Z y' ≤ distanceFunction Y Z y + 1 := by
  classical
  by_cases hmeet : (connectedComponent y ∩ (Z : Set Y)).Nonempty
  · have hcomp : connectedComponent y' = connectedComponent y :=
      connectedComponent_eq (isIrreducible_singleton.closure.isConnected.subset_connectedComponent
        (x := y') (subset_closure rfl) (specializes_iff_mem_closure.mp h.1))
    have hmeet' : (connectedComponent y' ∩ (Z : Set Y)).Nonempty := by
      simpa [hcomp] using hmeet
    rw [distanceFunction_eq_iInf_of_nonempty Y Z y hmeet]
    have := nonempty_distanceSystem_of_connectedComponent_inter Y Z y hmeet
    obtain ⟨s₀, hs₀⟩ := ENat.exists_eq_iInf
      (fun s : DistanceSystem Y Z y => (s.weight : ℕ∞))
    calc
      distanceFunction Y Z y' ≤ ((specializeDistanceSystem h s₀).weight : ℕ∞) := by
        rw [distanceFunction_eq_iInf_of_nonempty Y Z y' hmeet']
        exact iInf_le _ (specializeDistanceSystem h s₀)
      _ ≤ (s₀.weight : ℕ∞) + 1 := by
        exact_mod_cast specializeDistanceSystem_weight_le hY h s₀
      _ = (⨅ s : DistanceSystem Y Z y, (s.weight : ℕ∞)) + 1 := by rw [hs₀]
  · rw [distanceFunction_eq_top_of_disjoint Y Z y hmeet]
    exact le_top

/-- **Stacks Project, Tag 0EIY.** In a zigzag starting in `Z`, each immediate leftward
specialization increases the possible distance by at most one. -/
@[stacks 0EIY "zigzag_bound"]
public theorem distanceFunction_le_of_zigzag_specializations
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y)
    (hY : IrreducibleClosedsCodim.IsCatenarySpace Y)
    (k : ℕ) (y : Fin (k + 1) → Y) (y' : Fin k → Y)
    (hzero : y ⟨0, Nat.zero_lt_succ k⟩ ∈ (Z : Set Y))
    (hleft : ∀ i : Fin k, IsImmediateSpecialization (y' i) (y (Fin.castSucc i)))
    (hright : ∀ i : Fin k, y' i ⤳ y (Fin.succ i)) :
    distanceFunction Y Z (y (Fin.last k)) ≤ (k : ℕ∞) := by
  have hbound : ∀ i : Fin (k + 1), distanceFunction Y Z (y i) ≤ (i.val : ℕ∞) := by
    intro i
    induction i using Fin.induction with
    | zero => simpa using (distanceFunction_eq_zero_iff_mem Y Z _).2 hzero |>.le
    | succ i hi =>
        simpa using distanceFunction_sublevel_stableUnderSpecialization Y Z
          ((i.val + 1 : ℕ) : ℕ∞) (hright i)
          ((distanceFunction_le_add_one_of_isImmediateSpecialization Y Z hY (hleft i)).trans
            (by simpa using add_le_add_right hi 1))
  simpa using hbound (Fin.last k)

end Stacks.Algebraization
