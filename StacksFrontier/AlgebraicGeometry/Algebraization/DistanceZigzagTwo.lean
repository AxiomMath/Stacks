module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceFunction

/-!
# A zigzag of weight two

Let `Y` be a Noetherian scheme and `Z ⊆ Y` closed. Suppose a point `z ∈ Z` is an immediate
specialization of a point `v`, that `v` is an immediate specialization of a point `w`, and that
`w` specializes to a point `y` through a strict chain `w ⤳ c ⤳ y` of length two. Then the
zigzag

`{z}‾ ⊆ {v}‾ = {v}‾ ⊆ {w}‾ ⊇ {y}‾ = {y}‾`

has weight `2 + max(c₀ + c₁ − b₁, c₁ − b₁, 0)` with `c₀, c₁ ≤ 1` and `b₁ ≥ 2`, which is `2`, so
the distance `δ^Y_Z(y)` of Stacks 0EIX is at most two, however large the dimension of `{y}‾` is.

This is the mechanism by which `δ^Y_Z(y)` falls below `dim({y}‾)` on a non-catenary scheme: the
zigzag passes through a generic point `w` whose closure contains a curve `{v}‾` through `z` of
codimension one.

## Main results

* `Stacks.Algebraization.distanceFunction_le_two_of_zigzag` — the bound.

## References

* [Stacks Project, Tag 0EIX](https://stacks.math.columbia.edu/tag/0EIX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Algebraization

variable {X : Type*} [TopologicalSpace X]

/-- A specialization `a ⤳ b` gives an inclusion of closures `{b}‾ ⊆ {a}‾`. -/
private theorem closureSingleton_le_of_specializes {a b : X} (h : a ⤳ b) :
    IrreducibleCloseds.closureSingleton b ≤ IrreducibleCloseds.closureSingleton a := by
  show closure ({b} : Set X) ⊆ closure {a}
  exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp h))
    isClosed_closure

/-- A strict specialization in a `T0` space strictly shrinks closures. -/
private theorem closureSingleton_lt_of_specializes [T0Space X] {a b : X} (h : a ⤳ b)
    (hne : a ≠ b) :
    IrreducibleCloseds.closureSingleton b < IrreducibleCloseds.closureSingleton a := by
  refine lt_of_le_of_ne (closureSingleton_le_of_specializes h) fun heq => hne ?_
  have hcl : closure ({b} : Set X) = closure {a} :=
    congrArg (fun C : IrreducibleCloseds X => (C : Set X)) heq
  have hba : b ⤳ a := by
    rw [specializes_iff_mem_closure, hcl]
    exact subset_closure rfl
  exact (h.antisymm hba).eq

/-- If nothing lies strictly between `a` and its specialization `b`, the closure of `b` has
codimension at most one in the closure of `a`. -/
public theorem topCodim_closureSingleton_le_one_of_forall [QuasiSober X] [T0Space X] {a b : X}
    (hcov : ∀ x, a ⤳ x → x ⤳ b → x = a ∨ x = b) :
    IrreducibleClosedsCodim.topCodim (IrreducibleCloseds.closureSingleton b)
      (IrreducibleCloseds.closureSingleton a) ≤ 1 := by
  rw [IrreducibleClosedsCodim.topCodim_le_iff]
  intro p hh hl
  by_contra hcon
  have hlen : 2 ≤ p.length := by
    by_contra h2
    exact hcon (by exact_mod_cast (show p.length ≤ 1 by omega))
  set C := p.toFun ⟨1, by omega⟩ with hC
  have h₁ : p.head < C := p.strictMono (by simp [Fin.lt_def])
  have h₂ : C < p.last := p.strictMono (by simp [Fin.lt_def]; omega)
  rw [hh] at h₁
  rw [hl] at h₂
  obtain ⟨g, hg⟩ := QuasiSober.sober C.isIrreducible C.isClosed
  have hgen : IrreducibleCloseds.closureSingleton g = C :=
    IrreducibleCloseds.ext hg.def
  have hag : a ⤳ g := by
    rw [specializes_iff_mem_closure]
    exact h₂.le (hg.mem)
  have hgb : g ⤳ b := by
    rw [specializes_iff_mem_closure]
    have : (closure ({b} : Set X) : Set X) ⊆ C := h₁.le
    rw [hg.def]
    exact this (subset_closure rfl)
  rcases hcov g hag hgb with rfl | rfl
  · exact lt_irrefl _ (hgen ▸ h₂)
  · exact lt_irrefl _ (hgen ▸ h₁)

/-- A strict chain `a ⤳ c ⤳ b` makes the closure of `b` of codimension at least two in the
closure of `a`. -/
public theorem two_le_topCodim_closureSingleton_of_specializes [T0Space X] {a c b : X}
    (hac : a ⤳ c) (hcb : c ⤳ b) (hac' : a ≠ c) (hcb' : c ≠ b) :
    (2 : ℕ∞) ≤ IrreducibleClosedsCodim.topCodim (IrreducibleCloseds.closureSingleton b)
      (IrreducibleCloseds.closureSingleton a) := by
  have h₁ := closureSingleton_lt_of_specializes hcb hcb'
  have h₂ := closureSingleton_lt_of_specializes hac hac'
  let p : LTSeries (IrreducibleCloseds X) :=
    ⟨2, ![IrreducibleCloseds.closureSingleton b, IrreducibleCloseds.closureSingleton c,
      IrreducibleCloseds.closureSingleton a], fun i => by
        fin_cases i
        · exact h₁
        · exact h₂⟩
  exact IrreducibleClosedsCodim.length_le_topCodim _ _ p rfl rfl

/-- **Stacks Project, Tag 0EIX.** In a Noetherian scheme, if a point `z` of `Z` is an
immediate specialization of `v`, `v` an immediate specialization of `w`, and `w ⤳ c ⤳ y` is a
strict chain of length two, then `δ^Y_Z(y) ≤ 2`. -/
@[stacks 0EIX "a zigzag of weight two"]
public theorem distanceFunction_le_two_of_zigzag (Y : Scheme.{u}) [IsNoetherian Y]
    (Z : Closeds Y) {z v w c y : Y} (hz : z ∈ (Z : Set Y))
    (hvz : v ⤳ z) (hcovvz : ∀ x, v ⤳ x → x ⤳ z → x = v ∨ x = z)
    (hwv : w ⤳ v) (hcovwv : ∀ x, w ⤳ x → x ⤳ v → x = w ∨ x = v)
    (hwc : w ⤳ c) (hcy : c ⤳ y) (hwc' : w ≠ c) (hcy' : c ≠ y) :
    distanceFunction Y Z y ≤ 2 := by
  classical
  let cz := IrreducibleCloseds.closureSingleton z
  let cv := IrreducibleCloseds.closureSingleton v
  let cw := IrreducibleCloseds.closureSingleton w
  let cy := IrreducibleCloseds.closureSingleton y
  have hzv : cz ≤ cv := closureSingleton_le_of_specializes hvz
  have hvw : cv ≤ cw := closureSingleton_le_of_specializes hwv
  have hyw : cy ≤ cw := closureSingleton_le_of_specializes (hwc.trans hcy)
  let s : DistanceSystem Y Z y :=
    { k := 2
      V := ![cz, cv, cy]
      W := ![cv, cw, cy]
      V_le_W := by
        intro i
        fin_cases i
        · exact hzv
        · exact hvw
        · exact le_rfl
      V_next_le_W := by
        intro i
        fin_cases i
        · exact le_rfl
        · exact hyw
      V_zero_subset := by
        show closure ({z} : Set Y) ⊆ (Z : Set Y)
        exact closure_minimal (Set.singleton_subset_iff.mpr hz) Z.isClosed
      W_last_eq_closure := rfl }
  have hc0 : s.upCodimension 0 ≤ 1 :=
    ENat.toNat_le_of_le_natCast (topCodim_closureSingleton_le_one_of_forall hcovvz)
  have hc1 : s.upCodimension 1 ≤ 1 :=
    ENat.toNat_le_of_le_natCast (topCodim_closureSingleton_le_one_of_forall hcovwv)
  have hc2 : s.upCodimension 2 = 0 := by
    show (IrreducibleClosedsCodim.topCodim cy cy).toNat = 0
    simp [topCodim_self_eq_zero]
  have hb1 : 2 ≤ s.downCodimension 1 := by
    have h := two_le_topCodim_closureSingleton_of_specializes hwc hcy hwc' hcy'
    show 2 ≤ (IrreducibleClosedsCodim.topCodim cy cw).toNat
    simpa using ENat.toNat_le_toNat h (topCodim_ne_top Y cy cw)
  have hweight : s.weight ≤ 2 := by
    show 2 + (Finset.univ : Finset (Fin 3)).sup (fun i =>
        (∑ j : Fin 3, if i.val ≤ j.val then s.upCodimension j else 0) -
        (∑ j : Fin 2, if i.val ≤ j.val then s.downCodimension j else 0)) ≤ 2
    have hb0 : s.downCodimension 0 = 0 := by
      show (IrreducibleClosedsCodim.topCodim cv cv).toNat = 0
      simp [topCodim_self_eq_zero]
    refine (Nat.add_le_add_left (Finset.sup_le (a := 0) fun i _ => ?_) 2).trans_eq rfl
    fin_cases i <;>
      simp only [Fin.sum_univ_three, Fin.sum_univ_two] <;> simp <;> omega
  have hcomp : (connectedComponent y ∩ (Z : Set Y)).Nonempty := by
    refine ⟨z, ?_, hz⟩
    have hsub : closure ({w} : Set Y) ⊆ connectedComponent y :=
      (isIrreducible_singleton.closure.isConnected.isPreconnected).subset_connectedComponent
        (specializes_iff_mem_closure.mp (hwc.trans hcy))
    exact hsub (specializes_iff_mem_closure.mp (hwv.trans hvz))
  rw [distanceFunction_eq_iInf_of_nonempty Y Z y hcomp]
  exact (iInf_le _ s).trans (by exact_mod_cast hweight)

end Stacks.Algebraization

end
