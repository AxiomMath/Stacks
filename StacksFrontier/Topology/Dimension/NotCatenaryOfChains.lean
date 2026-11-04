module

public import StacksFrontier.Topology.Dimension.Catenary
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# A criterion for a space not to be catenary

In a quasi-sober `T0` space, a chain of specializations `a ⤳ b ⤳ c` with nothing strictly
between consecutive members is a maximal chain of irreducible closed subsets of length two. If
`a ⤳ p ⤳ q ⤳ c` is a strict chain of length three, the space is not catenary.

## Main results

* `TopologicalSpace.not_isCatenarySpace_of_specializes`: the criterion.
-/

@[expose] public section

open TopologicalSpace IrreducibleCloseds

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]

/-- **A space with a maximal chain of length two and a chain of length three between the same
points is not catenary.** -/
theorem not_isCatenarySpace_of_specializes {a b c p q : X} (hab : a ⤳ b) (hbc : b ⤳ c)
    (hab' : a ≠ b) (hbc' : b ≠ c)
    (hcov₁ : ∀ z, a ⤳ z → z ⤳ b → z = a ∨ z = b)
    (hcov₂ : ∀ z, b ⤳ z → z ⤳ c → z = b ∨ z = c)
    (hap : a ⤳ p) (hpq : p ⤳ q) (hqc : q ⤳ c) (hap' : a ≠ p) (hpq' : p ≠ q) (hqc' : q ≠ c) :
    ¬ IrreducibleClosedsCodim.IsCatenarySpace X := by
  intro hcat
  -- Specialization is reversed inclusion of the closures of points.
  have hsp : ∀ {x y : X}, closureSingleton y ≤ closureSingleton x ↔ x ⤳ y := by
    intro x y
    rw [← SetLike.coe_subset_coe, coe_closureSingleton, coe_closureSingleton,
      specializes_iff_closure_subset]
  -- A strict specialization strictly shrinks closures.
  have hlt : ∀ {x y : X}, x ⤳ y → x ≠ y → closureSingleton y < closureSingleton x :=
    fun hxy hne ↦ lt_of_le_not_ge (hsp.2 hxy) fun h ↦ hne (hxy.antisymm (hsp.1 h)).eq
  -- Every irreducible closed set is the closure of a point.
  have hgen : ∀ Y : IrreducibleCloseds X, ∃ z, Y = closureSingleton z := by
    intro Y
    obtain ⟨z, hz⟩ := QuasiSober.sober Y.isIrreducible Y.isClosed
    refine ⟨z, IrreducibleCloseds.ext ?_⟩
    rw [coe_closureSingleton]
    exact hz.symm
  -- A covering pair of points gives a covering pair of closures.
  have hcov : ∀ {x y : X}, x ⤳ y → x ≠ y → (∀ z, x ⤳ z → z ⤳ y → z = x ∨ z = y) →
      closureSingleton y ⋖ closureSingleton x := by
    intro x y hxy hne hz
    refine ⟨hlt hxy hne, fun Y h₁ h₂ ↦ ?_⟩
    obtain ⟨z, rfl⟩ := hgen Y
    have hzx : x ⤳ z := hsp.1 h₂.le
    have hyz : z ⤳ y := hsp.1 h₁.le
    rcases hz z hzx hyz with rfl | rfl
    · exact (lt_irrefl _ h₂)
    · exact (lt_irrefl _ h₁)
  set Yc := closureSingleton c
  set Ya := closureSingleton a
  -- The maximal chain of length two.
  let p₂ : LTSeries (IrreducibleCloseds X) :=
    ⟨2, ![Yc, closureSingleton b, Ya], fun i ↦ by
      fin_cases i
      · exact hlt hbc hbc'
      · exact hlt hab hab'⟩
  have hmax : IrreducibleClosedsCodim.IsMaximalChain p₂ Yc Ya := by
    refine ⟨rfl, rfl, fun i ↦ ?_⟩
    fin_cases i
    · exact hcov hbc hbc' hcov₂
    · exact hcov hab hab' hcov₁
  -- The chain of length three.
  let p₃ : LTSeries (IrreducibleCloseds X) :=
    ⟨3, ![Yc, closureSingleton q, closureSingleton p, Ya], fun i ↦ by
      fin_cases i
      · exact hlt hqc hqc'
      · exact hlt hpq hpq'
      · exact hlt hap hap'⟩
  have hle : Yc ≤ Ya := ((hlt hbc hbc').trans (hlt hab hab')).le
  obtain ⟨-, hlen⟩ := hcat Yc Ya hle
  have h₂ := hlen p₂ hmax
  have h₃ := IrreducibleClosedsCodim.length_le_topCodim Yc Ya p₃ rfl rfl
  rw [← h₂] at h₃
  change ((3 : ℕ) : ℕ∞) ≤ ((2 : ℕ) : ℕ∞) at h₃
  have : (3 : ℕ) ≤ 2 := ENat.natCast_le_natCast.1 h₃
  omega

end TopologicalSpace

end
