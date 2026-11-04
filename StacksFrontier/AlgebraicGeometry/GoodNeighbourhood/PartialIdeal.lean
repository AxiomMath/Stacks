module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.GoodSections
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic

/-!
# The ideals of the partial intersections `V(v₁, …, v_m)`

Elementary properties of `AlgebraicGeometry.GoodNeighbourhood.partialIdeal`: it is `⊥` for `m = 0`,
adds one zero scheme at each step, and is compatible with pullback, the zero scheme of a pulled
back section being the inverse image of the zero scheme ([Stacks, Tag 0B6Y]).

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.partialIdeal_zero`
* `AlgebraicGeometry.GoodNeighbourhood.partialIdeal_succ`
* `AlgebraicGeometry.GoodNeighbourhood.comap_partialIdeal`
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

variable {X : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] {c : ℕ}
  (v : Fin c → Γ(L, ⊤))

/-- `V(∅)` is the whole scheme. -/
theorem partialIdeal_zero : partialIdeal L v 0 = ⊥ := by
  simp [partialIdeal]

/-- Each zero scheme `V(v_j)` with `j < m` is contained in `V(v₁, …, v_m)`. -/
private theorem zeroScheme_le_partialIdeal {m : ℕ} (j : Fin c) (hj : j.val < m) :
    zeroScheme X L (v j) ≤ partialIdeal L v m :=
  le_iSup₂_of_le (f := fun (j : Fin c) (_ : j.val < m) => zeroScheme X L (v j)) j hj le_rfl

/-- `V(v₁, …, v_{m+1}) = V(v₁, …, v_m) ∩ V(v_{m+1})`. -/
theorem partialIdeal_succ (m : ℕ) (hm : m < c) :
    partialIdeal L v (m + 1) = partialIdeal L v m ⊔ zeroScheme X L (v ⟨m, hm⟩) := by
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact le_sup_of_le_left (zeroScheme_le_partialIdeal L v j h)
    · obtain rfl : j = ⟨m, hm⟩ := Fin.ext h
      exact le_sup_right
  · exact sup_le (iSup₂_le fun j hj => zeroScheme_le_partialIdeal L v j (Nat.lt_succ_of_lt hj))
      (zeroScheme_le_partialIdeal L v ⟨m, hm⟩ m.lt_succ_self)

/-- **The partial intersections pull back to the partial intersections of the pulled-back
sections.** -/
theorem comap_partialIdeal {X' : Scheme.{u}} (g : X' ⟶ X) (m : ℕ) :
    (partialIdeal L v m).comap g =
      partialIdeal ((Scheme.Modules.pullback g).obj L)
        (fun j => pullbackGlobalSections g L (v j)) m := by
  simp only [partialIdeal, (Scheme.IdealSheafData.map_gc g).l_iSup,
    ← Stacks.Divisors.zeroScheme_pullback g L]

end AlgebraicGeometry.GoodNeighbourhood

end
