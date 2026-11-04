module

public import Mathlib.Data.Fintype.Perm
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FiveChain
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.LongChain

/-!
# The endpoint of a chain of minus-two indices

Let `v 0, …, v (s - 1)` be a chain of at least five distinct minus-two indices
in a proper subset of the components of a numerical type, and suppose the
weights of all the interior vertices are known to be a common value `w`. This
file records what is then forced at the endpoint `v 0`: its weight is `w`, or
half of `w`, or twice `w`, with the first edge scaled to match, and it meets no
vertex of the chain other than `v 1`.

These are exactly the three endpoint scalings of the long-chain classification
and of the `A₅`/`B₅`/`C₅` classification of a five-chain, transported to the
left-hand end of the chain. The fork classification uses the result twice: once
along the long arm of the fork and once along the arm that ends in the branch
vertex.

## Main results

* `AlgebraicGeometry.NumericalType.chain_endpoint_pattern`: the endpoint
  weight, the first edge, and the vanishing of the remaining intersections at
  the endpoint.

## Implementation notes

The chain is indexed by `Fin s` rather than by a subset of the components, so
the hypothesis `hinj` records distinctness and `hproper` records that the chain
misses a component. The two cases `s = 5` and `5 < s` are handled separately
because the five-vertex classification is stated up to a permutation of the
five indices while the long-chain classification is stated up to reversal only.

## References

* [Stacks Project, Tag 0C82](https://stacks.math.columbia.edu/tag/0C82)
* [Stacks Project, Tag 0C89](https://stacks.math.columbia.edu/tag/0C89)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

open Matrix

/-- The endpoint pattern at the start of a chain of more than five minus-two
indices, read off from the long-chain classification applied to the chain and
to its reversal. -/
private lemma longChain_endpoint_pattern {s : ℕ} (T : NumericalType)
    (v : Fin s → Fin T.componentCount) (hs : 5 < s)
    (hproper : s < T.componentCount) (hinj : Function.Injective v)
    (hminus : ∀ j, IsMinusTwoIndex T (v j))
    (hadjacent : ∀ j k, k.val = j.val + 1 →
      T.intersection (v j) (v k) ≠ 0)
    (w : ℤ)
    (hknown : ∀ j, 0 < j.val → j.val + 1 < s → T.weight (v j) = w) :
    ((T.weight (v ⟨0, by omega⟩) = w ∧
        T.intersection (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) = w) ∨
      (2 * T.weight (v ⟨0, by omega⟩) = w ∧
        T.intersection (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) = w) ∨
      (T.weight (v ⟨0, by omega⟩) = 2 * w ∧
        T.intersection (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) = 2 * w)) ∧
      (∀ j, 2 ≤ j.val → T.intersection (v ⟨0, by omega⟩) (v j) = 0) := by
  classical
  let z : Fin s := ⟨0, by omega⟩
  let o : Fin s := ⟨1, by omega⟩
  let p : Fin s := ⟨s - 2, by omega⟩
  let l : Fin s := ⟨s - 1, by omega⟩
  let r : Fin s → Fin T.componentCount := fun j => v (Fin.rev j)
  have hz : Fin.rev z = l := Fin.ext (by simp [Fin.rev, z, l])
  have ho : Fin.rev o = p := Fin.ext (by simp [Fin.rev, o, p])
  have hp : Fin.rev p = o := Fin.ext (by simp [Fin.rev, o, p]; omega)
  have hl : Fin.rev l = z := Fin.ext (by simp [Fin.rev, z, l]; omega)
  have hclass := classify_long_chain_of_minus_two_indices T v hs hproper hinj hminus hadjacent
  have hknownO := hknown o (by simp [o]) (by simp [o]; omega)
  have hknownP : T.weight (v p) = w := hknown p (by simp [p]; omega) (by simp [p]; omega)
  have hrev {a : ℤ} (h : T.intersection (r p) (r l) = a) : T.intersection (v z) (v o) = a := by
    rw [T.intersection_symm]
    simpa [r, hp, hl] using h
  have hEndpoint :
      ((T.weight (v z) = w ∧ T.intersection (v z) (v o) = w) ∨
        (2 * T.weight (v z) = w ∧ T.intersection (v z) (v o) = w) ∨
        (T.weight (v z) = 2 * w ∧ T.intersection (v z) (v o) = 2 * w)) := by
    rcases hclass with hcfg | hcfg
    · rcases hcfg with ⟨u, hw, he, -⟩ | ⟨u, hw, -, he, -, -⟩ | ⟨u, hw, -, he, -⟩
      · have hu : u = w := (hw o).symm.trans hknownO
        exact Or.inl ⟨hu ▸ hw z, hu ▸ he z o rfl⟩
      · have hu : u = w := (hw o (by simp [o]; omega)).symm.trans hknownO
        exact Or.inl ⟨hu ▸ hw z (by simp [z]; omega), hu ▸ he z o rfl (by simp [o]; omega)⟩
      · have hu : 2 * u = w := (hw o (by simp [o]; omega)).symm.trans hknownO
        exact Or.inl ⟨hu ▸ hw z (by simp [z]; omega), hu ▸ he z o rfl⟩
    · change IsLongChainConfiguration T r at hcfg
      rcases hcfg with ⟨u, hw, he, -⟩ | ⟨u, hw, hlast, -, heLast, -⟩ | ⟨u, hw, hlast, he, -⟩
      · have hu : u = w := by simpa [r, ho] using (hw o).symm.trans hknownP
        exact Or.inl ⟨by simpa [r, hz, hl, hu] using hw l,
          hu ▸ hrev (he p l (by simp [p, l]; omega))⟩
      · have hu : u = w := by
          simpa [r, ho] using (hw o (by simp [o]; omega)).symm.trans hknownP
        exact Or.inr (Or.inr ⟨by simpa [r, hz, hl, hu] using hlast l (by simp [l]; omega),
          hu ▸ hrev (heLast p l (by simp [p, l]; omega) (by simp [l]; omega))⟩)
      · have hu : 2 * u = w := by
          simpa [r, ho] using (hw o (by simp [o]; omega)).symm.trans hknownP
        have hx : T.weight (v z) = u := by simpa [r, hz, hl] using hlast l (by simp [l]; omega)
        exact Or.inr (Or.inl ⟨hx ▸ hu, hu ▸ hrev (he p l (by simp [p, l]; omega))⟩)
  have hZero : ∀ j, 2 ≤ j.val → T.intersection (v z) (v j) = 0 := by
    intro j hj
    rcases hclass with hcfg | hcfg
    · rcases hcfg with ⟨_, -, -, hzero⟩ | ⟨_, -, -, -, -, hzero⟩ | ⟨_, -, -, -, hzero⟩ <;>
        exact hzero z j (by simp [z]; omega)
    · rcases hcfg with ⟨_, -, -, hzero⟩ | ⟨_, -, -, -, -, hzero⟩ | ⟨_, -, -, -, hzero⟩ <;>
      · rw [T.intersection_symm]
        simpa [hl, Fin.rev_rev] using hzero (Fin.rev j) l (by simp [Fin.rev, l]; omega)
  exact ⟨hEndpoint, hZero⟩

/-- A permutation of `Fin 5` whose consecutive images always differ by one is
the identity or the reversal. -/
private lemma fin5_path_order :
    ∀ (p : Equiv.Perm (Fin 5)),
    (∀ j : Fin 4,
      (p j.castSucc).val + 1 = (p j.succ).val ∨
        (p j.succ).val + 1 = (p j.castSucc).val) →
    (∀ j, p j = j) ∨ (∀ j, p j = Fin.rev j) := by
  decide +kernel

/-- The endpoint pattern at the start of a chain of exactly five minus-two
indices, read off from the `A₅`/`B₅`/`C₅` classification. -/
private lemma five_chain_endpoint_pattern (T : NumericalType)
    (hcount : 5 < T.componentCount)
    (v : Fin 5 → Fin T.componentCount) (hv : Function.Injective v)
    (hminus : ∀ j, IsMinusTwoIndex T (v j))
    (hadj : ∀ j : Fin 4,
      T.intersection (v j.castSucc) (v j.succ) ≠ 0)
    (w : ℤ) (hknown : T.weight (v 1) = w) :
    ((T.weight (v 0) = w ∧ T.intersection (v 0) (v 1) = w) ∨
      (2 * T.weight (v 0) = w ∧ T.intersection (v 0) (v 1) = w) ∨
      (T.weight (v 0) = 2 * w ∧ T.intersection (v 0) (v 1) = 2 * w)) ∧
      (∀ j, 2 ≤ j.val → T.intersection (v 0) (v j) = 0) := by
  classical
  obtain ⟨σ, u, -, hcfg⟩ := five_chain_is_A5_or_C5_or_B5 T hcount v hv hminus hadj
  have hconfigAdjacent : ∀ a b : Fin 5, a ≠ b →
      T.intersection (v (σ a)) (v (σ b)) ≠ 0 →
        (a.val + 1 = b.val ∨ b.val + 1 = a.val) := by
    intro a b hab hn
    rcases hcfg with ⟨-, hm, -⟩ | ⟨-, hm, -⟩ | ⟨-, hm, -⟩ <;>
    · rw [show T.intersection (v (σ a)) (v (σ b)) = _ from congrFun (congrFun hm a) b] at hn
      fin_cases a <;> fin_cases b <;> simp_all
  have hpAdj (j : Fin 4) :
      (σ.symm j.castSucc).val + 1 = (σ.symm j.succ).val ∨
        (σ.symm j.succ).val + 1 = (σ.symm j.castSucc).val :=
    hconfigAdjacent _ _ (σ.symm.injective.ne fun h => by simp [Fin.ext_iff] at h)
      (by simpa using hadj j)
  have hσid (hid : ∀ j, σ.symm j = j) : σ = Equiv.refl (Fin 5) :=
    Equiv.ext fun a => by simpa using (hid (σ a)).symm
  have hσrev (hrev : ∀ j, σ.symm j = Fin.rev j) : σ = Fin.revPerm := Equiv.ext fun a => by
    have hh : a = Fin.rev (σ a) := by simpa using hrev (σ a)
    simpa [Fin.rev_rev] using (congrArg Fin.rev hh).symm
  rcases (fin5_path_order σ.symm hpAdj).imp hσid hσrev with hσ | hσ <;>
  rcases hcfg with ⟨hw, hm, -⟩ | ⟨hw, hm, -⟩ | ⟨hw, hm, -⟩ <;>
  · have h0 := congrFun hw (σ.symm 0)
    have h1 := congrFun hw (σ.symm 1)
    have e := congrFun (congrFun hm (σ.symm 0)) (σ.symm 1)
    simp [hσ, Fin.rev] at h0 h1 e
    refine ⟨by omega, fun j hj => ?_⟩
    have hj0 := congrFun (congrFun hm (σ.symm 0)) (σ.symm j)
    obtain rfl | rfl | rfl :=
      (by decide : ∀ j : Fin 5, 2 ≤ j.val → j = 2 ∨ j = 3 ∨ j = 4) j hj <;>
    simpa [hσ, Fin.rev] using hj0

/-- At the start of a chain of at least five minus-two indices whose interior
weights are all `w`, the endpoint weight is `w`, half of `w`, or twice `w`, the
first edge is scaled to match, and the endpoint meets no other vertex of the
chain. -/
public lemma chain_endpoint_pattern {s : ℕ} (T : NumericalType)
    (v : Fin s → Fin T.componentCount) (hs : 5 ≤ s)
    (hproper : s < T.componentCount) (hinj : Function.Injective v)
    (hminus : ∀ j, IsMinusTwoIndex T (v j))
    (hadj : ∀ j k, k.val = j.val + 1 →
      T.intersection (v j) (v k) ≠ 0)
    (w : ℤ)
    (hknown : ∀ j, 0 < j.val → j.val + 1 < s → T.weight (v j) = w) :
    ((T.weight (v ⟨0, by omega⟩) = w ∧
        T.intersection (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) = w) ∨
      (2 * T.weight (v ⟨0, by omega⟩) = w ∧
        T.intersection (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) = w) ∨
      (T.weight (v ⟨0, by omega⟩) = 2 * w ∧
        T.intersection (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) = 2 * w)) ∧
      (∀ j, 2 ≤ j.val →
        T.intersection (v ⟨0, by omega⟩) (v j) = 0) := by
  by_cases hlong : 5 < s
  · exact longChain_endpoint_pattern T v hlong hproper hinj hminus hadj w hknown
  · obtain rfl : s = 5 := by omega
    exact five_chain_endpoint_pattern T (by omega) v hinj hminus
      (fun j => hadj j.castSucc j.succ (by simp)) w (hknown 1 (by decide) (by decide))

end AlgebraicGeometry.NumericalType
