module

public import StacksFrontier.AlgebraicGeometry.CompactOpenInduction.Basic

/-!
# The induction of [Stacks, Tag 08DR] from a local class of affine opens

`StacksFrontier/AlgebraicGeometry/CompactOpenInduction/Basic.lean` propagates a property `P` of
opens from **every** affine open to every quasi-compact open. Sometimes the affine base case is
only available on the affine opens satisfying a side condition `T` which holds locally and is
inherited by smaller opens -- for instance "an invertible module is trivial here".

That is enough to reach every affine open `W` on which `T` holds locally: `W` is a finite union
of basic opens on which `T` holds, and the class of finite unions of basic opens of `W` is
stable under the intersections the Mayer--Vietoris induction creates, because
`D(g) ⊓ D(h) = D(gh)` and `D(gh) ≤ D(g)` inherits `T`.

## Main results

* `Stacks.AlgebraicGeometry.CompactOpenInduction.of_iSup_basicOpen_of_forall`: `P` holds for a
  finite union of basic opens of an affine open on each of which `T` holds.
* `Stacks.AlgebraicGeometry.CompactOpenInduction.of_isAffineOpen_of_locally`: `P` holds for every
  affine open on which `T` holds locally.

## References

* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.CompactOpenInduction

variable {X : Scheme.{u}} {P T : X.Opens → Prop}
  (hT : ∀ U V : X.Opens, U ≤ V → T V → T U)
  (hbot : P ⊥)
  (h₁ : ∀ U : X.Opens, IsAffineOpen U → T U → P U)
  (h₂ : ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V →
    P U → P V → P (U ⊓ V) → P (U ⊔ V))

include hT hbot h₁ h₂ in
/-- **The affine step of [Stacks, Tag 08DR] under a local side condition.** If `T` is inherited
by smaller opens, `P` holds for the affine opens satisfying `T` and `P` is stable under the
Mayer--Vietoris union step, then `P` holds for every finite union of basic opens
`X.basicOpen (g i)` of an affine open `W` on each of which `T` holds.

The induction creates the intersection
`(⨆ i ∈ s, D (g i)) ⊓ D (g a) = ⨆ i ∈ s, D (g i * g a)`, whose members are contained in the
`D (g i)`, so `T` holds on them as well. -/
theorem of_iSup_basicOpen_of_forall {W : X.Opens} (hW : IsAffineOpen W) {ι : Type*} :
    ∀ (n : ℕ) (s : Finset ι) (g : ι → Γ(X, W)), s.card ≤ n →
      (∀ i ∈ s, T (X.basicOpen (g i))) → P (⨆ i ∈ s, X.basicOpen (g i)) := by
  classical
  intro n
  induction n with
  | zero =>
    intro s g hs _
    obtain rfl : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
    simpa using hbot
  | succ n ih =>
    intro s g hs hTg
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simpa using hbot
    · have hcard : (s.erase a).card ≤ n := by
        have := Finset.card_erase_of_mem ha
        have := Finset.card_pos.mpr ⟨a, ha⟩
        omega
      have key : (⨆ i ∈ s, X.basicOpen (g i))
          = (⨆ i ∈ s.erase a, X.basicOpen (g i)) ⊔ X.basicOpen (g a) := by
        conv_lhs => rw [← Finset.insert_erase ha]
        rw [Finset.iSup_insert, sup_comm]
      have hTe : ∀ i ∈ s.erase a, T (X.basicOpen (g i)) :=
        fun i hi => hTg i (Finset.mem_of_mem_erase hi)
      rw [key]
      refine h₂ _ _ ?_ (hW.basicOpen _) (ih _ _ hcard hTe)
        (h₁ _ (hW.basicOpen _) (hTg a ha)) ?_
      · simp only [Opens.coe_iSup]
        exact Set.Finite.isCompact_biUnion (s.erase a).finite_toSet
          fun i _ => (hW.basicOpen (g i)).isCompact
      · have e : (⨆ i ∈ s.erase a, X.basicOpen (g i)) ⊓ X.basicOpen (g a)
            = ⨆ i ∈ s.erase a, X.basicOpen (g i * g a) := by
          simp only [iSup_inf_eq, ← Scheme.basicOpen_mul]
        rw [e]
        exact ih _ _ hcard fun i hi =>
          hT _ _ ((Scheme.basicOpen_mul ..).trans_le inf_le_left) (hTe i hi)

include hT hbot h₁ h₂ in
/-- **`P` holds for every affine open on which the side condition holds locally.** Such an open
is quasi-compact, so it is a finite union of basic opens satisfying `T`, and
`of_iSup_basicOpen_of_forall` applies. -/
theorem of_isAffineOpen_of_locally (W : X.Opens) (hW : IsAffineOpen W)
    (hcover : ∀ x ∈ W, ∃ g : Γ(X, W), x ∈ X.basicOpen g ∧ T (X.basicOpen g)) : P W := by
  classical
  choose G hG₁ hG₂ using fun x : W => hcover x.1 x.2
  obtain ⟨σ, hσ⟩ := hW.isCompact.elim_finite_subcover
    (fun x : W => (X.basicOpen (G x) : Set X))
    (fun x => (X.basicOpen (G x)).isOpen)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hG₁ ⟨x, hx⟩⟩)
  have hWeq : W = ⨆ i ∈ σ, X.basicOpen (G i) := by
    refine le_antisymm (fun x hx => ?_)
      (iSup_le fun i => iSup_le fun _ => X.basicOpen_le (G i))
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hσ hx)
    exact Opens.mem_iSup.2 ⟨i, Opens.mem_iSup.2 ⟨hi, hxi⟩⟩
  rw [hWeq]
  exact of_iSup_basicOpen_of_forall hT hbot h₁ h₂ hW σ.card σ G le_rfl fun i _ => hG₂ i

end Stacks.AlgebraicGeometry.CompactOpenInduction
