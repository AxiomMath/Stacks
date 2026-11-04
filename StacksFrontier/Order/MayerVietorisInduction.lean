module

public import Mathlib.Data.Finset.Lattice.Fold

/-!
# The Mayer–Vietoris induction on a finite cover

Let `P` be a property of elements of a distributive lattice (for instance of the open subsets
of a space) satisfying the Mayer–Vietoris principle: `P a`, `P b` and `P (a ⊓ b)` imply
`P (a ⊔ b)`. If `P` holds for every finite meet of members of a finite nonempty family, it
holds for the join of the family. This is the induction on the number of opens of a cover by
which Poincaré duality is glued from the members of a cover all of whose finite intersections
satisfy it; in the purity step of the proof of Poincaré duality the cover is one on which a
smooth closed subscheme is cut out by a flag of smooth divisors, a property inherited by every
open subset.

## Main results

* `Finset.prop_sup'_of_prop_inf'`.
-/

@[expose] public section

namespace Finset

variable {α ι : Type*} [DistribLattice α]

/-- **Mayer–Vietoris induction.** If `P` satisfies `P a → P b → P (a ⊓ b) → P (a ⊔ b)` and holds
for the meet of every nonempty subfamily of `U` indexed by `s`, it holds for the join of the
family. -/
theorem prop_sup'_of_prop_inf' (P : α → Prop)
    (hMV : ∀ a b, P a → P b → P (a ⊓ b) → P (a ⊔ b)) {s : Finset ι} (hs : s.Nonempty) :
    ∀ U : ι → α, (∀ K ⊆ s, ∀ hK : K.Nonempty, P (K.inf' hK U)) → P (s.sup' hs U) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro U hU
    simpa using hU {a} subset_rfl (singleton_nonempty a)
  | cons a s ha hs ih =>
    intro U hU
    rw [sup'_cons hs]
    have hA : P (s.sup' hs U) := ih U fun K hK hKn => hU K (hK.trans (subset_cons ha)) hKn
    have hB : P (U a) := by simpa using hU {a} (by simp) (singleton_nonempty a)
    have hAB : P (s.sup' hs U ⊓ U a) := by
      rw [sup'_inf_distrib_right]
      refine ih (fun i => U i ⊓ U a) fun K hK hKn => ?_
      have := hU (cons a K fun h => ha (hK h)) (cons_subset_cons.2 hK) (cons_nonempty _)
      rw [inf'_cons hKn] at this
      have e : K.inf' hKn (fun i => U i ⊓ U a) = U a ⊓ K.inf' hKn U := by
        obtain ⟨i₀, hi₀⟩ := hKn
        exact le_antisymm
          (le_inf ((inf'_le _ hi₀).trans inf_le_right)
            (le_inf' _ _ fun i hi => (inf'_le _ hi).trans inf_le_left))
          (le_inf' _ _ fun i hi => le_inf (inf_le_right.trans (inf'_le _ hi)) inf_le_left)
      rwa [e]
    rw [sup_comm]
    exact hMV _ _ hA hB hAB

end Finset
