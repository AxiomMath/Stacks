module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober

/-!
# Closed subsets of large codimension

Let `X` be a scheme of finite dimension `d` and let `Z ⊆ X` be a closed subset all of whose
points `z` have local rings `𝒪_{X,z}` of dimension at least `q`. Then `dim Z ≤ d - q`: a chain of
irreducible closed subsets of `Z` ending in `Z' = closure {η}` extends, through the chain of
generalizations of `η` given by the primes of `𝒪_{X,η}`, to a chain of irreducible closed
subsets of `X` that is `q` steps longer.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_le_sub_of_le_ringKrullDim_stalk`
-/

@[expose] public section

open TopologicalSpace Order

universe u

namespace AlgebraicGeometry

/-- **A closed subset whose points have local rings of dimension at least `q` has dimension at
most `d - q`**, on a scheme of dimension `d`. -/
theorem topologicalKrullDim_le_sub_of_le_ringKrullDim_stalk {X : Scheme.{u}} {d : ℕ}
    (hd : topologicalKrullDim X = d) {Z : Set X} (hZ : IsClosed Z) {q : ℕ}
    (hq : ∀ z ∈ Z, (q : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk z)) :
    topologicalKrullDim Z ≤ ((d - q : ℕ) : WithBot ℕ∞) := by
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun C => ?_
  let g : IrreducibleCloseds Z → IrreducibleCloseds X := fun A =>
    ⟨Subtype.val '' (A : Set Z), A.isIrreducible.image _ continuous_subtype_val.continuousOn,
      hZ.isClosedMap_subtype_val _ A.isClosed⟩
  have hg : StrictMono g := by
    intro A B hAB
    rw [← SetLike.coe_ssubset_coe] at hAB ⊢
    exact Subtype.val_injective.image_strictMono hAB
  let η : X := irreducibleSetEquivPoints (g C)
  have : Nonempty X := ⟨η⟩
  have hηZ : η ∈ Z := by
    obtain ⟨z, -, hz⟩ : η ∈ (g C : Set X) :=
      ((g C).isIrreducible.isGenericPoint_genericPoint (g C).isClosed).mem
    exact hz ▸ z.2
  have hc : (q : ℕ∞) ≤ coheight η :=
    WithBot.coe_le_coe.1 (by rw [← ringKrullDim_stalk_eq_coheight]; exact hq η hηZ)
  have hsum : ((height η + coheight η : ℕ∞) : WithBot ℕ∞) ≤ d := by
    rw [← hd, topologicalKrullDim, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints,
      Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.2 (le_iSup (fun a : X => height a + coheight a) η)
  have hsum' : height η + coheight η ≤ d := WithBot.coe_le_coe.1 hsum
  have hfin : height η ≠ ⊤ := fun h => by simp [h] at hsum'
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hfin
  have hle : (m : ℕ∞) + q ≤ d := by
    rw [hm]
    exact (add_le_add le_rfl hc).trans hsum'
  have hle' : m + q ≤ d := mod_cast hle
  refine WithBot.coe_le_coe.2 ?_
  calc height C ≤ height (g C) := height_le_height_apply_of_strictMono g hg C
    _ = m := (height_orderIso irreducibleSetEquivPoints (g C)).symm.trans hm.symm
    _ ≤ (d - q : ℕ) := mod_cast (by omega : m ≤ d - q)

end AlgebraicGeometry

end
