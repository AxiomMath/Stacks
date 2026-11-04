/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# An immersion from a quasi-compact scheme is closed in a quasi-compact open

Let `i : X ⟶ P` be an immersion of schemes with `X` quasi-compact.  Then there is a quasi-compact
open `V ⊆ P` containing the image of `i` such that `i` factors as a closed immersion `X ⟶ V`
followed by the inclusion of `V`: the image of `i` is closed in its coborder, which is open, and
being quasi-compact it is covered by finitely many affine opens inside the coborder.

## Main results

* `AlgebraicGeometry.exists_isCompact_opens_isClosedImmersion_of_isImmersion`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An immersion `i : X ⟶ P` with `X` quasi-compact factors as a closed immersion `c : X ⟶ V`
followed by the inclusion `V.ι` of a quasi-compact open `V` of `P`. -/
theorem exists_isCompact_opens_isClosedImmersion_of_isImmersion {X P : Scheme.{u}} (i : X ⟶ P)
    [IsImmersion i] [CompactSpace X] :
    ∃ (V : P.Opens) (c : X ⟶ V.toScheme), IsCompact (V : Set P) ∧ IsClosedImmersion c ∧
      c ≫ V.ι = i := by
  have hrc : IsCompact (Set.range i.base) := isCompact_range i.base.hom.continuous
  have hcob : ∀ y ∈ Set.range i.base, ∃ W : P.Opens, IsAffineOpen W ∧ y ∈ W ∧
      (W : Set P) ⊆ i.coborderRange := fun _ hy =>
    exists_isAffineOpen_mem_and_subset (U := i.coborderRange) (subset_coborder hy)
  choose W hW hyW hWs using hcob
  obtain ⟨t, ht⟩ := hrc.elim_finite_subcover (fun y : Set.range i.base => (W y.1 y.2 : Set P))
    (fun y => (W y.1 y.2).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyW y hy⟩)
  let V : P.Opens := ⨆ y ∈ t, W y.1 y.2
  have hV : (V : Set P) = ⋃ y ∈ t, (W y.1 y.2 : Set P) := by
    simp only [V, TopologicalSpace.Opens.coe_iSup]
  have hVcob : (V : Set P) ⊆ i.coborderRange :=
    hV ▸ Set.iUnion₂_subset fun y _ => hWs y.1 y.2
  have hrV : Set.range i.base ⊆ V := hV ▸ ht
  have hVc : IsCompact (V : Set P) := hV ▸ t.isCompact_biUnion fun y _ => (hW y.1 y.2).isCompact
  let c : X ⟶ V.toScheme := IsOpenImmersion.lift V.ι i (by simpa using hrV)
  have hc : c ≫ V.ι = i := IsOpenImmersion.lift_fac _ _ _
  have : IsPreimmersion (c ≫ V.ι) := by rw [hc]; infer_instance
  have : IsPreimmersion c := .of_comp c V.ι
  refine ⟨V, c, hVc, .of_isPreimmersion c ?_, hc⟩
  have hrange : Set.range c.base = V.ι.base ⁻¹' closure (Set.range i.base) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine subset_closure ?_
      simp only [← Scheme.Hom.comp_apply, hc, Set.mem_range_self]
    · intro hz
      have hz' : V.ι.base z ∈ Set.range i.base := by
        have := hVcob (by simpa using Set.mem_range_self (f := V.ι.base) z)
        exact (mem_coborder_iff_imp.1 this) hz
      obtain ⟨x, hx⟩ := hz'
      refine ⟨x, V.ι.isOpenEmbedding.injective ?_⟩
      rw [← hx, ← Scheme.Hom.comp_apply, hc]
  rw [hrange]
  exact isClosed_closure.preimage V.ι.base.hom.continuous

end AlgebraicGeometry

end
