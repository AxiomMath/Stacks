module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Quasi-separatedness from a cover by two quasi-separated opens

A scheme covered by two quasi-separated open subschemes whose intersection is quasi-compact is
itself quasi-separated.  This is the topological ingredient of the glueing step of the
limit-descent argument, where a scheme is split as the union of two opens, one of them the union
of all but one member of a finite affine open cover.

## Main results

* `AlgebraicGeometry.quasiSeparatedSpace_of_sup`: a scheme covered by two quasi-separated opens
  whose intersection is quasi-compact is quasi-separated.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A scheme covered by two opens, each quasi-separated, whose intersection is quasi-compact,
is quasi-separated. -/
public lemma quasiSeparatedSpace_of_sup {Y : Scheme.{u}} {A B : Y.Opens} (hAB : A ⊔ B = ⊤)
    (hA : IsQuasiSeparated (A : Set Y)) (hB : IsQuasiSeparated (B : Set Y))
    (hAB' : IsCompact ((A ⊓ B : Y.Opens) : Set Y)) :
    QuasiSeparatedSpace Y := by
  rw [Opens.coe_inf] at hAB'
  have hABo : IsOpen ((A : Set Y) ∩ (B : Set Y)) := A.isOpen.inter B.isOpen
  have hcover : ∀ x : Y, x ∈ (A : Set Y) ∨ x ∈ (B : Set Y) := fun x => by
    simpa using (show x ∈ A ⊔ B by rw [hAB]; trivial)
  -- A compact open contained in `A` and a compact open contained in `B` meet in a compact set:
  -- cut the second one down to `A ⊓ B`, which is quasi-separated inside `B`, and then intersect
  -- inside `A`.
  have key : ∀ s t : Set Y, s ⊆ (A : Set Y) → t ⊆ (B : Set Y) → IsOpen s → IsCompact s →
      IsOpen t → IsCompact t → IsCompact (s ∩ t) := by
    intro s t hsA htB hso hsc hto htc
    have h1 : IsCompact (t ∩ ((A : Set Y) ∩ (B : Set Y))) :=
      hB _ _ htB hto htc Set.inter_subset_right hABo hAB'
    have h2 : IsCompact (s ∩ (t ∩ ((A : Set Y) ∩ (B : Set Y)))) :=
      hA _ _ hsA hso hsc (fun _ hx => hx.2.1) (hto.inter hABo) h1
    have he : s ∩ t = s ∩ (t ∩ ((A : Set Y) ∩ (B : Set Y))) :=
      Set.ext fun _ => ⟨fun h => ⟨h.1, h.2, hsA h.1, htB h.2⟩, fun h => ⟨h.1, h.2.1⟩⟩
    rw [he]
    exact h2
  refine QuasiSeparatedSpace.of_isTopologicalBasis
    (b := fun U : {U : Y.Opens // IsAffineOpen U ∧ (U ≤ A ∨ U ≤ B)} => (U.1 : Set Y)) ?_ ?_
  · refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro u ⟨U, rfl⟩
      exact U.1.isOpen
    · intro x u hxu hu
      have aux : ∀ C : Y.Opens, (C ≤ A ∨ C ≤ B) → x ∈ C → 
          ∃ V : {U : Y.Opens // IsAffineOpen U ∧ (U ≤ A ∨ U ≤ B)},
            x ∈ (V.1 : Set Y) ∧ (V.1 : Set Y) ⊆ u := by
        intro C hC hx
        obtain ⟨V, hV, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
          (U := ⟨u, hu⟩ ⊓ C) (x := x) (show x ∈ (⟨u, hu⟩ ⊓ C : Y.Opens) from ⟨hxu, hx⟩)
        have hVC := hVle.trans inf_le_right
        exact ⟨⟨V, hV, hC.imp hVC.trans hVC.trans⟩, hxV,
          SetLike.coe_subset_coe.2 (hVle.trans inf_le_left)⟩
      obtain ⟨V, hxV, hVu⟩ := (hcover x).elim (aux A (Or.inl le_rfl)) (aux B (Or.inr le_rfl))
      exact ⟨_, ⟨V, rfl⟩, hxV, hVu⟩
  · intro U V
    obtain ⟨hUaff, hU⟩ := U.2
    obtain ⟨hVaff, hV⟩ := V.2
    have hUo : IsOpen (U.1 : Set Y) := U.1.isOpen
    have hVo : IsOpen (V.1 : Set Y) := V.1.isOpen
    have hUc : IsCompact (U.1 : Set Y) := hUaff.isCompact
    have hVc : IsCompact (V.1 : Set Y) := hVaff.isCompact
    replace hU := hU.imp SetLike.coe_subset_coe.2 SetLike.coe_subset_coe.2
    replace hV := hV.imp SetLike.coe_subset_coe.2 SetLike.coe_subset_coe.2
    rcases hU with hU | hU <;> rcases hV with hV | hV
    · exact hA _ _ hU hUo hUc hV hVo hVc
    · exact key _ _ hU hV hUo hUc hVo hVc
    · rw [Set.inter_comm]
      exact key _ _ hV hU hVo hVc hUo hUc
    · exact hB _ _ hU hUo hUc hV hVo hVc

end AlgebraicGeometry
