module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Filling up a quasi-compact scheme by affine opens

In a quasi-compact scheme `S`, the complement of an open `U` is closed, hence quasi-compact, hence
covered by finitely many affine opens.

## Main results

* `AlgebraicGeometry.Scheme.exists_finite_affineOpens_sup_eq_top`: finitely many affine opens
  can be added to a given open of a quasi-compact scheme to cover the whole scheme.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- In a quasi-compact scheme, finitely many affine opens can be added to any open subscheme
so as to cover the whole scheme. -/
lemma exists_finite_affineOpens_sup_eq_top (S : Scheme.{u}) [CompactSpace S] (U : S.Opens) :
    ∃ (n : ℕ) (A : Fin n → S.affineOpens), U ⊔ ⨆ l, (A l : S.Opens) = ⊤ := by
  classical
  have hcover : (U : Set S)ᶜ ⊆ ⋃ V : S.affineOpens, (V : Set S) := by
    intro x _
    have hx : x ∈ (⨆ V : S.affineOpens, (V : S.Opens)) := by
      rw [iSup_affineOpens_eq_top]
      trivial
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨V, hV⟩
  obtain ⟨t, ht⟩ := U.2.isClosed_compl.isCompact.elim_finite_subcover
    (fun V : S.affineOpens ↦ (V : Set S)) (fun V ↦ V.1.2) hcover
  refine ⟨t.card, fun l ↦ (t.equivFin.symm l).1, top_unique fun x _ ↦ ?_⟩
  by_cases hx : x ∈ U
  · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl hx)
  · obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp (ht hx)
    refine TopologicalSpace.Opens.mem_sup.mpr
      (Or.inr (TopologicalSpace.Opens.mem_iSup.mpr ⟨t.equivFin ⟨V, hV⟩, ?_⟩))
    simpa using hxV

end AlgebraicGeometry.Scheme
