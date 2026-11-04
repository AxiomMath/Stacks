module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Compact subsets of a scheme sit inside quasi-compact opens

A compact subset of a scheme is contained in a quasi-compact open subset:
`AlgebraicGeometry.exists_opens_superset_isCompact`.
-/


universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A compact subset of a scheme is contained in a quasi-compact open subset. -/
public theorem exists_opens_superset_isCompact {X : Scheme.{u}} {K : Set X} (hK : IsCompact K) :
    ∃ W : X.Opens, K ⊆ (W : Set X) ∧ IsCompact (W : Set X) := by
  classical
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun A : X.affineOpens => ((A : X.Opens) : Set X))
    (fun A => (A : X.Opens).isOpen) fun x _ => by
      obtain ⟨A, hA⟩ := Opens.mem_iSup.mp
        (show x ∈ (⨆ A : X.affineOpens, (A : X.Opens)) by
          rw [iSup_affineOpens_eq_top X]; trivial)
      exact Set.mem_iUnion.mpr ⟨A, hA⟩
  refine ⟨⨆ A ∈ t, (A : X.Opens), ?_, ?_⟩
  · simpa only [Opens.coe_iSup] using ht
  · simp only [Opens.coe_iSup]
    exact t.finite_toSet.isCompact_biUnion fun A _ => A.2.isCompact

end AlgebraicGeometry
