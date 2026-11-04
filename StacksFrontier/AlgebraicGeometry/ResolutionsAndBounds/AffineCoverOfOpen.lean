module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Covering a quasi-compact scheme by an open together with finitely many affine opens

On a quasi-compact scheme every open `U` is part of a cover of the whole scheme by `U` together
with finitely many affine opens, and all the partial unions so formed are quasi-compact as soon
as `U` is. These are the inputs to the induction in the proof of [Stacks, Tag 01PF]: the source
picks a minimal number of affine opens `U_1, …, U_n` with `X = U ∪ ⋃ U_i` and extends the given
submodule one affine open at a time. Phrased with a `Finset` of affine opens the induction is
`Finset.induction_on` rather than an induction on a natural number, and no minimality is needed.

An open immersion with quasi-compact source into a quasi-separated scheme is quasi-compact, which
is what makes the extension result [Stacks, Tag 01PE] applicable at each stage of the induction.

## Main results

* `AlgebraicGeometry.exists_finset_affineOpens_sup_eq_top`: a quasi-compact scheme is covered by
  any open together with finitely many affine opens.
* `AlgebraicGeometry.isCompact_sup_biSup_affineOpens`: such a partial union is quasi-compact.
* `AlgebraicGeometry.quasiCompact_opens_ι`: the inclusion of a quasi-compact open of a
  quasi-separated scheme is a quasi-compact morphism.

## Implementation notes

The cover is extracted from `AlgebraicGeometry.iSup_affineOpens_eq_top` by
`IsCompact.elim_finite_subcover` on the whole space, so the resulting `Finset` is a `Finset` of
`X.affineOpens` rather than of `X.Opens`; each member therefore carries its affineness, and in
particular its quasi-compactness, with it.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The underlying set of an open together with finitely many affine opens is the union. -/
private theorem coe_sup_biSup_affineOpens (U : X.Opens) (s : Finset X.affineOpens) :
    (U ⊔ ⨆ V ∈ s, (V : X.Opens) : X.Opens).1
      = U.1 ∪ ⋃ V ∈ s, ((V : X.Opens) : Set X) := by
  simp

/-- On a quasi-compact scheme, any open together with finitely many affine opens covers the whole
scheme. -/
theorem exists_finset_affineOpens_sup_eq_top [CompactSpace X] (U : X.Opens) :
    ∃ s : Finset X.affineOpens, U ⊔ (⨆ V ∈ s, (V : X.Opens)) = ⊤ := by
  classical
  have hcover : (⨆ V : X.affineOpens, (V : X.Opens)) = ⊤ := iSup_affineOpens_eq_top X
  have hsub : (Set.univ : Set X) ⊆ ⋃ V : X.affineOpens, ((V : X.Opens) : Set X) := by
    intro x _
    have hx : x ∈ (⨆ V : X.affineOpens, (V : X.Opens)) := by rw [hcover]; trivial
    simpa using hx
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens => ((V : X.Opens) : Set X)) (fun V => (V : X.Opens).2) hsub
  refine ⟨s, Opens.ext ?_⟩
  exact (coe_sup_biSup_affineOpens U s).trans
    (Set.univ_subset_iff.mp (hs.trans Set.subset_union_right))

/-- A quasi-compact open together with finitely many affine opens is quasi-compact. -/
theorem isCompact_sup_biSup_affineOpens {U : X.Opens} (hU : IsCompact U.1)
    (s : Finset X.affineOpens) :
    IsCompact ((U ⊔ ⨆ V ∈ s, (V : X.Opens)) : X.Opens).1 := by
  classical
  rw [coe_sup_biSup_affineOpens]
  exact hU.union (s.isCompact_biUnion fun V _ => V.2.isCompact)

/-- The inclusion of a quasi-compact open of a quasi-separated scheme is a quasi-compact
morphism. -/
theorem quasiCompact_opens_ι [QuasiSeparatedSpace X] {U : X.Opens} (hU : IsCompact U.1) :
    QuasiCompact U.ι :=
  quasiCompact_iff_isSpectralMap.mpr
    (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp (hU.isRetrocompact U.2))

end AlgebraicGeometry
