module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# The complement of a dense open in a curve is a finite set of closed `k`-points

Let `X` be a separated scheme of finite type over an algebraically closed field `k`, of
dimension at most one, and let `X'` be a dense open subscheme. This file assembles the purely
topological content of that hypothesis for Tag 0GJE: the complement `Z = X \ X'` is a finite
set, every point of `Z` is a closed point of `X`, and at a closed point the residue field is
`k` itself.

The topological finiteness is `Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset`
and `Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset`, both about
Noetherian sober `T0` spaces of Krull dimension at most one, fed the fact that a closed
nowhere-dense set contains no irreducible component
(`IsClosed.isNowhereDense_iff_forall_irreducibleComponents_not_subset`). The residue field at a
closed point of a locally-of-finite-type `k`-scheme, `k` algebraically closed, is
`AlgebraicGeometry.residueFieldIsoBase`.

## Main results

* `Stacks.EtaleCohomology.TorsionModules.finite_compl_range_of_dense_isOpenImmersion` — the
  topological statement alone, for a Noetherian scheme.
* `Stacks.EtaleCohomology.TorsionModules.finite_compl_and_residueField_eq_of_dense_isOpenImmersion`
  — the full statement over an algebraically closed field: `Z` is finite, every point of `Z` is
  closed, and every point of `Z` has residue field `k`.

## Implementation notes

`X` separated of finite type over `k` is read as `LocallyOfFiniteType p` together with
`QuasiCompact p` for the structure morphism `p : X ⟶ Spec k`; separatedness is not needed here
(it is not used by either the topological finiteness argument or `residueFieldIsoBase`). From
these, `NoetherianSpace X` is assembled via `LocallyOfFiniteType.isLocallyNoetherian` and
`QuasiCompact.compactSpace_of_compactSpace`; `T0Space X` and `QuasiSober X` are unconditional
scheme instances and so do not appear as hypotheses.

## References

Assembled for use in [Stacks Project, Tag 0GJE](https://stacks.math.columbia.edu/tag/0GJE); not
itself a cited tag.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology Set AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.TorsionModules

/-- **The complement of a dense open in a Noetherian scheme of dimension at most one is a finite
set of closed points.** The complement is closed (the open immersion's range is open) and
nowhere dense (its range is dense), hence contains no irreducible component; dimension at most
one then makes every one of its points closed, and Noetherian-ness makes the set finite. -/
theorem finite_compl_range_of_dense_isOpenImmersion {X X' : Scheme.{u}} (j : X' ⟶ X)
    [IsOpenImmersion j] [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)
    (hdense : Dense (Set.range j.base)) :
    (Set.range j.base)ᶜ.Finite ∧ ∀ z ∈ (Set.range j.base)ᶜ, IsClosed ({z} : Set X) := by
  have hZ : IsClosed (Set.range j.base)ᶜ :=
    (IsOpenImmersion.isOpen_range j).isClosed_compl
  have hnd : IsNowhereDense (Set.range j.base)ᶜ := by
    rw [IsNowhereDense, hZ.closure_eq, interior_compl, hdense.closure_eq]
    simp
  have hTc := hZ.isNowhereDense_iff_forall_irreducibleComponents_not_subset.mp hnd
  exact ⟨Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hdim hZ hTc,
    fun z hz ↦ Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
      hdim hZ hTc hz⟩

/-- **The complement of a dense open in a curve over an algebraically closed field is a finite
set of closed `k`-points.** `X` separated of finite type over the algebraically closed field
`k`, of dimension at most one, and `X'` a dense open subscheme: the complement `Z = X \ X'` is
finite, each of its points is closed in `X`, and each has residue field `k`. This is the
geometric content of Tag 0GJE: it is what makes the closed complement a disjoint union of
spectra of `k`, whose cohomology is computed by
`Stacks.EtaleCohomology.TorsionModules.finite_moduleEtaleCohomology_zero_pointsDirectImage` and
`Stacks.EtaleCohomology.TorsionModules.isZero_moduleEtaleCohomology_succ_pointsDirectImage`. -/
theorem finite_compl_and_residueField_eq_of_dense_isOpenImmersion
    {k : Type u} [Field k] [IsAlgClosed k] {X X' : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim X ≤ 1)
    (j : X' ⟶ X) [IsOpenImmersion j] (hdense : Dense (Set.range j.base)) :
    (Set.range j.base)ᶜ.Finite ∧ (∀ z ∈ (Set.range j.base)ᶜ, IsClosed ({z} : Set X)) ∧
      ∀ z ∈ (Set.range j.base)ᶜ, Nonempty (X.residueField z ≅ CommRingCat.of k) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have : NoetherianSpace X := inferInstance
  obtain ⟨hfin, hcl⟩ := finite_compl_range_of_dense_isOpenImmersion j hdim hdense
  exact ⟨hfin, hcl, fun z hz ↦ ⟨residueFieldIsoBase p z (hcl z hz)⟩⟩

end Stacks.EtaleCohomology.TorsionModules

end
