module

public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Closed points see every affine basic open

The first half of the proof of Serre's criterion for affineness [Stacks, Tag 01XF] produces, for
each *closed* point `x` of a quasi-compact scheme `X`, a global section `r : Γ(X, ⊤)` with
`x ∈ X_r` and `X_r` affine; it then upgrades this to *every* point by the following topological
argument. The union `W` of all affine basic opens of global sections is open, and contains every
closed point; if `W` were not everything then `X \ W` would be a nonempty closed subset of a
quasi-compact space, hence would contain a point closed in `X`, contradicting the previous
sentence.

This file isolates that upgrade. It is purely topological, uses no cohomology, and is the part of
[Stacks, Tag 01XF] that does not depend on the vanishing hypothesis.

## Main results

* `Stacks.SerreAffinenessCriterion.exists_isClosed_singleton_mem`: a nonempty closed subset of a
  compact `T₀` space contains a point which is closed in the ambient space.
* `Stacks.SerreAffinenessCriterion.exists_isAffineOpen_basicOpen_mem`: on a quasi-compact scheme,
  if every closed point lies in an affine basic open of a global section then so does every point.

## Implementation notes

The closed point is extracted from Mathlib's
`IsClosed.exists_minimal_nonempty_closed_subset`: a minimal nonempty closed subset `V` of a
compact space equals `closure {y}` for each of its points `y`, so all of its points are
inseparable, so `V` is a singleton by `T0Space`. Schemes are `T0Space` by the instance in
`Mathlib/AlgebraicGeometry/Properties.lean`, and the ambient compactness needed by the Mathlib
lemma is exactly `CompactSpace X`.

## References

* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
-/

@[expose] public section

open TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SerreAffinenessCriterion

/-- **A nonempty closed subset of a compact `T₀` space contains a closed point.** The point is
closed in the ambient space, not merely in the subset. -/
theorem exists_isClosed_singleton_mem {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [T0Space X] {S : Set X} (hS : IsClosed S) (hne : S.Nonempty) :
    ∃ x ∈ S, IsClosed ({x} : Set X) := by
  obtain ⟨V, hVS, hVne, hVcl, hmin⟩ := hS.exists_minimal_nonempty_closed_subset hne
  obtain ⟨x, hx⟩ := hVne
  refine ⟨x, hVS hx, ?_⟩
  have key : ∀ y ∈ V, closure ({y} : Set X) = V := fun y hy ↦
    hmin _ (hVcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hy))
      ⟨y, subset_closure rfl⟩ isClosed_closure
  have hV : V = {x} :=
    Set.eq_singleton_iff_unique_mem.mpr
      ⟨hx, fun y hy ↦ (inseparable_iff_closure_eq.mpr ((key y hy).trans (key x hx).symm)).eq⟩
  exact hV ▸ hVcl

variable (X : Scheme.{u})

/-- The union of those basic opens of global sections of `X` which are affine. -/
def affineLocus : X.Opens :=
  ⨆ r : {r : Γ(X, ⊤) // IsAffineOpen (X.basicOpen r)}, X.basicOpen r.1

variable {X} in
/-- A point lies in `Stacks.SerreAffinenessCriterion.affineLocus X` exactly when some affine basic
open of a global section contains it. -/
theorem mem_affineLocus_iff {x : X} :
    x ∈ affineLocus X ↔
      ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r := by
  refine ⟨fun hx ↦ ?_, fun ⟨r, hr, hx⟩ ↦ Opens.mem_iSup.mpr ⟨⟨r, hr⟩, hx⟩⟩
  obtain ⟨r, hr⟩ := Opens.mem_iSup.mp hx
  exact ⟨r.1, r.2, hr⟩

/-- **The closed points of a quasi-compact scheme detect the affine basic opens.** If every closed
point of `X` lies in an affine basic open of a global section, then every point of `X` does.

This is the topological half of Serre's criterion [Stacks, Tag 01XF]: the hypothesis is what that
proof obtains from the vanishing of `H¹` on quasi-coherent ideal sheaves, and the conclusion is
what feeds `AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen`. -/
theorem exists_isAffineOpen_basicOpen_mem [CompactSpace X]
    (H : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r) (x : X) :
    ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r := by
  rw [← mem_affineLocus_iff]
  by_contra hx
  obtain ⟨y, hy, hycl⟩ :=
    exists_isClosed_singleton_mem (isClosed_compl_iff.mpr (affineLocus X).2) ⟨x, hx⟩
  exact hy (mem_affineLocus_iff.mpr (H y hycl))

end Stacks.SerreAffinenessCriterion
