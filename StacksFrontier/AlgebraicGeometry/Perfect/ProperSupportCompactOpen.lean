module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubsetCompact

/-!
# A quasi-compact open neighbourhood of a closed subset proper over the base

Let `S` be a quasi-compact scheme and `f : X ⟶ S` a morphism locally of finite type.  A closed
subset `Z ⊆ X` proper over `S` is quasi-compact
(`AlgebraicGeometry.isCompact_of_isProperOver`), so it is covered by finitely many affine opens
of `X`, whose union is a quasi-compact open `U ⊇ Z`.  When `X` is locally Noetherian, `U` is a
Noetherian scheme, so the inclusion `U ⟶ X` and the composite `U ⟶ X ⟶ S` are quasi-compact and
quasi-separated even though `f` itself need not be quasi-compact.

This is what lets a statement about `f` that is known only for quasi-compact quasi-separated
morphisms — [Stacks, Tag 08EU] — be applied to objects whose cohomology is supported on `Z`.

## Main results

* `AlgebraicGeometry.exists_isCompact_opens_superset_of_isProperOver`: the quasi-compact open
  `U ⊇ Z`.
* `AlgebraicGeometry.isNoetherian_of_isCompact_opens`: an open of a locally Noetherian scheme
  with quasi-compact underlying set is a Noetherian scheme.
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A closed subset proper over a quasi-compact base has a quasi-compact open
neighbourhood.**  The subset is quasi-compact, and finitely many of the affine opens of `X`
cover it. -/
theorem exists_isCompact_opens_superset_of_isProperOver {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [CompactSpace S] (Z : Closeds X) (hZ : IsProperOver f Z) :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ (Z : Set X) ⊆ U := by
  have hc := isCompact_of_isProperOver f Z hZ
  choose V hV hxV _ using fun x : X =>
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) trivial
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x : X => (V x : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  refine ⟨⨆ x ∈ t, V x, ?_, ?_⟩
  · simp only [Opens.coe_iSup]
    exact t.isCompact_biUnion fun x _ => (hV x).isCompact
  · simpa only [Opens.coe_iSup] using ht

/-- **An open of a locally Noetherian scheme with quasi-compact underlying set is a Noetherian
scheme.** -/
theorem isNoetherian_of_isCompact_opens {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) : IsNoetherian U.toScheme := by
  have : CompactSpace U := isCompact_iff_compactSpace.1 hU
  exact ⟨⟩

end AlgebraicGeometry
