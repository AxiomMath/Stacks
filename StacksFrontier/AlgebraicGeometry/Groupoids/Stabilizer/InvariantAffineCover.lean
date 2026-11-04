module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantAffineOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Covering the objects of a finite flat groupoid by invariant affine opens

Let `(U, R, s, t, c)` be a groupoid scheme whose source and target maps are finite locally
free. Assume that every nonempty closed subset of `U` contains a point whose `R`-equivalence
class `t(s⁻¹({u}))` lies in an affine open of `U`. Then *every* point of `U` has an
`R`-invariant affine open neighbourhood, and in particular `U` is covered by `R`-invariant
affine opens.

This is the first step of the proof of Tag 07S6: it turns the pointwise statement of Tag 03JE
into a covering, which is what the glueing argument of Tag 07S6 consumes.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.GroupoidScheme.forall_exists_isInvariantOpen_isAffineOpen_mem`: under the
  hypothesis as Tag 07S6 states it, every point has an invariant affine open neighbourhood.
* `AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isAffineOpen_cover` is the resulting
  covering, indexed by the points of the object scheme.
* `AlgebraicGeometry.GroupoidScheme.exists_isAffineOpen_saturation_subset_of_forall_finite`
  verifies the hypothesis of Tag 07S6 pointwise when every finite subset of `U` lies in an
  affine open, which is the form in which Tag 03JI supplies it (through Tag 01ZY).
* `AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isAffineOpen_cover_of_forall_finite`
  is the covering under that stronger, more usable hypothesis.

## Implementation notes

The only content is that the union `W` of all invariant affine opens is everything. Were `W` a
proper open, its complement would be a nonempty closed subset, so by hypothesis it would
contain a point whose class lies in an affine open, and Tag 03JE would produce an invariant
affine open neighbourhood of that point — which is contained in `W`, contradicting that the
point lies outside `W`. The supremum is taken over the *set* of invariant affine opens, so no
choice is made there and the index type is in the universe of the schemes involved.

So the source's condition (3) in fact forces the set `E` of its footnote to be all of `U`. The
covering is then indexed by the points of `U`, as in
`AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isCompact_cover`; that index type is
the one the glueing step of Tag 07S6 needs, since the big site carries a size cutoff and the
set of all invariant affine opens carries no bound below it.

`AlgebraicGeometry.GroupoidScheme.exists_isAffineOpen_saturation_subset_of_forall_finite` uses
only that the fibres of `s` are finite, which holds because a finite locally free morphism is
finite: the equivalence class `t(s⁻¹({u}))` is then the image of a finite set.

The hypothesis of the first result is the source's condition (3) of Tag 07S6 verbatim,
including that the affine open is not required to be invariant and is allowed to depend on the
point.

## References

* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The invariant affine opens of the object scheme of a groupoid scheme. -/
private abbrev InvariantAffineOpens : Type u :=
  {V : G.objects.left.Opens // IsInvariantOpen G V ∧ IsAffineOpen V}

/-- **The covering step of Stacks Project, Tag 07S6.** Let `(U, R, s, t, c)` be a groupoid
scheme with `s` and `t` finite locally free. If every nonempty closed subset of `U` contains a
point whose equivalence class `t(s⁻¹({u}))` is contained in an affine open of `U`, then every
point of `U` has an `R`-invariant affine open neighbourhood. -/
@[sga "1 V 1.8" "partial"]
theorem forall_exists_isInvariantOpen_isAffineOpen_mem
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    (h : ∀ Z : Set G.objects.left, IsClosed Z → Z.Nonempty →
      ∃ u ∈ Z, ∃ W : G.objects.left.Opens, IsAffineOpen W ∧
        G.target.left.base '' (G.source.left.base ⁻¹' {u}) ⊆ (W : Set G.objects.left))
    (u : G.objects.left) :
    ∃ V : G.objects.left.Opens, IsInvariantOpen G V ∧ IsAffineOpen V ∧ u ∈ V := by
  have htop : (⨆ i : InvariantAffineOpens G, (i : G.objects.left.Opens)) = ⊤ := by
    by_contra hne
    have hZ : (((⨆ i : InvariantAffineOpens G, (i : G.objects.left.Opens)) :
        G.objects.left.Opens) : Set G.objects.left)ᶜ.Nonempty := by
      refine Set.nonempty_compl.mpr fun hcoe => hne ?_
      exact Opens.ext (by rw [hcoe, Opens.coe_top])
    obtain ⟨v, hv, W, hWaff, hWsub⟩ :=
      h _ (isClosed_compl_iff.mpr (⨆ i : InvariantAffineOpens G,
        (i : G.objects.left.Opens)).2) hZ
    obtain ⟨V, hVinv, hVaff, hVv⟩ :=
      exists_isInvariantOpen_isAffineOpen_mem G v ⟨W, hWaff, hWsub⟩
    exact hv (Opens.mem_iSup.mpr ⟨⟨V, hVinv, hVaff⟩, hVv⟩)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (htop ▸ (show u ∈ (⊤ : G.objects.left.Opens) from trivial))
  exact ⟨i.1, i.2.1, i.2.2, hi⟩

/-- **The covering of Stacks Project, Tag 07S6.** Under the hypothesis of
`AlgebraicGeometry.GroupoidScheme.forall_exists_isInvariantOpen_isAffineOpen_mem` the object
scheme of the groupoid has an open covering by `R`-invariant affine opens, indexed by its
points. -/
@[sga "1 V 1.8" "partial"]
theorem exists_isInvariantOpen_isAffineOpen_cover
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    (h : ∀ Z : Set G.objects.left, IsClosed Z → Z.Nonempty →
      ∃ u ∈ Z, ∃ W : G.objects.left.Opens, IsAffineOpen W ∧
        G.target.left.base '' (G.source.left.base ⁻¹' {u}) ⊆ (W : Set G.objects.left)) :
    ∃ (ι : Type u) (V : ι → G.objects.left.Opens),
      (∀ i, IsInvariantOpen G (V i)) ∧
      (∀ i, IsAffineOpen (V i)) ∧
      ⨆ i, V i = ⊤ := by
  classical
  choose V hVinv hVaff hVmem using forall_exists_isInvariantOpen_isAffineOpen_mem G h
  refine ⟨G.objects.left, V, hVinv, hVaff, le_antisymm le_top fun u _ => ?_⟩
  exact Opens.mem_iSup.mpr ⟨u, hVmem u⟩

/-- If every finite subset of the object scheme of a groupoid scheme with finite locally free
source lies in an affine open, then the equivalence class of every point lies in an affine
open: the class is the image of a fibre of `s`, which is finite. -/
theorem exists_isAffineOpen_saturation_subset_of_forall_finite
    [IsFiniteLocallyFree G.source.left]
    (hfin : ∀ E : Set G.objects.left, E.Finite →
      ∃ W : G.objects.left.Opens, IsAffineOpen W ∧ E ⊆ (W : Set G.objects.left))
    (u : G.objects.left) :
    ∃ W : G.objects.left.Opens, IsAffineOpen W ∧
      G.target.left.base '' (G.source.left.base ⁻¹' {u}) ⊆ (W : Set G.objects.left) := by
  obtain ⟨hsfin, -, -⟩ := (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    G.source.left).mp inferInstance
  have hs : IsFinite G.source.left := hsfin
  exact hfin _ ((G.source.left.finite_preimage_singleton u).image _)

/-- **The covering of Stacks Project, Tag 07S6, under the hypothesis of Tag 03JI.** Let
`(U, R, s, t, c)` be a groupoid scheme with `s` and `t` finite locally free. If every finite
subset of `U` is contained in an affine open of `U`, then `U` has an open covering by
`R`-invariant affine opens, indexed by its points. -/
@[sga "1 V 1.8" "special case"]
theorem exists_isInvariantOpen_isAffineOpen_cover_of_forall_finite
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    (hfin : ∀ E : Set G.objects.left, E.Finite →
      ∃ W : G.objects.left.Opens, IsAffineOpen W ∧ E ⊆ (W : Set G.objects.left)) :
    ∃ (ι : Type u) (V : ι → G.objects.left.Opens),
      (∀ i, IsInvariantOpen G (V i)) ∧
      (∀ i, IsAffineOpen (V i)) ∧
      ⨆ i, V i = ⊤ :=
  exists_isInvariantOpen_isAffineOpen_cover G fun _ _ hZne => by
    obtain ⟨u, hu⟩ := hZne
    exact ⟨u, hu, exists_isAffineOpen_saturation_subset_of_forall_finite G hfin u⟩

end AlgebraicGeometry.GroupoidScheme

end
