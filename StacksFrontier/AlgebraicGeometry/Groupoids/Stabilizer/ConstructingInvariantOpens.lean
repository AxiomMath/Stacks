module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.OpenSaturation

/-!
# Constructing invariant opens in a groupoid scheme

For a groupoid scheme `(U, R, s, t, c)` the saturation `t(s⁻¹(W))` of a subset `W ⊆ U` is the
set of points of `U` equivalent to a point of `W` for the equivalence relation that the source
and target maps induce on points. It is therefore invariant. When `t` is an open map the
saturation of an open is open, and when in addition `s` is quasi-compact the saturation of a
quasi-compact open is quasi-compact; saturating the affine opens then covers `U` by invariant
quasi-compact opens.

## Main results

* `AlgebraicGeometry.GroupoidScheme.equivalence_sourceTargetRel`: the relation induced on the
  points of the object scheme by the source and target maps is an equivalence relation.
* `AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_eq_target_image_source_preimage` is
  part (2): for an open map `t` and an open `W`, the saturation of `W` is an invariant open
  subscheme.
* `AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isCompact_mem` and
  `AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isCompact_cover` are part (3): every
  point of the object scheme lies in an invariant quasi-compact open, so these cover it.

## Implementation notes

Part (1), that the saturation of an arbitrary subset is set-theoretically invariant, is
`AlgebraicGeometry.GroupoidScheme.isInvariantSet_target_image_source_preimage` of
`StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic`, and is used here as it
stands.

Invariance of a subset is `Stacks.Groupoids.IsInvariantSet`, the repository's form of Stacks
03BC part (1): every arrow whose source lies in the subset has its target there too. Because
the groupoid has inverses this single implication is equivalent to the equality
`s⁻¹(E) = t⁻¹(E)` of the source's phrasing, and
`AlgebraicGeometry.GroupoidScheme.source_preimage_eq_target_preimage` records that equality.

The source states parts (2) and (3) under the hypothesis that both `s` and `t` are open. Only
`t` being open is used — `s` enters part (3) only through its quasi-compactness — so the
hypothesis on `s` is dropped, which generalizes rather than weakens the statement. Likewise
part (3) uses only that `s` is quasi-compact, not that `t` is.

Openness of a map of schemes is taken as `IsOpenMap` on the underlying map of points, which is
the source's definition of an open morphism; no universal openness is assumed.

The covering in part (3) is indexed by the points of the object scheme, each point being sent
to the saturation of an affine open neighbourhood of it. The saturation of an affine open is in
general strictly larger than the affine open, so this is not a refinement of the affine cover.

## References

* [Stacks Project, Tag 03LO](https://stacks.math.columbia.edu/tag/03LO)
* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)

/-- The relation induced on the points of the object scheme of a groupoid scheme by its target
and source maps is an equivalence relation: two points are related when some arrow has the
first as its target and the second as its source. -/
theorem equivalence_sourceTargetRel :
    Equivalence (Function.SourceTargetRel G.source.left.base G.target.left.base) := by
  simpa [groupoidPreRelation, Stacks.Groupoids.PreRelation.target,
    Stacks.Groupoids.PreRelation.source] using
    _root_.AlgebraicGeometry.PreRelation.equivalence_sourceTargetRel (groupoidPreRelation G)
      (groupoidPreRelation_isPreEquivalenceRelation G)

/-- An arrow is related to its own source and target. -/
theorem sourceTargetRel_target_source (r : G.arrows.left) :
    Function.SourceTargetRel G.source.left.base G.target.left.base
      (G.target.left.base r) (G.source.left.base r) :=
  ⟨r, rfl, rfl⟩

/-- Applying the points map of a composite of scheme morphisms that equals `h` is applying `h`. -/
private theorem base_comp_apply_eq_of_comp_eq {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : X ⟶ Z} (e : f ≫ g = h) (x : X) : g.base (f.base x) = h.base x := by
  rw [← e]
  rfl

/-- An invariant subset has equal source and target preimages in the arrow scheme: the
implication defining invariance may be reversed by passing to the inverse arrow. -/
theorem source_preimage_eq_target_preimage {E : Set G.objects.left}
    (hE : IsInvariantSet G E) :
    G.source.left.base ⁻¹' E = G.target.left.base ⁻¹' E := by
  have hinvTarget : ∀ r : G.arrows.left,
      G.target.left.base (G.inverse.left.base r) = G.source.left.base r := fun r =>
    base_comp_apply_eq_of_comp_eq (congrArg (·.left) G.target_inverse) r
  have hinvSource : ∀ r : G.arrows.left,
      G.source.left.base (G.inverse.left.base r) = G.target.left.base r := fun r =>
    base_comp_apply_eq_of_comp_eq (congrArg (·.left) G.source_inverse) r
  refine Set.Subset.antisymm (fun r hr => hE r hr) (fun r hr => ?_)
  have h := hE (G.inverse.left.base r) (show G.source.left.base (G.inverse.left.base r) ∈ E by
    rw [hinvSource r]; exact hr)
  show G.source.left.base r ∈ E
  rw [← hinvTarget r]
  exact h

/-- The complement of an invariant subset is invariant. -/
theorem isInvariantSet_compl {E : Set G.objects.left} (hE : IsInvariantSet G E) :
    IsInvariantSet G Eᶜ := by
  intro r hr hcontra
  exact hr (by
    have := (source_preimage_eq_target_preimage G hE).symm
    exact (Set.ext_iff.mp this r).mp hcontra)

/-- A point of the object scheme lies in the saturation of any subset containing it: the
identity arrow at that point has it as both source and target. -/
theorem subset_target_image_source_preimage (W : Set G.objects.left) :
    W ⊆ G.target.left.base '' (G.source.left.base ⁻¹' W) := by
  intro x hx
  refine ⟨G.identity.left.base x, ?_, ?_⟩
  · show G.source.left.base (G.identity.left.base x) ∈ W
    rw [base_comp_apply_eq_of_comp_eq (identity_left_comp_source_left G)]
    exact hx
  · exact base_comp_apply_eq_of_comp_eq (identity_left_comp_target_left G) x

/-- The saturation of an open subset along an open target map is open.

This is `AlgebraicGeometry.GroupoidScheme.isOpen_target_image_source_preimage` with the open
subset presented as a set together with a proof that it is open, which is the shape the
constructions below apply it in. -/
theorem isOpen_target_image_source_preimage_of_isOpen (ht : IsOpenMap G.target.left.base)
    {W : Set G.objects.left} (hW : IsOpen W) :
    IsOpen (G.target.left.base '' (G.source.left.base ⁻¹' W)) :=
  ht _ (hW.preimage G.source.left.continuous)

/-- **Stacks Project, Tag 03LO, part (2).** If the target map of a groupoid scheme is open then
the saturation `t(s⁻¹(W))` of an open subscheme `W` of the object scheme is an invariant open
subscheme. -/
@[stacks 03LO "(2) t(s⁻¹(W)) is an invariant open subscheme"]
theorem exists_isInvariantOpen_eq_target_image_source_preimage
    (ht : IsOpenMap G.target.left.base) (W : G.objects.left.Opens) :
    ∃ V : G.objects.left.Opens,
      (V : Set G.objects.left) =
        G.target.left.base '' (G.source.left.base ⁻¹' (W : Set G.objects.left)) ∧
      (W : Set G.objects.left) ⊆ (V : Set G.objects.left) ∧ IsInvariantOpen G V :=
  ⟨⟨_, isOpen_target_image_source_preimage_of_isOpen G ht W.2⟩, rfl,
    subset_target_image_source_preimage G _,
    isInvariantSet_target_image_source_preimage G _⟩

/-- Every point of the object scheme of a groupoid scheme with open target map and quasi-compact
source map lies in an invariant quasi-compact open subscheme, namely the saturation of an affine
open neighbourhood of it. -/
theorem exists_isInvariantOpen_isCompact_mem [QuasiCompact G.source.left]
    (ht : IsOpenMap G.target.left.base) (u : G.objects.left) :
    ∃ V : G.objects.left.Opens,
      IsInvariantOpen G V ∧ IsCompact (V : Set G.objects.left) ∧ u ∈ V := by
  obtain ⟨W, hWaff, huW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := G.objects.left) (x := u) (U := ⊤) trivial
  refine ⟨⟨_, isOpen_target_image_source_preimage_of_isOpen G ht W.2⟩,
    isInvariantSet_target_image_source_preimage G _, ?_, ?_⟩
  · exact (QuasiCompact.isCompact_preimage _ W.2 hWaff.isCompact).image
      G.target.left.continuous
  · exact subset_target_image_source_preimage G (W : Set G.objects.left) huW

/-- **Stacks Project, Tag 03LO, part (3).** If the target map of a groupoid scheme is open and
its source map is quasi-compact, then the object scheme has an open covering consisting of
invariant quasi-compact open subschemes. -/
@[stacks 03LO "(3) covering by invariant quasi-compact opens"]
theorem exists_isInvariantOpen_isCompact_cover [QuasiCompact G.source.left]
    (ht : IsOpenMap G.target.left.base) :
    ∃ (ι : Type u) (V : ι → G.objects.left.Opens),
      (∀ i, IsInvariantOpen G (V i)) ∧
      (∀ i, IsCompact (V i : Set G.objects.left)) ∧
      ⨆ i, V i = ⊤ := by
  classical
  choose V hVinv hVcpt hVmem using exists_isInvariantOpen_isCompact_mem G ht
  refine ⟨G.objects.left, V, hVinv, hVcpt, le_antisymm le_top fun u _ => ?_⟩
  exact Opens.mem_iSup.mpr ⟨u, hVmem u⟩

end AlgebraicGeometry.GroupoidScheme

end
