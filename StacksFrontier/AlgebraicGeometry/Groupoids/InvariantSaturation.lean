module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation

/-!
# Invariant subsets and the saturation of a subset of the objects of a groupoid scheme

A subset of the object scheme of a groupoid scheme is invariant when every arrow whose source
lies in it has its target in it as well; an open subscheme is invariant when its underlying set
is. The saturation of an arbitrary subset `W`, namely the image under the target map of the
inverse image under the source map, is always invariant. When the target map is open the
saturation of an open set is open, and when the source map is in addition quasi-compact these
saturated opens give a quasi-compact invariant open neighbourhood of every point.

Invariance itself — `Stacks.Groupoids.IsInvariantSet` for a subset of the objects and
`Stacks.Groupoids.IsInvariantOpen` for an open subscheme of them — is taken from
`StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic`.

## Main results

* `Stacks.Groupoids.isInvariantSet_target_image_source_preimage`: the saturation of any subset
  is invariant.
* `Stacks.Groupoids.isOpen_target_image_source_preimage`: the saturation of an open set is open
  when the target map is open.
* `Stacks.Groupoids.exists_invariant_compact_open_neighborhood`: when the target map is open and
  the source map is quasi-compact, every point of the object scheme lies in an invariant
  quasi-compact open.

## Implementation notes

Invariance is stated on underlying points, so `IsInvariantOpen` is `IsInvariantSet` applied to
the open's carrier rather than a separate condition. The saturation is written as
`G.target.left.base '' (G.source.left.base ⁻¹' W)`; its invariance comes from transitivity and
symmetry of the equivalence relation that the groupoid's source and target maps induce on
points. The hypotheses are exactly what each conclusion needs: the source map need not be open,
and the target map need not be quasi-compact, since inverse images of opens are open and
continuous images of compact sets are compact.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

variable {S : Scheme.{u}}

/-- The saturation of any subset of the objects of a groupoid scheme is invariant. -/
theorem isInvariantSet_target_image_source_preimage (G : GroupoidScheme S)
    (W : Set G.objects.left) :
    IsInvariantSet G (G.target.left.base '' (G.source.left.base ⁻¹' W)) := by
  rintro r ⟨a, haW, has⟩
  have hE := AlgebraicGeometry.PreRelation.equivalence_sourceTargetRel
    (groupoidPreRelation G) (groupoidPreRelation_isPreEquivalenceRelation G)
  simp [groupoidPreRelation, PreRelation.target, PreRelation.source] at hE
  obtain ⟨b, hb₁, hb₂⟩ := hE.trans ⟨r, rfl, rfl⟩
    (by simpa [has] using (show Function.SourceTargetRel G.source.left.base
      G.target.left.base (G.target.left.base a) (G.source.left.base a) from
      ⟨a, rfl, rfl⟩))
  exact ⟨b, by simpa [hb₂] using haW, hb₁⟩

/-- The saturation of an open set is open when the target map is an open map. -/
theorem isOpen_target_image_source_preimage (G : GroupoidScheme S)
    (ht : IsOpenMap G.target.left.base) (W : G.objects.left.Opens) :
    IsOpen (G.target.left.base '' (G.source.left.base ⁻¹' (W : Set G.objects.left))) :=
  ht _ (Continuous.isOpen_preimage (by fun_prop) _ W.2)

/-- When the target map is open and the source map is quasi-compact, every point of the object
scheme of a groupoid scheme has an invariant quasi-compact open neighbourhood. -/
theorem exists_invariant_compact_open_neighborhood (G : GroupoidScheme S)
    (ht : IsOpenMap G.target.left.base) [QuasiCompact G.source.left]
    (x : G.objects.left) :
    ∃ V : G.objects.left.Opens,
      x ∈ (V : Set G.objects.left) ∧ IsInvariantOpen G V ∧
        IsCompact (V : Set G.objects.left) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, _⟩ :=
    G.objects.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine ⟨⟨_, isOpen_target_image_source_preimage G ht W⟩, ?_, ?_, ?_⟩
  · refine ⟨G.identity.left.base x, by simpa [← Scheme.Hom.comp_apply,
      identity_left_comp_source_left] using hxW, by simp [← Scheme.Hom.comp_apply,
      identity_left_comp_target_left]⟩
  · exact isInvariantSet_target_image_source_preimage G (W : Set G.objects.left)
  · exact (QuasiCompact.isCompact_preimage (f := G.source.left) _ W.2 hW.isCompact).image
      (by fun_prop)

end Stacks.Groupoids
