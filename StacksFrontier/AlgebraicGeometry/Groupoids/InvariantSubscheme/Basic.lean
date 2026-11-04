module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic

/-!
# Invariant subsets and invariant opens of a groupoid scheme

A subset of the objects of a groupoid scheme is *invariant* when every arrow whose source lies
in it has its target there too, and an open is invariant when its underlying set is.  The
*saturation* of a subset is the image under the target map of its inverse image under the source
map; it is always invariant, because the relation on points cut out by the source and target
maps of a groupoid scheme is an equivalence relation.  If the target map is open, the saturation
of an open is open, so saturating an affine open neighbourhood of a point produces an invariant
open neighbourhood; it is quasi-compact as soon as the source map is.

## Main definitions

* `Stacks.Groupoids.IsInvariantSet`: set-theoretic invariance under the arrows of a groupoid
  scheme.
* `Stacks.Groupoids.IsInvariantOpen`: invariance of an open subscheme of the object scheme.

## Main results

* `AlgebraicGeometry.GroupoidScheme.isInvariantSet_target_image_source_preimage`: the
  saturation of any subset is invariant.
* `AlgebraicGeometry.GroupoidScheme.isOpen_target_image_source_preimage`: the saturation of an
  open is open when the target map is open.
* `AlgebraicGeometry.GroupoidScheme.exists_invariant_compact_open_neighborhood`: with the target
  map open and the source map quasi-compact, every point of the object scheme has an invariant
  quasi-compact open neighbourhood.

## Implementation notes

Invariance is written pointwise: membership of the source of an arrow implies membership of its
target.  The scheme-theoretic notion for a closed subscheme is
`Stacks.Groupoids.IsInvariantClosedSubscheme`, an equality of scheme-theoretic inverse images.

The source map need not be open and the target map need not be quasi-compact for the covering
statement: inverse images of opens are open, and continuous images of compact sets are compact.

## References

* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
* [Stacks Project, Tag 03LO](https://stacks.math.columbia.edu/tag/03LO)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Groupoids

/-- **Stacks Project, Tag 03BC, part (1).**  A subset of the objects of a groupoid scheme is
invariant if every arrow starting in it also ends in it. -/
@[stacks 03BC "part (1): set-theoretic invariance"]
abbrev IsInvariantSet {S : AlgebraicGeometry.Scheme.{u}} (G : GroupoidScheme S)
    (W : Set G.objects.left) : Prop :=
  ∀ r : G.arrows.left, G.source.left.base r ∈ W → G.target.left.base r ∈ W

/-- **Stacks Project, Tag 03BC, part (2).**  An open subscheme of the objects of a groupoid
scheme is invariant if its underlying set is. -/
@[stacks 03BC "part (2): invariant opens"]
abbrev IsInvariantOpen {S : AlgebraicGeometry.Scheme.{u}} (G : GroupoidScheme S)
    (W : G.objects.left.Opens) : Prop :=
  IsInvariantSet G W.1

end Stacks.Groupoids

namespace AlgebraicGeometry.GroupoidScheme

open Stacks.Groupoids

/-- Every point of a scheme has a quasi-compact open neighbourhood, namely an affine one. -/
private theorem exists_compact_affineOpen_mem (X : Scheme.{u}) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsCompact (U : Set X) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨U, hxU, hU.isCompact⟩

/-- **Stacks Project, Tag 03LO (1).** The saturation of any subset by the arrows of a groupoid
scheme is invariant. -/
@[stacks 03LO "part (1): set-theoretic invariance"]
theorem isInvariantSet_target_image_source_preimage {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (W : Set G.objects.left) :
    IsInvariantSet G (G.target.left.base '' (G.source.left.base ⁻¹' W)) := by
  rintro r ⟨a, haW, has⟩
  have hE : Equivalence
      (Function.SourceTargetRel G.source.left.base G.target.left.base) := by
    simpa [groupoidPreRelation, Stacks.Groupoids.PreRelation.target,
      Stacks.Groupoids.PreRelation.source] using
      PreRelation.equivalence_sourceTargetRel (groupoidPreRelation G)
        (groupoidPreRelation_isPreEquivalenceRelation G)
  have hR : ∀ r, Function.SourceTargetRel G.source.left.base G.target.left.base
      (G.target.left.base r) (G.source.left.base r) := fun r => ⟨r, rfl, rfl⟩
  obtain ⟨b, hb₁, hb₂⟩ := hE.trans (hR r) (by simpa [has] using hR a)
  exact ⟨b, by simpa [hb₂] using haW, hb₁⟩

/-- **Stacks Project, Tag 03LO (2).** The saturation of an open set is open when the target map
is an open map. -/
@[stacks 03LO "part (2): invariant open saturation"]
theorem isOpen_target_image_source_preimage {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S)
    (ht : IsOpenMap G.target.left.base)
    (W : G.objects.left.Opens) :
    IsOpen (G.target.left.base '' (G.source.left.base ⁻¹' (W : Set G.objects.left))) :=
  ht _ (Continuous.isOpen_preimage (by fun_prop) _ W.2)

/-- **Stacks Project, Tag 03LO (3).** If the target map is open and the source map is
quasi-compact, every point of the object scheme has an invariant quasi-compact open
neighbourhood. -/
@[stacks 03LO "part (3): invariant quasi-compact open covering"]
theorem exists_invariant_compact_open_neighborhood {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S)
    (ht : IsOpenMap G.target.left.base)
    [QuasiCompact G.source.left]
    (x : G.objects.left) :
    ∃ V : G.objects.left.Opens,
      x ∈ (V : Set G.objects.left) ∧
        IsInvariantOpen G V ∧ IsCompact (V : Set G.objects.left) := by
  obtain ⟨W, hxW, hW⟩ := exists_compact_affineOpen_mem G.objects.left x
  refine ⟨⟨_, isOpen_target_image_source_preimage G ht W⟩, ?_, ?_, ?_⟩
  · have h : ∀ f : G.arrows.left ⟶ G.objects.left, G.identity.left ≫ f = 𝟙 _ →
        f.base (G.identity.left.base x) = x := fun f hf => by
      rw [← Scheme.Hom.comp_apply, hf]; rfl
    exact ⟨G.identity.left.base x, by simpa [h _ (identity_left_comp_source_left G)] using hxW,
      h _ (identity_left_comp_target_left G)⟩
  · exact isInvariantSet_target_image_source_preimage G (W : Set G.objects.left)
  · exact (QuasiCompact.isCompact_preimage (f := G.source.left) _ W.2 hW).image
      (by fun_prop)

end AlgebraicGeometry.GroupoidScheme

end
