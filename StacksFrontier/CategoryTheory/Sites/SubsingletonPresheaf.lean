module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Presheaves whose values are subsingletons

A presheaf of sets with at most one section over every object carries no gluing data: a family
of elements for a presieve is the bare assertion that each member of the presieve has a
section, compatibility is automatic, and an amalgamation is unique as soon as it exists. This
file records the resulting reformulations of the sheaf condition and of the comparison between
a cofiltered limit and the colimit of the values.

## Main results

* `CategoryTheory.Presieve.isSheafFor_iff_nonempty_of_subsingleton` and
  `CategoryTheory.Presheaf.isSheaf_iff_nonempty_of_subsingleton`: for such a presheaf the sheaf
  condition says exactly that a section exists over an object as soon as one exists over every
  member of a covering sieve.
* `CategoryTheory.nonempty_isColimit_mapCocone_op_iff_of_subsingleton`: the values at a
  cofiltered limit cone form a colimit cocone exactly when a section over the limit already
  comes from some stage.

## Implementation notes

The hypothesis is phrased as an instance `∀ X, Subsingleton (F.obj X)`; it holds, for example,
for a functor whose values are `PLift` or `ULift (PLift _)` of a proposition.

For the colimit statement the index category is only assumed cofiltered, and nothing is assumed
about the cone beyond its existence; both implications are read off the description of a
colimit in types as bijectivity of the canonical map out of
`CategoryTheory.Functor.ColimitType`. Injectivity of that map is automatic here, because a
cofiltered index makes `ColimitType` itself a subsingleton: two elements are represented at two
stages, and the two representatives have equal images at any common earlier stage.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

universe w v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- For a presheaf with at most one section over every object, the sheaf condition for a
presieve is the implication "a section over each member of the presieve yields a section over
its target". -/
theorem Presieve.isSheafFor_iff_nonempty_of_subsingleton (F : Cᵒᵖ ⥤ Type w)
    [∀ X : Cᵒᵖ, Subsingleton (F.obj X)] {X : C} (R : Presieve X) :
    Presieve.IsSheafFor F R ↔
      ((∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → Nonempty (F.obj (op Y))) → Nonempty (F.obj (op X))) := by
  refine ⟨fun h hne ↦ ?_, fun h x _ ↦ ?_⟩
  · obtain ⟨t, -⟩ := h (fun _ f hf ↦ (hne f hf).some) fun _ _ _ _ _ _ _ _ _ _ ↦
      Subsingleton.elim _ _
    exact ⟨t⟩
  · obtain ⟨t⟩ := h fun _ f hf ↦ ⟨x f hf⟩
    exact ⟨t, fun _ _ _ ↦ Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩

/-- For a presheaf with at most one section over every object, being a sheaf says exactly that a
section over each member of a covering sieve yields a section over its target. -/
theorem Presheaf.isSheaf_iff_nonempty_of_subsingleton (J : GrothendieckTopology C)
    (F : Cᵒᵖ ⥤ Type w) [∀ X : Cᵒᵖ, Subsingleton (F.obj X)] :
    Presheaf.IsSheaf J F ↔
      ∀ (X : C) (S : Sieve X), S ∈ J X →
        ((∀ ⦃Y : C⦄ (f : Y ⟶ X), S.arrows f → Nonempty (F.obj (op Y))) →
          Nonempty (F.obj (op X))) := by
  rw [isSheaf_iff_isSheaf_of_type]
  simp only [Presieve.IsSheaf, Presieve.isSheafFor_iff_nonempty_of_subsingleton]

/-- For a presheaf with at most one section over every object and a cone over a cofiltered
diagram, the induced cocone of values is a colimit cocone exactly when every section over the
cone point is pulled back from a section over some stage of the diagram. -/
theorem nonempty_isColimit_mapCocone_op_iff_of_subsingleton
    {I : Type u'} [Category.{v'} I] [IsCofiltered I] (F : Cᵒᵖ ⥤ Type w)
    [∀ X : Cᵒᵖ, Subsingleton (F.obj X)] (E : I ⥤ C) (c : Cone E) :
    Nonempty (IsColimit (F.mapCocone c.op)) ↔
      (Nonempty (F.obj (op c.pt)) → ∃ i, Nonempty (F.obj (op (E.obj i)))) := by
  rw [Types.isColimit_iff_coconeTypesIsColimit]
  constructor
  · intro hc hne
    obtain ⟨j, y, -⟩ :=
      (Functor.CoconeTypes.descColimitType_surjective_iff _).mp hc.bijective.2 hne.some
    exact ⟨j.unop, ⟨y⟩⟩
  · intro h
    have hsub : Subsingleton ((E.op ⋙ F).ColimitType) := by
      refine ⟨fun a b ↦ ?_⟩
      obtain ⟨j, x, rfl⟩ := (E.op ⋙ F).ιColimitType_jointly_surjective a
      obtain ⟨j', y, rfl⟩ := (E.op ⋙ F).ιColimitType_jointly_surjective b
      refine (E.op ⋙ F).ιColimitType_eq_of_map_eq_map x y (IsFiltered.leftToMax j j')
        (IsFiltered.rightToMax j j') ?_
      exact Subsingleton.elim (α := F.obj (E.op.obj (IsFiltered.max j j'))) _ _
    refine ⟨⟨fun a b _ ↦ hsub.allEq a b, ?_⟩⟩
    rw [Functor.CoconeTypes.descColimitType_surjective_iff]
    intro z
    obtain ⟨i, hi⟩ := h ⟨z⟩
    exact ⟨op i, hi.some, Subsingleton.elim (α := F.obj (op c.pt)) _ _⟩

end CategoryTheory

end
