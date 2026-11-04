module

public import StacksFrontier.CategoryTheory.Representable.SolutionSet

/-!
# Reading a diagram of objects off a diagram of representable presheaves

A diagram `F : J ⥤ (Cᵒᵖ ⥤ Type u)` all of whose values are representable presheaves is, up to
isomorphism, the composite of a diagram of objects of `C` with the Yoneda embedding: choosing a
representing object of each `F.obj j`, the Yoneda lemma transports each `F.map f` to a morphism
between the chosen objects, and functoriality is inherited from `F` through the faithfulness of
`yoneda`.

## Main definitions

* `CategoryTheory.representedDiagram`: the diagram of chosen representing objects.
* `CategoryTheory.representedDiagramIso`: the isomorphism
  `representedDiagram F hF ⋙ yoneda ≅ F`.

## Implementation notes

The index category `J` has independent object and morphism universes, so that the construction
applies to diagrams of arbitrary shape.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe u v w w'

section RepresentedDiagram

variable {C : Type v} [Category.{u} C] {J : Type w} [Category.{w'} J]

/-- **A diagram of representable presheaves is represented by a diagram of objects.** -/
noncomputable def representedDiagram (F : J ⥤ (Cᵒᵖ ⥤ Type u))
    (hF : ∀ j, (F.obj j).IsRepresentable) : J ⥤ C where
  obj j := have := hF j; (F.obj j).reprX
  map {i j} f :=
    have := hF i
    have := hF j
    yoneda.preimage ((F.obj i).reprW.hom ≫ F.map f ≫ (F.obj j).reprW.inv)
  map_id i := by
    have := hF i
    apply yoneda.map_injective
    simp
  map_comp {i j k} f g := by
    have := hF i
    have := hF j
    have := hF k
    apply yoneda.map_injective
    simp [Category.assoc]

/-- The diagram of objects read off a diagram of representable presheaves does represent it. -/
noncomputable def representedDiagramIso (F : J ⥤ (Cᵒᵖ ⥤ Type u))
    (hF : ∀ j, (F.obj j).IsRepresentable) : representedDiagram F hF ⋙ yoneda ≅ F :=
  NatIso.ofComponents (fun j => have := hF j; (F.obj j).reprW) (by
    intro i j f
    have := hF i
    have := hF j
    apply yoneda.map_injective
    simp [representedDiagram, Category.assoc])

end RepresentedDiagram

end CategoryTheory
