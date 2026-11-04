module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Global sections along a functor preserving the terminal object

A *global section* of an object `X` of a category with a terminal object is a morphism
`⊤ ⟶ X`. A functor `F` preserving the terminal object carries it to the global section
`⊤ ≅ F ⊤ ⟶ F X` of `F X` (`CategoryTheory.Functor.globalSectionMap`). For the inverse image of
a morphism of topoi, which preserves finite limits, this is the image of a global section of a
sheaf in the inverse image sheaf, without reference to the unit of the adjunction.

Its point is that *any* comparison `F ⋙ G ⟶ H` of functors preserving the terminal object is
compatible with it (`CategoryTheory.Functor.globalSectionMap_globalSectionMap_comp_app`): the
only input is the naturality of the comparison, the rest is the uniqueness of maps into a
terminal object. For the composition law of inverse images of sheaves (Stacks 03G8) this says
that the image of a global section along a composite does not depend on the factorization.

## Main results

* `CategoryTheory.Functor.globalSectionMap`
* `CategoryTheory.Functor.globalSectionMap_comp`: compatibility with morphisms.
* `CategoryTheory.Functor.globalSectionMap_comp_app`: compatibility with natural transformations.
* `CategoryTheory.Functor.globalSectionMap_globalSectionMap_comp_app`: compatibility with any
  comparison `F ⋙ G ⟶ H`.
* `CategoryTheory.Adjunction.homEquiv_symm_comp_unit_app_globalSection`: the adjunct of a global
  section followed by the unit is its image along the left adjoint.
* `CategoryTheory.Adjunction.eq_globalSectionMap_of_comp_map_eq`: a global section of `F X` whose
  image under the right adjoint is the unit on a global section of `X` is its image.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [HasTerminal C] [HasTerminal D] [HasTerminal E]

/-- **The image of a global section along a functor preserving the terminal object**: for
`a : ⊤ ⟶ X`, the global section `⊤ ≅ F ⊤ ⟶ F X` of `F X`. -/
noncomputable def globalSectionMap (F : C ⥤ D) [IsIso (terminalComparison F)] {X : C}
    (a : ⊤_ C ⟶ X) : ⊤_ D ⟶ F.obj X :=
  CategoryTheory.inv (terminalComparison F) ≫ F.map a

/-- The image of global sections is compatible with morphisms. -/
theorem globalSectionMap_comp (F : C ⥤ D) [IsIso (terminalComparison F)] {X Y : C}
    (a : ⊤_ C ⟶ X) (φ : X ⟶ Y) :
    globalSectionMap F a ≫ F.map φ = globalSectionMap F (a ≫ φ) := by
  simp only [globalSectionMap, Functor.map_comp, Category.assoc]

/-- Any global section of `H ⊤` followed by `H.map a` is the image of `a`. -/
private theorem comp_map_eq_globalSectionMap (H : C ⥤ D) [IsIso (terminalComparison H)]
    (f : ⊤_ D ⟶ H.obj (⊤_ C)) {X : C} (a : ⊤_ C ⟶ X) : f ≫ H.map a = globalSectionMap H a := by
  rw [show f = CategoryTheory.inv (terminalComparison H) from
    (IsTerminal.ofIso terminalIsTerminal (asIso (terminalComparison H)).symm).hom_ext _ _]
  rfl

/-- The image of global sections is compatible with any natural transformation `G ⟶ H` of
functors preserving the terminal object. -/
theorem globalSectionMap_comp_app {G H : C ⥤ D} (e : G ⟶ H) [IsIso (terminalComparison G)]
    [IsIso (terminalComparison H)] {X : C} (a : ⊤_ C ⟶ X) :
    globalSectionMap G a ≫ e.app X = globalSectionMap H a := by
  rw [globalSectionMap, Category.assoc, e.naturality a, ← Category.assoc]
  exact comp_map_eq_globalSectionMap H _ a

/-- **The image of a global section along a composite does not depend on the factorization**:
for any comparison `e : F ⋙ G ⟶ H` of functors preserving the terminal object, taking the image
along `F` and then along `G`, followed by `e`, is taking the image along `H`. -/
theorem globalSectionMap_globalSectionMap_comp_app {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    (e : F ⋙ G ⟶ H) [IsIso (terminalComparison F)] [IsIso (terminalComparison G)]
    [IsIso (terminalComparison H)] {X : C} (a : ⊤_ C ⟶ X) :
    globalSectionMap G (globalSectionMap F a) ≫ e.app X = globalSectionMap H a := by
  have hn : G.map (F.map a) ≫ e.app X = e.app (⊤_ C) ≫ H.map a := e.naturality a
  simp only [globalSectionMap, Functor.map_comp, Category.assoc, hn]
  simpa only [globalSectionMap, Category.assoc] using comp_map_eq_globalSectionMap H
    (CategoryTheory.inv (terminalComparison G) ≫
      G.map (CategoryTheory.inv (terminalComparison F)) ≫ e.app _) a

/-- The same, for the inverse of a comparison `F ⋙ G ≅ H`. -/
theorem globalSectionMap_comp_inv_app {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    (e : F ⋙ G ≅ H) [IsIso (terminalComparison F)] [IsIso (terminalComparison G)]
    [IsIso (terminalComparison H)] {X : C} (a : ⊤_ C ⟶ X) :
    globalSectionMap H a ≫ e.inv.app X = globalSectionMap G (globalSectionMap F a) := by
  rw [← globalSectionMap_globalSectionMap_comp_app e.hom a, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [HasTerminal C] [HasTerminal D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [IsIso (terminalComparison F)]

/-- **The adjunct of a global section followed by the unit is its image along the left
adjoint**: for `x : ⊤ ⟶ X`, `⊤ ≅ F ⊤ ⟶ Y` adjunct to `x ≫ η_X : ⊤ ⟶ G F X` is
`CategoryTheory.Functor.globalSectionMap F x`. -/
theorem homEquiv_symm_comp_unit_app_globalSection {X : C} (x : ⊤_ C ⟶ X) :
    CategoryTheory.inv (terminalComparison F) ≫ (adj.homEquiv _ _).symm (x ≫ adj.unit.app X) =
      F.globalSectionMap x := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.left_triangle_components, Category.comp_id]
  rfl

/-- The adjunct of a global section followed by the image of a morphism under the right adjoint
is the adjunct followed by the morphism. -/
theorem homEquiv_symm_comp_map_globalSection {Y Y' : D} (m : ⊤_ C ⟶ G.obj Y) (α : Y ⟶ Y') :
    CategoryTheory.inv (terminalComparison F) ≫ (adj.homEquiv _ _).symm (m ≫ G.map α) =
      (CategoryTheory.inv (terminalComparison F) ≫ (adj.homEquiv _ _).symm m) ≫ α := by
  rw [Adjunction.homEquiv_naturality_right_symm, Category.assoc]

/-- **A global section of `F X` whose image under `G` is the unit on a global section is the
image of that section**: if `w : ⊤ ⟶ F X` satisfies `e ≫ G.map w = x ≫ η_X` for some
`e : ⊤ ⟶ G ⊤`, then `w` is `CategoryTheory.Functor.globalSectionMap F x`. -/
theorem eq_globalSectionMap_of_comp_map_eq {X : C} (x : ⊤_ C ⟶ X) (w : ⊤_ D ⟶ F.obj X)
    (e : ⊤_ C ⟶ G.obj (⊤_ D)) (h : e ≫ G.map w = x ≫ adj.unit.app X) :
    w = F.globalSectionMap x := by
  have he : (adj.homEquiv _ _).symm e = terminalComparison F :=
    (IsTerminal.ofIso terminalIsTerminal (Iso.refl _)).hom_ext _ _
  rw [← adj.homEquiv_symm_comp_unit_app_globalSection x, ← h,
    Adjunction.homEquiv_naturality_right_symm, he, IsIso.inv_hom_id_assoc]

end CategoryTheory.Adjunction

end
