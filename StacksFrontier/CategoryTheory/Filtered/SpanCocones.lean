module

public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.Filtered.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Categories with span cocones decompose into filtered pieces

A category `J` in which

* every span `y ← x → z` can be completed to a commutative square `y → w ← z`, and
* every pair of parallel morphisms `a, b : x ⟶ y` can be coequalized by some `c : y ⟶ z`

is a disjoint union of filtered categories: each of its connected components is filtered. The
decomposition of `J` into its connected components is `CategoryTheory.decomposedTo`.

## Main definitions

* `CategoryTheory.HasSpanCocone`: every span can be completed to a commutative square.
* `CategoryTheory.HasCoequalizingHom`: every pair of parallel morphisms can be coequalized.

## Main results

* `CategoryTheory.isFiltered_component_of_cocone_and_coequaliser`: under both hypotheses, every
  connected component is filtered.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe v u

/-- A category `J` **has span cocones** if every span `y ← x → z` can be completed to a
commutative square `y → w ← z`. -/
@[sga "4 VI 6.4"]
def HasSpanCocone (J : Type u) [Category.{v} J] : Prop :=
  ∀ ⦃x y z : J⦄ (f : x ⟶ y) (g : x ⟶ z), ∃ (w : J) (h : y ⟶ w) (k : z ⟶ w), f ≫ h = g ≫ k

/-- A category `J` **has coequalizing morphisms** if any two parallel morphisms
`a, b : x ⟶ y` become equal after composing with some `c : y ⟶ z`. -/
def HasCoequalizingHom (J : Type u) [Category.{v} J] : Prop :=
  ∀ ⦃x y : J⦄ (a b : x ⟶ y), ∃ (z : J) (c : y ⟶ z), a ≫ c = b ≫ c

variable {J : Type u} [Category.{v} J]

/-- A morphism of `J` places its source and target in the same connected component. -/
theorem ConnectedComponents.mk_eq_mk_of_hom {X Y : J} (f : X ⟶ Y) :
    ConnectedComponents.mk X = ConnectedComponents.mk Y :=
  _root_.Quotient.sound (Zigzag.of_hom f)

/-- In a category with span cocones, two objects joined by a zigzag admit morphisms to a common
object. -/
public lemma exists_cocone_of_zigzag (h1 : HasSpanCocone J) {X Y : J} (hxy : Zigzag X Y) :
    ∃ (Z : J) (_ : X ⟶ Z) (_ : Y ⟶ Z), True := by
  induction hxy with
  | refl => exact ⟨X, 𝟙 X, 𝟙 X, trivial⟩
  | tail _ step ih =>
    obtain ⟨Z₁, fX, fY, _⟩ := ih
    rcases step with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · obtain ⟨Z, c, d, _⟩ := h1 fY f
      exact ⟨Z, fX ≫ c, d, trivial⟩
    · exact ⟨Z₁, fX, f ≫ fY, trivial⟩

/-- A category with span cocones and coequalizing morphisms is a disjoint union of filtered
categories: every connected component of it is filtered. -/
@[stacks 002X, sga "4 I 2.7.1" "pseudo-filtered part"]
theorem isFiltered_component_of_cocone_and_coequaliser
    (h1 : HasSpanCocone J) (h2 : HasCoequalizingHom J) (j : ConnectedComponents J) :
    IsFiltered j.Component := by
  have : IsFilteredOrEmpty j.Component := by
    refine ⟨fun X Y ↦ ?_, fun X Y f g ↦ ?_⟩
    · obtain ⟨Z, a, b, _⟩ :=
        exists_cocone_of_zigzag h1 (Quotient.exact (X.property.trans Y.property.symm))
      exact ⟨⟨Z, (ConnectedComponents.mk_eq_mk_of_hom a).symm.trans X.property⟩, ⟨a⟩, ⟨b⟩,
        trivial⟩
    · obtain ⟨Z, c, hfg⟩ := h2 f.hom g.hom
      exact ⟨⟨Z, (ConnectedComponents.mk_eq_mk_of_hom c).symm.trans Y.property⟩, ⟨c⟩,
        InducedCategory.Hom.ext hfg⟩
  exact ⟨⟩

end CategoryTheory
