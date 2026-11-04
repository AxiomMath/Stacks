module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import StacksFrontier.CategoryTheory.KanExtension.Extend

/-! # Monoidal identities extend from compact generators

Let `P` be a property of objects of a monoidal category `C` cutting out a locally `w`-small full
subcategory of categorically compact objects (Stacks 0FWX) such that every object of `C` is a
`w`-filtered colimit of `P`-objects, and let `D` be a monoidal category in which tensoring on
either side commutes with `w`-filtered colimits. A natural transformation out of a functor
commuting with filtered colimits is determined by its components at `P`-objects
(`CategoryTheory.ObjectProperty.existsUnique_natTrans_of_preservesFilteredColimits`, the
uniqueness in Stacks 0FWY). Applied once in each variable, this shows that an identity between
two families of maps `G X ⊗ G' Y ⟶ L(X, Y)`, natural in `X` and in `Y`, holds as soon as it holds
for `P`-objects `X` and `Y`.

The main application: a natural transformation between lax monoidal functors commuting with
filtered colimits is monoidal as soon as it is monoidal on `P`-objects. This is the step "the
extension is unique as a tensor functor" in the proofs of Stacks 0GRJ and 0GRR.

## Main results

* `CategoryTheory.ObjectProperty.tensor_app_eq_of_preservesFilteredColimits`: two families of
  maps `G X ⊗ G' Y ⟶ L(X, Y)`, natural in both variables, agree when they agree on `P`-objects.
* `CategoryTheory.ObjectProperty.isMonoidal_of_preservesFilteredColimits`: a natural
  transformation `G₁ ⟶ G₂` of lax monoidal functors, `G₁` commuting with filtered colimits, is
  monoidal when it is compatible with the unit morphisms and with the tensorators at `P`-objects.

## References

* [Stacks Project, Tag 0FWY](https://stacks.math.columbia.edu/tag/0FWY)
* [Stacks Project, Tag 0GRJ](https://stacks.math.columbia.edu/tag/0GRJ)
* [Stacks Project, Tag 0GRR](https://stacks.math.columbia.edu/tag/0GRR)
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Functor.LaxMonoidal

universe w v v' u u'

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (P : ObjectProperty C)
  [LocallySmall.{w} P.FullSubcategory]
  (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)

variable [MonoidalCategory D]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]

include hP hgen in
/-- **Identities between maps out of a tensor product extend from compact generators.** Let
`G, G' : C ⥤ D` commute with `w`-filtered colimits, let `L : C ⥤ C ⥤ D`, and let
`a b : G X ⊗ G' Y ⟶ L(X, Y)` be two families of maps natural in `X` and in `Y`. If `a` and `b`
agree whenever `X` and `Y` are `P`-objects, they agree everywhere. -/
theorem tensor_app_eq_of_preservesFilteredColimits (G G' : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w, w} G] [PreservesFilteredColimitsOfSize.{w, w} G']
    (L : C ⥤ C ⥤ D) (a b : ∀ X Y : C, G.obj X ⊗ G'.obj Y ⟶ (L.obj X).obj Y)
    (ha₁ : ∀ {X X' : C} (f : X ⟶ X') (Y : C), G.map f ▷ G'.obj Y ≫ a X' Y = a X Y ≫ (L.map f).app Y)
    (ha₂ : ∀ (X : C) {Y Y' : C} (g : Y ⟶ Y'),
      G.obj X ◁ G'.map g ≫ a X Y' = a X Y ≫ (L.obj X).map g)
    (hb₁ : ∀ {X X' : C} (f : X ⟶ X') (Y : C), G.map f ▷ G'.obj Y ≫ b X' Y = b X Y ≫ (L.map f).app Y)
    (hb₂ : ∀ (X : C) {Y Y' : C} (g : Y ⟶ Y'),
      G.obj X ◁ G'.map g ≫ b X Y' = b X Y ≫ (L.obj X).map g)
    (h : ∀ X Y : P.FullSubcategory, a X.obj Y.obj = b X.obj Y.obj) (X Y : C) :
    a X Y = b X Y := by
  -- first in the second variable, for `X` a `P`-object
  have h₂ : ∀ (X : P.FullSubcategory) (Y : C), a X.obj Y = b X.obj Y := by
    intro X
    let α : G' ⋙ tensorLeft (G.obj X.obj) ⟶ L.obj X.obj :=
      { app := fun Y ↦ a X.obj Y
        naturality := fun _ _ g ↦ ha₂ X.obj g }
    let β : G' ⋙ tensorLeft (G.obj X.obj) ⟶ L.obj X.obj :=
      { app := fun Y ↦ b X.obj Y
        naturality := fun _ _ g ↦ hb₂ X.obj g }
    have hαβ : α = β := (existsUnique_natTrans_of_preservesFilteredColimits P hP hgen _ _
      (Functor.whiskerLeft P.ι α)).unique rfl (by ext Y; exact (h X Y).symm)
    exact NatTrans.congr_app hαβ
  -- then in the first variable
  let α : G ⋙ tensorRight (G'.obj Y) ⟶ L.flip.obj Y :=
    { app := fun X ↦ a X Y
      naturality := fun _ _ f ↦ ha₁ f Y }
  let β : G ⋙ tensorRight (G'.obj Y) ⟶ L.flip.obj Y :=
    { app := fun X ↦ b X Y
      naturality := fun _ _ f ↦ hb₁ f Y }
  have hαβ : α = β := (existsUnique_natTrans_of_preservesFilteredColimits P hP hgen _ _
    (Functor.whiskerLeft P.ι α)).unique rfl (by ext X; exact (h₂ X Y).symm)
  exact NatTrans.congr_app hαβ X

variable [MonoidalCategory C]

include hP hgen in
/-- **Monoidality of a natural transformation extends from compact generators.** Let
`G₁, G₂ : C ⥤ D` be lax monoidal functors commuting with `w`-filtered colimits and let
`τ : G₁ ⟶ G₂` be compatible with the unit morphisms. If `τ` is compatible with the tensorators
at all pairs of `P`-objects, then `τ` is a monoidal natural transformation. -/
theorem isMonoidal_of_preservesFilteredColimits {G₁ G₂ : C ⥤ D} [G₁.LaxMonoidal] [G₂.LaxMonoidal]
    [PreservesFilteredColimitsOfSize.{w, w} G₁] (τ : G₁ ⟶ G₂)
    (hε : ε G₁ ≫ τ.app (𝟙_ C) = ε G₂)
    (hμ : ∀ X Y : P.FullSubcategory,
      μ G₁ X.obj Y.obj ≫ τ.app (X.obj ⊗ Y.obj) = (τ.app X.obj ⊗ₘ τ.app Y.obj) ≫ μ G₂ X.obj Y.obj) :
    NatTrans.IsMonoidal τ where
  unit := hε
  tensor X Y := by
    refine tensor_app_eq_of_preservesFilteredColimits P hP hgen G₁ G₁
      (curriedTensor C ⋙ (Functor.whiskeringRight C C D).obj G₂)
      (fun X Y ↦ μ G₁ X Y ≫ τ.app (X ⊗ Y)) (fun X Y ↦ (τ.app X ⊗ₘ τ.app Y) ≫ μ G₂ X Y)
      ?_ ?_ ?_ ?_ hμ X Y
    · intro X X' f Y
      dsimp
      rw [μ_natural_left_assoc, τ.naturality, assoc]
    · intro X Y Y' g
      dsimp
      rw [μ_natural_right_assoc, τ.naturality, assoc]
    · intro X X' f Y
      dsimp
      have h : G₁.map f ▷ G₁.obj Y ≫ (τ.app X' ⊗ₘ τ.app Y) =
          (τ.app X ⊗ₘ τ.app Y) ≫ G₂.map f ▷ G₂.obj Y := by
        rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
          τ.naturality]
        simp
      simp only [assoc]
      rw [reassoc_of% h, μ_natural_left]
    · intro X Y Y' g
      dsimp
      have h : G₁.obj X ◁ G₁.map g ≫ (τ.app X ⊗ₘ τ.app Y') =
          (τ.app X ⊗ₘ τ.app Y) ≫ G₂.obj X ◁ G₂.map g := by
        rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
          τ.naturality]
        simp
      simp only [assoc]
      rw [reassoc_of% h, μ_natural_right]

end CategoryTheory.ObjectProperty
